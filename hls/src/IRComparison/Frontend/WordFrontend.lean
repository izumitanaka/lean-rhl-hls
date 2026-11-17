import IRComparison.Core.WordLoopFacts
import IRComparison.Frontend.LeanEntryEnvironment
import IRComparison.Frontend.LeanCertificate
import IRComparison.Frontend.DependencyClosure
import IRComparison.Frontend.LeanTypingCompleteness

/-! Word frontend uses the same formal type-and-definition environment as the
Int frontend. Each syntax constructor applies an existing general theorem;
the result retains a formal typing derivation against the exact source term. -/
namespace IRComparison.WordFrontend
open Lean4Lean LeanTyped LeanTypeInference

def word : Lean.Expr := .const ``HybridWord.Word []
def state : Lean.Expr := .const ``HybridWord.State []
def app (n : Lean.Name) (args : List Lean.Expr) : Lean.Expr :=
  args.foldl Lean.Expr.app (.const n [])
def option (ty : Lean.Expr) := Lean.Expr.app (.const ``Option [.zero]) ty
def someExpr (ty v : Lean.Expr) := Lean.mkApp2 (.const ``Option.some [.zero]) ty v
def eq (ty a b : Lean.Expr) := Lean.mkApp3 (.const ``Eq [.succ .zero]) ty a b
def nilWords := Lean.Expr.app (.const ``List.nil [.zero]) word
def consWord (v vs : Lean.Expr) := Lean.mkApp3 (.const ``List.cons [.zero]) word v vs

/-- Compare in the existing proof-side representation. Unlike Expr.eqv this
is a defined Lean computation, so syntax-completeness proofs can unfold it.
Every accepted term still receives the ordinary typed source certificate. -/
def sameTerm (a b : Lean.Expr) : Bool :=
  match translate a, translate b with
  | some a, some b => decide (a.val = b.val)
  | _, _ => false

def isClosed (e : Lean.Expr) : Bool := LeanScalar.wellScoped 0 e

theorem app_represents (head : Represents f fc)
    (arguments : List.Forall₂ Represents args cores) :
    Represents (args.foldl Lean.Expr.app f) (applications fc cores) := by
  induction arguments generalizing f fc with
  | nil => exact head
  | cons argument rest ih => exact ih (.app head argument)

/-- A quoted target term together with its lexical scope proof. This wraps
Lean.Expr; it introduces neither a source AST nor an execution semantics. -/
structure ClosedTerm where
  val : Lean.Expr
  closed : isClosed val = true
  represented : {core // Represents val core}

instance : Coe ClosedTerm Lean.Expr := ⟨ClosedTerm.val⟩

private theorem foldApp_closed (args : List Lean.Expr) (head : Lean.Expr)
    (hh : isClosed head = true) (ha : ∀ a ∈ args, isClosed a = true) :
    isClosed (args.foldl Lean.Expr.app head) = true := by
  induction args generalizing head with
  | nil => exact hh
  | cons a args ih =>
    apply ih
    · change (isClosed head && isClosed a) = true
      simp only [hh,ha a (by simp),Bool.and_self]
    · intro b hb; exact ha b (by simp [hb])

def ClosedTerm.const (name : Lean.Name) : ClosedTerm :=
  ⟨.const name [],rfl,⟨.const name [],.constant rfl⟩⟩
def ClosedTerm.app (name : Lean.Name) (args : List ClosedTerm) : ClosedTerm :=
  ⟨WordFrontend.app name (args.map ClosedTerm.val),foldApp_closed _ _ rfl (by
    intro a ha
    obtain ⟨value,_,rfl⟩ := List.mem_map.mp ha
    exact value.closed),
   ⟨applications (.const name []) (args.map (fun a => a.represented.val)),
     app_represents (.constant rfl) (by
       induction args with
       | nil => exact .nil
       | cons a args ih => exact .cons a.represented.property ih)⟩⟩

/-- A binding position follows the same successor structure as localSucc's
proof. Unlike arbitrary data literals its magnitude is bounded by the source
binding count, so this representation is linear in the input syntax size. -/
def ClosedTerm.bindingIndex : Nat → ClosedTerm
  | 0 => .const ``Nat.zero
  | n+1 => .app ``Nat.succ [bindingIndex n]

def closedTerm (e : Lean.Expr) : Option ClosedTerm := do
  if closed : isClosed e = true then
    let represented ← translate e
    return ⟨e,closed,represented⟩
  else none

structure Inputs where
  i : Lean.Expr
  x : Lean.Expr
  y : Lean.Expr
  s : Lean.Expr
  locals : List Lean.Expr := []

def Inputs.list (p : Inputs) := p.locals.foldr consWord nilWords
def Inputs.args (p : Inputs) := [p.i,p.x,p.y,p.s,p.list]
def Inputs.lift (p : Inputs) : Inputs :=
  ⟨LeanBindings.rename Nat.succ p.i,LeanBindings.rename Nat.succ p.x,LeanBindings.rename Nat.succ p.y,
    LeanBindings.rename Nat.succ p.s,p.locals.map (LeanBindings.rename Nat.succ)⟩

def evalExpr (p : Inputs) (code : Lean.Expr) := app ``HybridWord.Expr.eval (p.args ++ [code])
def evalCmd (p : Inputs) (code : Lean.Expr) :=
  app ``HybridWord.Cmd.eval [p.i,p.x,p.y,code,p.s,p.list]

structure Artifact (env : VEnv) (ctx : List VExpr) (expected : Lean.Expr) where
  code : Lean.Expr
  proof : Lean.Expr
  core : {v // Represents expected v}
  proofCore : {v // Represents proof v}
  correct : env.HasType 0 ctx proofCore.val core.val

/-- A child certificate may be reused only at its exact term and binder
context. The stored typing proof is transported along these checked equalities. -/
def Artifact.known (a : Artifact env ctx expected) : KnownTypes env 0 := fun context term =>
  if hc : context = ctx then
    if ht : term = a.proofCore.val then
      some ⟨a.core.val,by cases hc; cases ht; exact a.correct⟩
    else none
  else none

/-- Reusing a child derivation always succeeds at its own expected type,
irrespective of the optional conversion procedure or source nesting depth. -/
theorem Artifact.check_known (a : Artifact env ctx expected)
    (conv : Conversion env) (exposure : Exposure env) :
    ∃ checked, checkWith env conv 0 ctx a.proofCore.val a.core.val exposure a.known = some checked := by
  rw [checkWith,inferWith.eq_def]
  simp only [Artifact.known,dif_pos rfl,dite_true,bind,Option.bind]
  exact ⟨_,rfl⟩

/-- Only the types of the composed facts are checked here. No program
equivalence solver, execution test, or optimizer certificate is substituted. -/
def finish (env : VEnv) (conv : Conversion env) (exposure : Exposure env)
    (ctx : List VExpr) (expected code proof : Lean.Expr)
    (known : KnownTypes env 0 := noKnownTypes env 0) : Option (Artifact env ctx expected) := do
  let core ← translate expected
  let proofCore ← translate proof
  let inferred ← inferWith env conv 0 ctx proofCore.val exposure known
  if same : inferred.val = core.val then
    return ⟨code,proof,core,proofCore,same ▸ inferred.property⟩
  else
    let cast ← conv 0 ctx inferred.val core.val
    -- Retain the expected type in the proof term itself, so a later cached
    -- child has that exact inferred type even after a Word/BV32 conversion.
    let transported := Lean.Expr.app (.lam `certificate expected (.bvar 0) .default) proof
    let transportedCore := VExpr.app (.lam core.val (.bvar 0)) proofCore.val
    have typed : env.HasType 0 ctx transportedCore core.val := by
      have domain := cast.property.symm.trans cast.property
      have identity : env.HasType 0 ctx (.lam core.val (.bvar 0)) (.forallE core.val core.val.lift) :=
        .lam domain (.bvar .zero)
      simpa only [transportedCore,VExpr.inst_lift] using
        (VEnv.HasType.app identity (.defeq cast.property inferred.property))
    return ⟨code,transported,core,
      ⟨transportedCore,.app (.lam core.property .bvar) proofCore.property⟩,typed⟩

/-- Retain a child's already constructed typing derivation when removing one
administrative let/beta step. Re-inferring the raw proof would forget previous
casts and force conversion to normalize the entire enclosing chain again. -/
def Artifact.retarget (a : Artifact env ctx previous) (conv : Conversion env)
    (expected : Lean.Expr) : Option (Artifact env ctx expected) := do
  let core ← translate expected
  if same : a.core.val = core.val then
    return ⟨a.code,a.proof,core,a.proofCore,same ▸ a.correct⟩
  else
    let cast ← conv 0 ctx a.core.val core.val
    -- Make the transported type explicit in the term. Reusing the old term
    -- at two convertible but syntactically distinct types would invalidate
    -- exact-type cache invariants during the source-syntax induction.
    let proof := Lean.Expr.app (.lam `certificate expected (.bvar 0) .default) a.proof
    let proofCore := VExpr.app (.lam core.val (.bvar 0)) a.proofCore.val
    have typed : env.HasType 0 ctx proofCore core.val := by
      have domain := cast.property.symm.trans cast.property
      have identity : env.HasType 0 ctx (.lam core.val (.bvar 0)) (.forallE core.val core.val.lift) :=
        .lam domain (.bvar .zero)
      simpa only [proofCore,VExpr.inst_lift] using
        (VEnv.HasType.app identity (.defeq cast.property a.correct))
    return ⟨a.code,proof,core,
      ⟨proofCore,.app (.lam core.property .bvar) a.proofCore.property⟩,typed⟩

/-- The certificate constructor succeeds for structurally represented terms
with a direct typing derivation. This is a library-side lemma; callers of HLS
are not asked to supply a successful checker or an equivalence certificate. -/
theorem finish_complete
    (expectedRep : Represents expected expectedCore)
    (proofRep : Represents proof proofCore)
    (typed : DirectTyping env 0 ctx proofCore expectedCore)
    (conv : Conversion env) (exposure : Exposure env) (code : Lean.Expr) :
    ∃ result, finish env conv exposure ctx expected code proof = some result := by
  obtain ⟨⟨ec,he⟩,translatedExpected,sameExpected⟩ := expectedRep.translate_complete
  obtain ⟨⟨pc,hp⟩,translatedProof,sameProof⟩ := proofRep.translate_complete
  dsimp only at sameExpected sameProof
  subst ec; subst pc
  obtain ⟨⟨_,inferred⟩,accepted,same⟩ := typed.infer_complete conv exposure
  dsimp only at same
  subst expectedCore
  simp only [finish,translatedExpected,translatedProof,bind,Option.bind,accepted,dif_pos rfl]
  exact ⟨_,rfl⟩

/-- Fixed signature interface of every supported source form. List source
heads explicitly as well as certificate facts: loading a simple program must
not rely on that program incidentally mentioning a library head. -/
def declarations : List Lean.Name :=
  [``Bool, ``Bool.true, ``Decidable, ``DecidableEq, ``bne, ``instBEqOfDecidableEq,
   ``instDecidableEqBitVec, ``instDecidableEqBool,
   ``WordLoopFacts.lift, ``WordLoopFacts.someYield, ``WordLoopFacts.letBinding, ``WordLoopFacts.bindState,
   ``WordLoopFacts.bindWord, ``WordLoopFacts.bindUnit, ``WordLoopFacts.branch,
   ``WordLoopFacts.compose, ``WordLoopFacts.forIn, ``WordLoopFacts.forStatic,
   ``WordLoopFacts.letValue, ``WordLoopFacts.letStateAlias, ``WordLoopFacts.letState,
   ``WordLoopFacts.bindValue, ``WordLoopFacts.sequence, ``WordLoopFacts.branchCmd,
   ``WordLoopFacts.unitSequence, ``WordFrontendFacts.unitSequence,
   ``HybridWord.range, ``HybridWord.rangeCount, ``HybridWord.State.copy,
   ``WordFrontendFacts.copy, ``HybridWord.Cmd.copy,
   ``WordFrontendFacts.literal, ``WordFrontendFacts.index, ``WordFrontendFacts.left,
   ``WordFrontendFacts.right, ``WordFrontendFacts.localZero, ``WordFrontendFacts.localSucc,
   ``WordFrontendFacts.register, ``WordFrontendFacts.add, ``WordFrontendFacts.sub,
   ``WordFrontendFacts.mul, ``WordFrontendFacts.div, ``WordFrontendFacts.read, ``WordFrontendFacts.readNat,
   ``WordFrontendFacts.skip, ``WordFrontendFacts.assign, ``WordFrontendFacts.skipPure, ``WordFrontendFacts.assignPure, ``WordFrontendFacts.store,
   ``WordFrontendFacts.bindValue, ``WordFrontendFacts.sequence,
   ``WordFrontendFacts.letValue, ``WordFrontendFacts.letStateAlias, ``WordFrontendFacts.letState, ``WordFrontendFacts.branch,
   ``WordFrontendFacts.select, ``WordFrontendFacts.forRange, ``WordFrontendFacts.neg,
   ``HybridWord.Expr.neg,
   ``HybridWord.Expr, ``HybridWord.Expr.eval, ``HybridWord.Cmd, ``HybridWord.Cmd.eval,
   ``HybridWord.Expr.lit, ``HybridWord.Expr.index, ``HybridWord.Expr.left, ``HybridWord.Expr.right,
   ``HybridWord.Expr.local, ``HybridWord.Expr.reg, ``HybridWord.Expr.add, ``HybridWord.Expr.sub,
   ``HybridWord.Expr.mul, ``HybridWord.Expr.div, ``HybridWord.Expr.read, ``HybridWord.Expr.readNat, ``HybridWord.Expr.select,
   ``HybridWord.Cmd.skip, ``HybridWord.Cmd.assign, ``HybridWord.Cmd.store, ``HybridWord.Cmd.letValue,
   ``HybridWord.Cmd.seq, ``HybridWord.Cmd.branch, ``HybridWord.Cmd.repeat, ``HybridWord.Cmd.forRange,
   ``HybridWord.Cmd.forStatic,
   ``Int, ``instOfNat, ``Int.instNegInt, ``Int.instAdd, ``Int.instSub, ``Int.instMul, ``Int.instDiv,
   ``Nat.zero, ``Nat.succ, ``Nat.mul, ``Nat, ``BitVec, ``List, ``Option,
   ``HybridWord.Word, ``HybridWord.State, ``List.nil, ``List.cons, ``Eq, ``Option.some,
   ``Neg, ``BitVec.instNeg, ``Neg.neg, ``OfNat, ``BitVec.instOfNat, ``OfNat.ofNat,
   ``HAdd, ``HSub, ``HMul, ``HDiv,
   ``instOfNatNat, ``Add, ``Sub, ``Mul, ``Div,
   ``BitVec.instAdd, ``BitVec.instSub, ``BitVec.instMul, ``BitVec.instDiv,
   ``instHAdd, ``instHSub, ``instHMul, ``instHDiv,
   ``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul, ``HDiv.hDiv, ``ite,
   ``HybridWord.State.regs, ``Pure.pure, ``Alternative.toApplicative, ``Applicative.toPure,
   ``instAlternativeOption, ``HybridWord.State.set, ``HybridWord.State.write,
   ``Bind.bind, ``Monad.toBind, ``instMonadOption,
   ``Array, ``Array.size, ``LT.lt, ``instLTNat, ``GetElem?, ``GetElem?.getElem?,
   ``Array.instGetElem?NatLtSize, ``HybridWord.State.arrays, ``BitVec.toNat,
   ``PUnit, ``PUnit.unit, ``ForInStep, ``ForInStep.yield, ``ForIn.forIn,
   ``instForInOfForIn', ``inferInstance, ``List.instMembership,
   ``List.instForIn'InferInstanceMembershipOfMonad, ``Membership,
   ``BitVec.ofNat, ``List.range, ``List.foldlM]

/-- All declarations in the actual native environment form a finite graph.
Traversal no longer rejects an otherwise valid closure after 8192 edges. -/
def declarationNames (native : Lean.Environment) : List Lean.Name :=
  native.constants.toList.map Prod.fst

def typeDependencies (native : Lean.Environment) (name : Lean.Name) : Option (List Lean.Name) := do
  let info ← native.find? name
  return LeanEntryEnvironment.constants info.type

def dependencies (native : Lean.Environment) (todo seen : List Lean.Name) : Option (List Lean.Name) :=
  DependencyClosure.walk (typeDependencies native) (declarationNames native).length todo seen

theorem dependencies_complete (native : Lean.Environment) (todo seen : List Lean.Name)
    (pending : ∀ n ∈ todo, n ∈ seen ∨ n ∈ declarationNames native)
    (available : ∀ n ∈ declarationNames native, ∃ ds, typeDependencies native n = some ds ∧
      ∀ d ∈ ds, d ∈ seen ∨ d ∈ declarationNames native) :
    ∃ names, dependencies native todo seen = some names :=
  DependencyClosure.complete _ _ _ _ _ (Nat.le_refl _) pending available

def libraryRoots (name : Lean.Name) (value : Lean.Expr) : List Lean.Name :=
  (name :: LeanEntryEnvironment.constants value ++ declarations ++
    [``outParam,``optParam,``DecidableEq]).eraseDups

def load (native : Lean.Environment) (name : Lean.Name) : Option (LeanEntryEnvironment.Loaded native name) := do
  let source ← LeanTypeReduction.load native name
  let names := libraryRoots name source.declaration.value
  let names ← dependencies native names []
  let base ← match h : LeanLibrary.installTypes native VEnv.empty names with
    | none => none
    | some env => some (⟨env,LeanEnvironmentProvenance.install_types names h⟩ :
        {env // LeanEnvironmentProvenance.Faithful native env})
  let identity ← LeanTypeAliases.load native ``outParam
  let optional ← LeanTypeReduction.load native ``optParam
  let decEq ← LeanTypeReduction.load native ``DecidableEq
  let wd ← LeanTypeReduction.load native ``HybridWord.Word
  let model := source.install (wd.install (decEq.install (optional.install (identity.install base.val))))
  let baseConv := LeanUniverseConversion.orElse
    (identity.conversion (env:=model) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      (LeanUniverseConversion.conversion model)) (LeanUniverseConversion.conversion model)
  let rules : List (LeanTypeReduction.Rule model) :=
    [⟨native,name,source,Or.inl rfl⟩,
     ⟨native,``HybridWord.Word,wd,Or.inr (Or.inl rfl)⟩,
     ⟨native,``DecidableEq,decEq,Or.inr (Or.inr (Or.inl rfl))⟩,
     ⟨native,``optParam,optional,Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩]
  let basic := LeanTypeReduction.conversion rules baseConv
  let expose : Exposure model := fun U ctx e => LeanTypeReduction.expose rules basic U ctx e
  let conv := LeanStructuralConversion.conversion model basic expose
  let exposure : Exposure model := fun U ctx e => LeanTypeReduction.expose rules conv U ctx e
  have faithful := LeanEnvironmentProvenance.install_definition
    (LeanEnvironmentProvenance.install_definition
      (LeanEnvironmentProvenance.install_definition
        (LeanEnvironmentProvenance.install_definition
          (LeanEnvironmentProvenance.install_alias base.property identity) optional) decEq) wd) source
  return ⟨model,faithful,conv,exposure,source,Or.inl rfl⟩

def compatible (env : VEnv) (conv : Conversion env) (ctx : List VExpr) (actual expected : Lean.Expr) : Bool :=
  if sameTerm actual expected then true else
    ((do
      let a ← translate actual
      let b ← translate expected
      let _ ← conv 0 ctx a.val b.val
      return ()) : Option Unit).isSome

def scalarExpected (p : Inputs) (code source : Lean.Expr) :=
  eq (option word) (evalExpr p code) (someExpr word source)
def readExpected (p : Inputs) (code source : Lean.Expr) :=
  eq (option word) (evalExpr p code) source
def bodyExpected (p : Inputs) (code source : Lean.Expr) :=
  eq (option state) (evalCmd p code) source

structure Piece (env : VEnv) (ctx : List VExpr) (p : Inputs) (source : Lean.Expr)
    (spec : Inputs → Lean.Expr → Lean.Expr → Lean.Expr) where
  code : Lean.Expr
  checked : Artifact env ctx (spec p code source)
  closed : isClosed code = true
  represented : {core // Represents code core}

def Piece.closedTerm (piece : Piece env ctx p source spec) : ClosedTerm :=
  ⟨piece.code,piece.closed,piece.represented⟩

def localFact (p : Inputs) : Nat → List Lean.Expr → Option Lean.Expr
  | _,[] => none
  | 0,v::vs => some (app ``WordFrontendFacts.localZero [p.i,p.x,p.y,p.s,v,vs.foldr consWord nilWords])
  | n+1,v::vs => do
    let proof ← localFact p n vs
    let w ← vs[n]?
    return app ``WordFrontendFacts.localSucc
      [(ClosedTerm.bindingIndex n).val,p.i,p.x,p.y,p.s,v,w,vs.foldr consWord nilWords,proof]

def nonzeroValue (condition : Lean.Expr) : Option Lean.Expr := do
  if condition.getAppFn.constName? != some ``Eq then none else do
    let [_ty,test,_truth] := condition.getAppArgs.toList | none
    if test.getAppFn.constName? != some ``bne then none else do
      let [_ty,_instance,v,z] := test.getAppArgs.toList | none
      if z.getAppFn.constName? != some ``OfNat.ofNat then none else do
        let [_ty,.lit (.natVal 0),_instance] := z.getAppArgs.toList | none
        return v

def leadingLet : Lean.Expr → Option Lean.Expr
  | .letE _ _ value next _ => some (LeanBindings.instantiate value next)
  | e => do
    -- Lean's do elaborator shares the continuation after an if with a local
    -- lambda. Reduce its application; the ordinary formal conversion checker
    -- still checks the resulting proof against the original source term.
    let .lam _ _ next _ := e.getAppFn | none
    let first :: rest := e.getAppArgs.toList | none
    return Lean.mkAppN (LeanBindings.instantiate first next) rest.toArray

def scalarStep (env : VEnv) (conv : Conversion env) (exposure : Exposure env)
    (ctx : List VExpr) (p : Inputs)
    (rec : (source : Lean.Expr) → Option (Piece env ctx p source scalarExpected))
    (source : Lean.Expr) : Option (Piece env ctx p source scalarExpected) := do
  let finishScalar (code : ClosedTerm) (proof : Lean.Expr) (known : KnownTypes env 0 := noKnownTypes env 0) := do
    let h ← finish env conv exposure ctx (scalarExpected p code source) code proof known
    return (⟨code.val,h,code.closed,code.represented⟩ : Piece env ctx p source scalarExpected)
  for (v,ctor,fact) in [(p.i,``HybridWord.Expr.index,``WordFrontendFacts.index),
      (p.x,``HybridWord.Expr.left,``WordFrontendFacts.left),(p.y,``HybridWord.Expr.right,``WordFrontendFacts.right)] do
    if sameTerm source v then return ← finishScalar (.const ctor) (app fact p.args)
  for k in List.range p.locals.length do
    if (p.locals[k]?.map (sameTerm source)).getD false then
      return ← finishScalar (.app ``HybridWord.Expr.local [.bindingIndex k]) (← localFact p k p.locals)
  if let some reducedSource := leadingLet source then
    let reduced ← rec reducedSource
    let checked ← reduced.checked.retarget conv (scalarExpected p reduced.code source)
    return ⟨reduced.code,checked,reduced.closed,reduced.represented⟩
  let args := source.getAppArgs.toList
  let head := source.getAppFn.constName?
  if head == some ``ite then
    let [_ty,condition,d,yes,no] := args | none
    let v ← nonzeroValue condition
    let e ← rec v
    let a ← rec yes
    let b ← rec no
    return ← finishScalar (known := e.checked.known.orElse (a.checked.known.orElse b.checked.known))
      (.app ``HybridWord.Expr.select [e.closedTerm,a.closedTerm,b.closedTerm])
      (app ``WordFrontendFacts.select ([e.code,a.code,b.code] ++ p.args ++
        [v,d,yes,no,e.checked.proof,a.checked.proof,b.checked.proof]))
  if head == some ``OfNat.ofNat then
    let literal ← closedTerm source
    return ← finishScalar (.app ``HybridWord.Expr.lit [literal]) (app ``WordFrontendFacts.literal (source::p.args))
  for (op,ctor,fact) in [(``HAdd.hAdd,``HybridWord.Expr.add,``WordFrontendFacts.add),
      (``HSub.hSub,``HybridWord.Expr.sub,``WordFrontendFacts.sub),
      (``HMul.hMul,``HybridWord.Expr.mul,``WordFrontendFacts.mul),
      (``HDiv.hDiv,``HybridWord.Expr.div,``WordFrontendFacts.div)] do
    if head == some op then
      let u ← args[args.length-2]?
      let v ← args[args.length-1]?
      let a ← rec u
      let b ← rec v
      return ← finishScalar (known := a.checked.known.orElse b.checked.known) (.app ctor [a.closedTerm,b.closedTerm])
        (app fact ([a.code,b.code] ++ p.args ++ [u,v,a.checked.proof,b.checked.proof]))
  if head == some ``Neg.neg then
    let v ← args.getLast?
    let a ← rec v
    return ← finishScalar (known := a.checked.known) (.app ``HybridWord.Expr.neg [a.closedTerm])
      (app ``WordFrontendFacts.neg ([a.code] ++ p.args ++ [v,a.checked.proof]))
  if head == some ``HybridWord.State.regs then
    let [s,r] := args | none
    if sameTerm s p.s then
      let register ← closedTerm r
      return ← finishScalar (.app ``HybridWord.Expr.reg [register]) (app ``WordFrontendFacts.register (r::p.args))
  none

def readStep (env : VEnv) (conv : Conversion env) (exposure : Exposure env)
    (ctx : List VExpr) (p : Inputs)
    (rec : (source : Lean.Expr) → Option (Piece env ctx p source scalarExpected))
    (source : Lean.Expr) : Option (Piece env ctx p source readExpected) := do
  let args := source.getAppArgs.toList
  if source.getAppFn.constName? != some ``GetElem?.getElem? then none else do
    let array ← args[args.length-2]?
    let index ← args[args.length-1]?
    if array.getAppFn.constName? != some ``HybridWord.State.arrays then none else do
      let [st,a] := array.getAppArgs.toList | none
      if !sameTerm st p.s then none else do
        let arrayCode ← closedTerm a
        if index.getAppFn.constName? == some ``BitVec.toNat then
          let [_width,k] := index.getAppArgs.toList | none
          let j ← rec k
          let code := ClosedTerm.app ``HybridWord.Expr.read [arrayCode,j.closedTerm]
          let proof := app ``WordFrontendFacts.read ([a,j.code] ++ p.args ++ [k,j.checked.proof])
          let checked ← finish env conv exposure ctx (readExpected p code source) code proof j.checked.known
          return ⟨code.val,checked,code.closed,code.represented⟩
        else if isClosed index && ((match index with | .lit (.natVal _) => true | _ => false) || index.getAppFn.constName? == some ``OfNat.ofNat) then
          let indexCode ← closedTerm index
          let code := ClosedTerm.app ``HybridWord.Expr.readNat [arrayCode,indexCode]
          let proof := app ``WordFrontendFacts.readNat ([a,index] ++ p.args)
          let checked ← finish env conv exposure ctx (readExpected p code source) code proof
          return ⟨code.val,checked,code.closed,code.represented⟩
        else none

def stepType := Lean.Expr.app (.const ``ForInStep [.zero]) state
def stepExpected (plain original : Lean.Expr) :=
  eq (option stepType) (app ``WordLoopFacts.lift [plain]) original

def bindHead (domain result : Lean.Expr) : Lean.Expr :=
  Lean.mkApp4 (.const ``Bind.bind [.zero,.zero]) (.const ``Option [.zero])
    (Lean.mkApp2 (.const ``Monad.toBind [.zero,.zero]) (.const ``Option [.zero])
      (.const ``instMonadOption [.zero])) domain result

structure StepPiece (env : VEnv) (ctx : List VExpr) (source : Lean.Expr) where
  plain : Lean.Expr
  checked : Artifact env ctx (stepExpected plain source)

def stepBodyStep (env : VEnv) (conv : Conversion env) (exposure : Exposure env)
    (rec : (ctx : List VExpr) → (source : Lean.Expr) → Option (StepPiece env ctx source))
    (ctx : List VExpr) (source : Lean.Expr) : Option (StepPiece env ctx source) := do
  let done (plain proof : Lean.Expr) (known : KnownTypes env 0 := noKnownTypes env 0) := do
    let h ← finish env conv exposure ctx (stepExpected plain source) plain proof known
    return (⟨plain,h⟩ : StepPiece env ctx source)
  let letParts := match source with
    | .letE binder ty value nextBody nondep => some (binder,ty,value,nextBody,nondep)
    | _ => none
  if let some (binder,ty,value,nextBody,nondep) := letParts then
    if compatible env conv ctx ty word || compatible env conv ctx ty state then
      let domain ← translate ty
      let child ← rec (domain.val::ctx) nextBody
      let plain := Lean.Expr.letE binder ty value child.plain nondep
      return ← done (known := child.checked.known) plain (app ``WordLoopFacts.letBinding
        [ty,value,.lam binder ty child.plain .default,
          .lam binder ty nextBody .default,.lam binder ty child.checked.proof .default])
  if let some reduced := leadingLet source then
    let child ← rec ctx reduced
    let checked ← child.checked.retarget conv (stepExpected child.plain source)
    return ⟨child.plain,checked⟩
  let args := source.getAppArgs.toList
  let head := source.getAppFn.constName?
  if head == some ``Pure.pure then
    let yield ← args.getLast?
    if yield.getAppFn.constName? == some ``ForInStep.yield then
      let value ← yield.getAppArgs.toList.getLast?
      return ← done (someExpr state value) (app ``WordLoopFacts.someYield [value])
  if head == some ``Bind.bind then
    let first ← args[args.length-2]?
    let fn ← args.getLast?
    let .lam bn ty b bi := fn | none
    if sameTerm ty (.const ``PUnit [.succ .zero]) then
      let child ← rec ctx (LeanBindings.instantiate (.const ``PUnit.unit [.succ .zero]) b)
      return ← done (known := child.checked.known) child.plain (app ``WordLoopFacts.bindUnit [child.plain,fn,child.checked.proof])
    if compatible env conv ctx ty state || compatible env conv ctx ty word then
      let domain ← translate ty
      let child ← rec (domain.val::ctx) b
      let plainFn := Lean.Expr.lam bn ty child.plain bi
      let proofFn := Lean.Expr.lam bn ty child.checked.proof bi
      let plain := Lean.mkApp2 (bindHead ty state) first plainFn
      return ← done (known := child.checked.known) plain (app (if compatible env conv ctx ty state then ``WordLoopFacts.bindState else ``WordLoopFacts.bindWord)
        [first,plainFn,fn,proofFn])
  if head == some ``ite then
    let [_ty,p,d,yes,no] := args | none
    let a ← rec ctx yes
    let b ← rec ctx no
    let plain := Lean.mkAppN (.const ``ite [.succ .zero]) #[option state,p,d,a.plain,b.plain]
    return ← done (known := a.checked.known.orElse b.checked.known) plain
      (app ``WordLoopFacts.branch [p,d,a.plain,b.plain,yes,no,a.checked.proof,b.checked.proof])
  none

abbrev PieceParser (env : VEnv) (spec : Inputs → Lean.Expr → Lean.Expr → Lean.Expr) :=
  (ctx : List VExpr) → (p : Inputs) → (source : Lean.Expr) → Option (Piece env ctx p source spec)
abbrev StepParser (env : VEnv) :=
  (ctx : List VExpr) → (source : Lean.Expr) → Option (StepPiece env ctx source)

/-- One syntactic body step. Recursive calls are parameters so that traversal
bounds can be reasoned about independently of certificate construction. -/

def bodyStep (env : VEnv) (conv : Conversion env) (exposure : Exposure env)
    (scalarCall : PieceParser env scalarExpected) (readCall : PieceParser env readExpected)
    (stepCall : StepParser env) (bodyCall : PieceParser env bodyExpected)
    (ctx : List VExpr) (p : Inputs) (source : Lean.Expr) :
    Option (Piece env ctx p source bodyExpected) := do
  let finishBody (code : ClosedTerm) (proof : Lean.Expr) (known : KnownTypes env 0 := noKnownTypes env 0) := do
    let h ← finish env conv exposure ctx (bodyExpected p code source) code proof known
    return (⟨code.val,h,code.closed,code.represented⟩ : Piece env ctx p source bodyExpected)
  let letParts := match source with
    | .letE binder ty value nextBody _ => some (binder, ty, value, nextBody)
    | _ => none
  if let some (binder, ty, value, nextBody) := letParts then
    if sameTerm ty state && sameTerm value p.s then
      let tyCore ← translate ty
      let p' := { p.lift with s := .bvar 0 }
      let b ← bodyCall (tyCore.val::ctx) p' nextBody
      return ← finishBody (known := b.checked.known) b.closedTerm
        (app ``WordFrontendFacts.letStateAlias ([b.code] ++ p.args ++
          [.lam binder ty nextBody .default,.lam binder ty b.checked.proof .default]))
    if !sameTerm ty state && compatible env conv ctx ty word then
      let e ← scalarCall ctx p value
      let tyCore ← translate ty
      let p' := { p.lift with locals := .bvar 0 :: p.lift.locals }
      let b ← bodyCall (tyCore.val::ctx) p' nextBody
      let next := Lean.Expr.lam binder ty nextBody .default
      let proofNext := Lean.Expr.lam binder ty b.checked.proof .default
      return ← finishBody (known := e.checked.known.orElse b.checked.known)
        (.app ``HybridWord.Cmd.letValue [e.closedTerm,b.closedTerm])
        (app ``WordFrontendFacts.letValue ([e.code,b.code] ++ p.args ++
          [value,next,e.checked.proof,proofNext]))
    if compatible env conv ctx ty state && !sameTerm value p.s then
      let a ← bodyCall ctx p (someExpr state value)
      let tyCore ← translate ty
      let p' := { p.lift with s := .bvar 0 }
      let b ← bodyCall (tyCore.val::ctx) p' nextBody
      let next := Lean.Expr.lam binder ty nextBody .default
      let proofNext := Lean.Expr.lam binder ty b.checked.proof .default
      return ← finishBody (known := a.checked.known.orElse b.checked.known) (.app ``HybridWord.Cmd.seq [a.closedTerm,b.closedTerm])
        (app ``WordFrontendFacts.letState ([a.code,b.code] ++ p.args ++
          [value,next,a.checked.proof,proofNext]))
  if let some reducedSource := leadingLet source then
    let reduced ← bodyCall ctx p reducedSource
    let checked ← reduced.checked.retarget conv (bodyExpected p reduced.code source)
    return ⟨reduced.code,checked,reduced.closed,reduced.represented⟩
  let args := source.getAppArgs.toList
  let head := source.getAppFn.constName?
  match head with
  | some ``ite => do
    let [_ty,condition,d,yes,no] := args | none
    let v ← nonzeroValue condition
    let e ← scalarCall ctx p v
    let a ← bodyCall ctx p yes
    let b ← bodyCall ctx p no
    return ← finishBody (known := e.checked.known.orElse (a.checked.known.orElse b.checked.known))
      (.app ``HybridWord.Cmd.branch [e.closedTerm,a.closedTerm,b.closedTerm])
      (app ``WordFrontendFacts.branch ([e.code,a.code,b.code] ++ p.args ++
        [v,d,yes,no,e.checked.proof,a.checked.proof,b.checked.proof]))
  | some ``ForIn.forIn => do
    let range ← args[args.length-3]?
    let initial ← args[args.length-2]?
    let fn ← args.getLast?
    if sameTerm initial p.s && range.getAppFn.constName? == some ``HybridWord.range then
      let [start,stop,stride] := range.getAppArgs.toList | none
      let startCode ← closedTerm start
      let stopCode ← closedTerm stop
      let strideCode ← closedTerm stride
      do
        let .lam kn kt (.lam tn st fnBody ti) ki := fn | none
        if !compatible env conv ctx st state || !compatible env conv ctx kt word then none else do
          let stCore ← translate st
          let ktCore ← translate kt
          let ctx' := stCore.val::ktCore.val::ctx
          let p2 := p.lift.lift
          let p' := { p2 with s := .bvar 0,locals := .bvar 1::p2.locals }
          let normalized ← stepCall ctx' fnBody
          let b ← bodyCall ctx' p' normalized.plain
          let composed := app ``WordLoopFacts.compose
            [evalCmd p' b.code,normalized.plain,fnBody,b.checked.proof,normalized.checked.proof]
          let proofNext := Lean.Expr.lam kn kt (.lam tn st composed ti) ki
          return ← finishBody (known := b.checked.known.orElse normalized.checked.known)
            (.app ``HybridWord.Cmd.forStatic [startCode,stopCode,strideCode,b.closedTerm])
            (app ``WordLoopFacts.forStatic ([start,stop,stride,b.code] ++ p.args ++ [fn,proofNext]))
    if !sameTerm initial p.s || range.getAppFn.constName? != some ``List.range then none else do
      let [nNat] := range.getAppArgs.toList | none
      if nNat.getAppFn.constName? != some ``BitVec.toNat then none else do
        let [width,n] := nNat.getAppArgs.toList | none
        let count ← scalarCall ctx p n
        let .lam kn kt (.lam tn st fnBody ti) ki := fn | none
        if !compatible env conv ctx st state || !sameTerm kt (.const ``Nat []) then none else do
          let stCore ← translate st
          let ktCore ← translate kt
          let ctx' := stCore.val::ktCore.val::ctx
          let p2 := p.lift.lift
          let index := app ``BitVec.ofNat [LeanBindings.rename (· + 2) width,.bvar 1]
          let p' := { p2 with s := .bvar 0,locals := index::p2.locals }
          let normalized ← stepCall ctx' fnBody
          let b ← bodyCall ctx' p' normalized.plain
          let composed := app ``WordLoopFacts.compose
            [evalCmd p' b.code,normalized.plain,fnBody,b.checked.proof,normalized.checked.proof]
          let proofNext := Lean.Expr.lam kn kt (.lam tn st composed ti) ki
          return ← finishBody (known := count.checked.known.orElse (b.checked.known.orElse normalized.checked.known))
            (.app ``HybridWord.Cmd.forRange [count.closedTerm,b.closedTerm])
            (app ``WordLoopFacts.forIn ([count.code,b.code] ++ p.args ++ [n,fn,count.checked.proof,proofNext]))
  | some ``List.foldlM => do
    let fn ← args[args.length-3]?
    let initial ← args[args.length-2]?
    let range ← args.getLast?
    if !sameTerm initial p.s || range.getAppFn.constName? != some ``List.range then none else do
      let [nNat] := range.getAppArgs.toList | none
      if nNat.getAppFn.constName? != some ``BitVec.toNat then none else do
        let [width,n] := nNat.getAppArgs.toList | none
        let count ← scalarCall ctx p n
        let .lam tn st (.lam kn kt fnBody ki) ti := fn | none
        if !compatible env conv ctx st state || !sameTerm kt (.const ``Nat []) then none else do
          let stCore ← translate st
          let ktCore ← translate kt
          let p2 := p.lift.lift
          let index := app ``BitVec.ofNat [LeanBindings.rename (· + 2) width,.bvar 0]
          let p' := { p2 with s := .bvar 1,locals := index::p2.locals }
          let b ← bodyCall (ktCore.val::stCore.val::ctx) p' fnBody
          let proofNext := Lean.Expr.lam tn st (.lam kn kt b.checked.proof ki) ti
          return ← finishBody (known := count.checked.known.orElse b.checked.known)
            (.app ``HybridWord.Cmd.forRange [count.closedTerm,b.closedTerm])
            (app ``WordFrontendFacts.forRange ([count.code,b.code] ++ p.args ++ [n,fn,count.checked.proof,proofNext]))
  | some ``HybridWord.State.copy => do
    let [st,destination,origin,count] := args | none
    if !sameTerm st p.s then none else do
      let destinationCode ← closedTerm destination
      let originCode ← closedTerm origin
      let countCode ← closedTerm count
      return ← finishBody (.app ``HybridWord.Cmd.copy [destinationCode,originCode,countCode])
        (app ``WordFrontendFacts.copy ([destination,origin,count] ++ p.args))
  | some ``HybridWord.State.write => do
    let [st,a,j,e] := args | none
    if !sameTerm st p.s then none else do
      let arrayCode ← closedTerm a
      let ja ← scalarCall ctx p j
      let ea ← scalarCall ctx p e
      return ← finishBody (known := ja.checked.known.orElse ea.checked.known)
        (.app ``HybridWord.Cmd.store [arrayCode,ja.closedTerm,ea.closedTerm])
        (app ``WordFrontendFacts.store ([a,ja.code,ea.code] ++ p.args ++ [j,e,ja.checked.proof,ea.checked.proof]))
  | some ``Pure.pure | some ``Option.some => do
    let value ← args.getLast?
    let surface := head == some ``Pure.pure
    if sameTerm value p.s then
      return ← finishBody (.const ``HybridWord.Cmd.skip)
        (app (if surface then ``WordFrontendFacts.skipPure else ``WordFrontendFacts.skip) p.args)
    if value.getAppFn.constName? == some ``HybridWord.State.set then
      let [st,r,e] := value.getAppArgs.toList | none
      if !sameTerm st p.s then none else do
        let registerCode ← closedTerm r
        let ea ← scalarCall ctx p e
        return ← finishBody (known := ea.checked.known) (.app ``HybridWord.Cmd.assign [registerCode,ea.closedTerm])
          (app (if surface then ``WordFrontendFacts.assignPure else ``WordFrontendFacts.assign)
            ([r,ea.code] ++ p.args ++ [e,ea.checked.proof]))
    none
  | some ``Bind.bind => do
    let first ← args[args.length-2]?
    let next ← args.getLast?
    let .lam binder ty nextBody info := next | none
    let tyCore ← translate ty
    -- An exact State binder is the state continuation. Do not ask the
    -- general alias converter whether it might instead be a Word binder.
    if !sameTerm ty state && compatible env conv ctx ty word then
      let value ← readCall ctx p first
      let p' := { p.lift with locals := .bvar 0 :: p.lift.locals }
      let b ← bodyCall (tyCore.val::ctx) p' nextBody
      let proofNext := Lean.Expr.lam binder ty b.checked.proof info
      return ← finishBody (known := value.checked.known.orElse b.checked.known)
        (.app ``HybridWord.Cmd.letValue [value.closedTerm,b.closedTerm])
        (app ``WordFrontendFacts.bindValue
          ([value.code,b.code] ++ p.args ++ [first,next,value.checked.proof,proofNext]))
    if compatible env conv ctx ty state then
      let a ← bodyCall ctx p first
      let p' := { p.lift with s := .bvar 0 }
      let b ← bodyCall (tyCore.val::ctx) p' nextBody
      let proofNext := Lean.Expr.lam binder ty b.checked.proof info
      return ← finishBody (known := a.checked.known.orElse b.checked.known) (.app ``HybridWord.Cmd.seq [a.closedTerm,b.closedTerm])
        (app ``WordFrontendFacts.sequence
          ([a.code,b.code] ++ p.args ++ [first,next,a.checked.proof,proofNext]))
    none
  | _ => none

def parameters : Inputs := ⟨.bvar 3,.bvar 2,.bvar 1,.bvar 0,[]⟩

/-- The named source application and generated evaluation are represented by
construction. Re-running partial expression translation at this final join
would add a failure branch without providing any new evidence. -/
def sourceApplication (name : Lean.Name) :
    {v // Represents (app name [parameters.i,parameters.x,parameters.y,parameters.s]) v} :=
  ⟨applications (.const name []) [.bvar 3,.bvar 2,.bvar 1,.bvar 0],
    app_represents (.constant rfl) (.cons .bvar (.cons .bvar (.cons .bvar (.cons .bvar .nil))))⟩

def targetEvaluation (code : Lean.Expr) (represented : {v // Represents code v}) :
    {v // Represents (evalCmd parameters code) v} :=
  ⟨applications (.const ``HybridWord.Cmd.eval [])
    [.bvar 3,.bvar 2,.bvar 1,represented.val,.bvar 0,
      .app (.const ``List.nil [.zero]) (.const ``HybridWord.Word [])],
    app_represents (.constant rfl) (.cons .bvar (.cons .bvar (.cons .bvar
      (.cons represented.property (.cons .bvar (.cons (.app (.constant rfl) (.constant rfl)) .nil))))))⟩

def namedEquality (name : Lean.Name) (code : Lean.Expr) (represented : {v // Represents code v}) :
    {v // Represents (bodyExpected parameters code
      (app name [parameters.i,parameters.x,parameters.y,parameters.s])) v} :=
  ⟨.app (.app (.app (.const ``Eq [.succ .zero])
    (.app (.const ``Option [.zero]) (.const ``HybridWord.State [])))
    (targetEvaluation code represented).val) (sourceApplication name).val,
    .app (.app (.app (.constant rfl) (.app (.constant rfl) (.constant rfl)))
      (targetEvaluation code represented).property) (sourceApplication name).property⟩

def closeLambda (e : Lean.Expr) : Lean.Expr :=
  Lean.Expr.lam `i word (.lam `x word (.lam `y word (.lam `s state e .default) .default) .default) .default
def closeForall (e : Lean.Expr) : Lean.Expr :=
  Lean.Expr.forallE `i word (.forallE `x word (.forallE `y word (.forallE `s state e .default) .default) .default) .default

def specification (name : Lean.Name) (code : Lean.Expr) : Lean.Expr :=
  closeForall (bodyExpected parameters code (app name [parameters.i,parameters.x,parameters.y,parameters.s]))

structure Result (native : Lean.Environment) (name : Lean.Name) where
  library : LeanEntryEnvironment.Loaded native name
  code : Lean.Expr
  closed : isClosed code = true
  proof : Artifact library.model [] (specification name code)

/-- In addition to the named-source equality certificate, a successful
syntax-directed derivation supplies a closed, well-typed command quotation.
This property does not assume native export or backend generation succeeds. -/
def Result.CodeTyped (result : Result native name) : Prop :=
  ∃ core, Represents result.code core ∧
    result.library.model.HasType 0 [] core (.const ``HybridWord.Cmd [])

def context : List VExpr := [.const ``HybridWord.State [],.const ``HybridWord.Word [],
  .const ``HybridWord.Word [],.const ``HybridWord.Word []]

def closeArtifact (env : VEnv) (a : Artifact env context expected) :
    Option (Artifact env [] (closeForall expected)) := do
  let w0 ← check env 0 [] (.const ``HybridWord.Word []) (.sort (.succ .zero))
  let w1 ← check env 0 [.const ``HybridWord.Word []] (.const ``HybridWord.Word []) (.sort (.succ .zero))
  let w2 ← check env 0 [.const ``HybridWord.Word [],.const ``HybridWord.Word []] (.const ``HybridWord.Word []) (.sort (.succ .zero))
  let s3 ← check env 0 [.const ``HybridWord.Word [],.const ``HybridWord.Word [],.const ``HybridWord.Word []]
    (.const ``HybridWord.State []) (.sort (.succ .zero))
  let core := VExpr.forallE (.const ``HybridWord.Word []) (.forallE (.const ``HybridWord.Word [])
    (.forallE (.const ``HybridWord.Word []) (.forallE (.const ``HybridWord.State []) a.core.val)))
  let pf := VExpr.lam (.const ``HybridWord.Word []) (.lam (.const ``HybridWord.Word [])
    (.lam (.const ``HybridWord.Word []) (.lam (.const ``HybridWord.State []) a.proofCore.val)))
  return ⟨a.code,closeLambda a.proof,
    ⟨core,.forallE (.constant rfl) (.forallE (.constant rfl) (.forallE (.constant rfl) (.forallE (.constant rfl) a.core.property)))⟩,
    ⟨pf,.lam (.constant rfl) (.lam (.constant rfl) (.lam (.constant rfl) (.lam (.constant rfl) a.proofCore.property)))⟩,
    .lamDF w0.down (.lamDF w1.down (.lamDF w2.down (.lamDF s3.down a.correct)))⟩

def optionState : VExpr := .app (.const ``Option [.zero]) (.const ``HybridWord.State [])
def eqHead : VExpr := .app (.const ``Eq [.succ .zero]) optionState
def equality (a b : VExpr) := VExpr.app (.app eqHead a) b

theorem result_congr {env : VEnv} {U : Nat} {ctx : List VExpr}
    {result source target : VExpr}
    (heq : env.HasType U ctx eqHead (.forallE optionState (.forallE optionState (.sort .zero))))
    (hl : env.HasType U ctx result optionState)
    (hr : env.IsDefEq U ctx source target optionState) :
    env.IsDefEq U ctx (equality result source) (equality result target) (.sort .zero) := by
  have h := VEnv.IsDefEq.appDF heq hl
  simp only [optionState, VExpr.inst] at h
  exact .appDF h hr

/-- Structural decrease measure for traversal of the original expression.
It is not an execution-cycle bound or an optimization-search budget. -/
def syntaxSize : Lean.Expr → Nat
  | .app f a => syntaxSize f + syntaxSize a + 1
  | .lam _ ty b _ | .forallE _ ty b _ => syntaxSize ty + syntaxSize b + 1
  | .letE _ ty v b _ => syntaxSize ty + syntaxSize v + syntaxSize b + 1
  | .mdata _ b | .proj _ _ b => syntaxSize b + 1
  | _ => 1

/-- Shared named-source connection, independent of the body traversal. -/
def compileWith
    (parseBody : (env : VEnv) → Conversion env → Exposure env →
      (ctx : List VExpr) → (p : Inputs) → (source : Lean.Expr) →
      Option (Piece env ctx p source bodyExpected))
    (native : Lean.Environment) (name : Lean.Name) :
    Option (Result native name) := do
  let lib ← load native name
  let source := LeanSourceEntry.strip lib.source.declaration.value
  let .lam _ wi (.lam _ wx (.lam _ wy (.lam _ st original _) _) _) _ := source | none
  if !(compatible lib.model lib.conversion [] wi word) ||
      !(compatible lib.model lib.conversion [] wx word) || !(compatible lib.model lib.conversion [] wy word) ||
      !(compatible lib.model lib.conversion [] st state) then none else do
    let parsed ← parseBody lib.model lib.conversion lib.exposure context parameters original
    let sourceApp := sourceApplication name
    let rules : List (LeanTypeReduction.Rule lib.model) := [⟨native,name,lib.source,lib.registered⟩]
    let reduced ← LeanTypeReduction.step rules lib.conversion 0 context lib.exposure sourceApp.val
    let target := targetEvaluation parsed.code parsed.represented
    let expected := namedEquality name parsed.code parsed.represented
    let heq ← check lib.model 0 context eqHead (.forallE optionState (.forallE optionState (.sort .zero)))
    let ht ← checkWith lib.model lib.conversion 0 context target.val optionState lib.exposure
    if typeSame : reduced.val.2 = optionState then
      if before : parsed.checked.core.val = equality target.val reduced.val.1 then
        have reduction : lib.model.IsDefEq 0 context sourceApp.val reduced.val.1 optionState :=
          by simpa only [typeSame] using reduced.property
        have cast := result_congr heq.down ht.down reduction
        let named : Artifact lib.model context
            (bodyExpected parameters parsed.code (app name [parameters.i,parameters.x,parameters.y,parameters.s])) :=
          ⟨parsed.code,parsed.checked.proof,expected,parsed.checked.proofCore,
            .defeq cast.symm (before ▸ parsed.checked.correct)⟩
        let proof ← closeArtifact lib.model named
        return ⟨lib,parsed.code,parsed.closed,proof⟩
      else none
    else none

/-- Same formal boundary as LeanBodyPipeline.Result.correct: declarations and
reduction rules come from the native environment, and the emitted proof has
the exact named-source equality type. This is not an evaluator for a newly
invented source language, nor a per-input optimization equivalence test. -/
theorem Result.correct (r : Result native name) :
    LeanEnvironmentProvenance.Faithful native r.library.model ∧
    Represents (specification name r.code) r.proof.core.val ∧
    r.library.model.HasType 0 [] r.proof.proofCore.val r.proof.core.val :=
  ⟨r.library.faithful,r.proof.core.property,r.proof.correct⟩

end IRComparison.WordFrontend
