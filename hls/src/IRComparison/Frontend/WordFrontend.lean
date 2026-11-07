import IRComparison.Core.WordLoopFacts
import IRComparison.Frontend.LeanEntryEnvironment
import IRComparison.Frontend.LeanCertificate

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

structure Inputs where
  i : Lean.Expr
  x : Lean.Expr
  y : Lean.Expr
  s : Lean.Expr
  locals : List Lean.Expr := []

def Inputs.list (p : Inputs) := p.locals.foldr consWord nilWords
def Inputs.args (p : Inputs) := [p.i,p.x,p.y,p.s,p.list]
def Inputs.lift (p : Inputs) : Inputs :=
  ⟨p.i.liftLooseBVars 0 1,p.x.liftLooseBVars 0 1,p.y.liftLooseBVars 0 1,
    p.s.liftLooseBVars 0 1,p.locals.map (·.liftLooseBVars 0 1)⟩

def evalExpr (p : Inputs) (code : Lean.Expr) := app ``HybridWord.Expr.eval (p.args ++ [code])
def evalCmd (p : Inputs) (code : Lean.Expr) :=
  app ``HybridWord.Cmd.eval [p.i,p.x,p.y,code,p.s,p.list]

structure Artifact (env : VEnv) (ctx : List VExpr) (expected : Lean.Expr) where
  code : Lean.Expr
  proof : Lean.Expr
  core : {v // Represents expected v}
  proofCore : {v // Represents proof v}
  correct : env.HasType 0 ctx proofCore.val core.val

/-- Only the types of the composed facts are checked here. No program
equivalence solver, execution test, or optimizer certificate is substituted. -/
def finish (env : VEnv) (conv : Conversion env) (exposure : Exposure env)
    (ctx : List VExpr) (expected code proof : Lean.Expr) : Option (Artifact env ctx expected) := do
  let core ← translate expected
  let proofCore ← translate proof
  let h ← checkWith env conv 0 ctx proofCore.val core.val exposure
  return ⟨code,proof,core,proofCore,h.down⟩

def declarations : List Lean.Name :=
  [``WordLoopFacts.lift, ``WordLoopFacts.someYield, ``WordLoopFacts.bindState,
   ``WordLoopFacts.bindWord, ``WordLoopFacts.bindUnit, ``WordLoopFacts.branch,
   ``WordLoopFacts.compose, ``WordLoopFacts.forIn,
   ``WordFrontendFacts.literal, ``WordFrontendFacts.index, ``WordFrontendFacts.left,
   ``WordFrontendFacts.right, ``WordFrontendFacts.localZero, ``WordFrontendFacts.localSucc,
   ``WordFrontendFacts.register, ``WordFrontendFacts.add, ``WordFrontendFacts.sub,
   ``WordFrontendFacts.mul, ``WordFrontendFacts.div, ``WordFrontendFacts.read, ``WordFrontendFacts.readNat,
   ``WordFrontendFacts.skip, ``WordFrontendFacts.assign, ``WordFrontendFacts.skipPure, ``WordFrontendFacts.assignPure, ``WordFrontendFacts.store,
   ``WordFrontendFacts.bindValue, ``WordFrontendFacts.sequence, ``WordFrontendFacts.branch,
   ``WordFrontendFacts.select, ``WordFrontendFacts.forRange, ``WordFrontendFacts.neg,
   ``HybridWord.Expr.neg,
   ``HybridWord.Expr, ``HybridWord.Expr.eval, ``HybridWord.Cmd, ``HybridWord.Cmd.eval,
   ``HybridWord.Expr.lit, ``HybridWord.Expr.index, ``HybridWord.Expr.left, ``HybridWord.Expr.right,
   ``HybridWord.Expr.local, ``HybridWord.Expr.reg, ``HybridWord.Expr.add, ``HybridWord.Expr.sub,
   ``HybridWord.Expr.mul, ``HybridWord.Expr.div, ``HybridWord.Expr.read, ``HybridWord.Expr.readNat, ``HybridWord.Expr.select,
   ``HybridWord.Cmd.skip, ``HybridWord.Cmd.assign, ``HybridWord.Cmd.store, ``HybridWord.Cmd.letValue,
   ``HybridWord.Cmd.seq, ``HybridWord.Cmd.branch, ``HybridWord.Cmd.repeat, ``HybridWord.Cmd.forRange,
   ``Nat.zero, ``Nat.succ, ``Nat, ``BitVec, ``List, ``Option,
   ``HybridWord.Word, ``HybridWord.State, ``List.nil, ``List.cons, ``Eq, ``Option.some]

/-- Close imported signatures under their declared type dependencies. -/
def dependencies (native : Lean.Environment) : Nat → List Lean.Name → List Lean.Name → Option (List Lean.Name)
  | _,[],seen => some seen
  | 0,_::_,_ => none
  | fuel+1,n::todo,seen =>
    if n ∈ seen then dependencies native fuel todo seen else do
      let info ← native.find? n
      dependencies native fuel (LeanEntryEnvironment.constants info.type ++ todo) (n::seen)

def load (native : Lean.Environment) (name : Lean.Name) : Option (LeanEntryEnvironment.Loaded native name) := do
  let source ← LeanTypeReduction.load native name
  let names := (name :: LeanEntryEnvironment.constants source.declaration.value ++ declarations ++
    [``outParam,``optParam,``DecidableEq]).eraseDups
  let names ← dependencies native 8192 names []
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
  if actual == expected then true else
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

def localFact (p : Inputs) : Nat → List Lean.Expr → Option Lean.Expr
  | _,[] => none
  | 0,v::vs => some (app ``WordFrontendFacts.localZero [p.i,p.x,p.y,p.s,v,vs.foldr consWord nilWords])
  | n+1,v::vs => do
    let proof ← localFact p n vs
    let w ← vs[n]?
    return app ``WordFrontendFacts.localSucc
      [.lit (.natVal n),p.i,p.x,p.y,p.s,v,w,vs.foldr consWord nilWords,proof]

def nonzeroValue (condition : Lean.Expr) : Option Lean.Expr := do
  if condition.getAppFn.constName? != some ``Eq then none else do
    let [_ty,test,_truth] := condition.getAppArgs.toList | none
    if test.getAppFn.constName? != some ``bne then none else do
      let [_ty,_instance,v,z] := test.getAppArgs.toList | none
      if z.getAppFn.constName? != some ``OfNat.ofNat then none else do
        let [_ty,.lit (.natVal 0),_instance] := z.getAppArgs.toList | none
        return v

def leadingLet : Lean.Expr → Option Lean.Expr
  | .letE _ _ value next _ => some (next.instantiate1 value)
  | _ => none

def scalar (env : VEnv) (conv : Conversion env) (exposure : Exposure env)
    (ctx : List VExpr) (p : Inputs) : Nat → (source : Lean.Expr) →
    Option (Piece env ctx p source scalarExpected)
  | 0,_ => none
  | fuel+1,source => do
    let finishScalar (code proof : Lean.Expr) := do
      let h ← finish env conv exposure ctx (scalarExpected p code source) code proof
      return (⟨code,h⟩ : Piece env ctx p source scalarExpected)
    for (v,ctor,fact) in [(p.i,``HybridWord.Expr.index,``WordFrontendFacts.index),
        (p.x,``HybridWord.Expr.left,``WordFrontendFacts.left),(p.y,``HybridWord.Expr.right,``WordFrontendFacts.right)] do
      if source == v then return ← finishScalar (.const ctor []) (app fact p.args)
    for k in List.range p.locals.length do
      if p.locals[k]? == some source then
        return ← finishScalar (app ``HybridWord.Expr.local [.lit (.natVal k)]) (← localFact p k p.locals)
    if let some reducedSource := leadingLet source then
      let reduced ← scalar env conv exposure ctx p fuel reducedSource
      return ← finishScalar reduced.code reduced.checked.proof
    let args := source.getAppArgs.toList
    let head := source.getAppFn.constName?
    if head == some ``ite then
      let [_ty,condition,d,yes,no] := args | none
      let v ← nonzeroValue condition
      let e ← scalar env conv exposure ctx p fuel v
      let a ← scalar env conv exposure ctx p fuel yes
      let b ← scalar env conv exposure ctx p fuel no
      return ← finishScalar (app ``HybridWord.Expr.select [e.code,a.code,b.code])
        (app ``WordFrontendFacts.select ([e.code,a.code,b.code] ++ p.args ++
          [v,d,yes,no,e.checked.proof,a.checked.proof,b.checked.proof]))
    if head == some ``OfNat.ofNat && !source.hasLooseBVars then
      return ← finishScalar (app ``HybridWord.Expr.lit [source]) (app ``WordFrontendFacts.literal (source::p.args))
    for (op,ctor,fact) in [(``HAdd.hAdd,``HybridWord.Expr.add,``WordFrontendFacts.add),
        (``HSub.hSub,``HybridWord.Expr.sub,``WordFrontendFacts.sub),
        (``HMul.hMul,``HybridWord.Expr.mul,``WordFrontendFacts.mul),
        (``HDiv.hDiv,``HybridWord.Expr.div,``WordFrontendFacts.div)] do
      if head == some op then
        let u ← args[args.length-2]?
        let v ← args[args.length-1]?
        let a ← scalar env conv exposure ctx p fuel u
        let b ← scalar env conv exposure ctx p fuel v
        return ← finishScalar (app ctor [a.code,b.code])
          (app fact ([a.code,b.code] ++ p.args ++ [u,v,a.checked.proof,b.checked.proof]))
    if head == some ``Neg.neg then
      let v ← args.getLast?
      let a ← scalar env conv exposure ctx p fuel v
      return ← finishScalar (app ``HybridWord.Expr.neg [a.code])
        (app ``WordFrontendFacts.neg ([a.code] ++ p.args ++ [v,a.checked.proof]))
    if head == some ``HybridWord.State.regs then
      let [s,r] := args | none
      if s == p.s && !r.hasLooseBVars then
        return ← finishScalar (app ``HybridWord.Expr.reg [r]) (app ``WordFrontendFacts.register (r::p.args))
    none

def read (env : VEnv) (conv : Conversion env) (exposure : Exposure env)
    (ctx : List VExpr) (p : Inputs) (fuel : Nat) (source : Lean.Expr) :
    Option (Piece env ctx p source readExpected) := do
  let args := source.getAppArgs.toList
  if source.getAppFn.constName? != some ``GetElem?.getElem? then none else do
    let array ← args[args.length-2]?
    let index ← args[args.length-1]?
    if array.getAppFn.constName? != some ``HybridWord.State.arrays then none else do
      let [st,a] := array.getAppArgs.toList | none
      if st != p.s || a.hasLooseBVars then none else do
        if index.getAppFn.constName? == some ``BitVec.toNat then
          let [_width,k] := index.getAppArgs.toList | none
          let j ← scalar env conv exposure ctx p fuel k
          let code := app ``HybridWord.Expr.read [a,j.code]
          let proof := app ``WordFrontendFacts.read ([a,j.code] ++ p.args ++ [k,j.checked.proof])
          let checked ← finish env conv exposure ctx (readExpected p code source) code proof
          return ⟨code,checked⟩
        else if !index.hasLooseBVars && ((match index with | .lit (.natVal _) => true | _ => false) || index.getAppFn.constName? == some ``OfNat.ofNat) then
          let code := app ``HybridWord.Expr.readNat [a,index]
          let proof := app ``WordFrontendFacts.readNat ([a,index] ++ p.args)
          let checked ← finish env conv exposure ctx (readExpected p code source) code proof
          return ⟨code,checked⟩
        else none

def stepType := Lean.Expr.app (.const ``ForInStep [.zero]) state
def stepExpected (plain original : Lean.Expr) :=
  eq (option stepType) (app ``WordLoopFacts.lift [plain]) original

def bindHead (domain result : Lean.Expr) : Lean.Expr :=
  Lean.mkAppN (.const ``Bind.bind [.zero,.zero]) #[.const ``Option [.zero],
    Lean.mkAppN (.const ``Monad.toBind [.zero,.zero]) #[.const ``Option [.zero],.const ``instMonadOption [.zero]],domain,result]

structure StepPiece (env : VEnv) (ctx : List VExpr) (source : Lean.Expr) where
  plain : Lean.Expr
  checked : Artifact env ctx (stepExpected plain source)

def stepBody (env : VEnv) (conv : Conversion env) (exposure : Exposure env)
    (ctx : List VExpr) : Nat → (source : Lean.Expr) → Option (StepPiece env ctx source)
  | 0,_ => none
  | fuel+1,source => do
    let done (plain proof : Lean.Expr) := do
      let h ← finish env conv exposure ctx (stepExpected plain source) plain proof
      return (⟨plain,h⟩ : StepPiece env ctx source)
    if let some reduced := leadingLet source then
      let child ← stepBody env conv exposure ctx fuel reduced
      return ← done child.plain child.checked.proof
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
      if ty == .const ``PUnit [.succ .zero] then
        let child ← stepBody env conv exposure ctx fuel (b.instantiate1 (.const ``PUnit.unit [.succ .zero]))
        return ← done child.plain (app ``WordLoopFacts.bindUnit [child.plain,fn,child.checked.proof])
      if ty == state || ty == word then
        let domain ← translate ty
        let child ← stepBody env conv exposure (domain.val::ctx) fuel b
        let plainFn := Lean.Expr.lam bn ty child.plain bi
        let proofFn := Lean.Expr.lam bn ty child.checked.proof bi
        let plain := Lean.mkApp2 (bindHead ty state) first plainFn
        return ← done plain (app (if ty == state then ``WordLoopFacts.bindState else ``WordLoopFacts.bindWord)
          [first,plainFn,fn,proofFn])
    if head == some ``ite then
      let [_ty,p,d,yes,no] := args | none
      let a ← stepBody env conv exposure ctx fuel yes
      let b ← stepBody env conv exposure ctx fuel no
      let plain := Lean.mkAppN (.const ``ite [.succ .zero]) #[option state,p,d,a.plain,b.plain]
      return ← done plain (app ``WordLoopFacts.branch [p,d,a.plain,b.plain,yes,no,a.checked.proof,b.checked.proof])
    none

def body (env : VEnv) (conv : Conversion env) (exposure : Exposure env)
    (ctx : List VExpr) (p : Inputs) : Nat → (source : Lean.Expr) →
    Option (Piece env ctx p source bodyExpected)
  | 0,_ => none
  | fuel+1,source => do
    let finishBody (code proof : Lean.Expr) := do
      let h ← finish env conv exposure ctx (bodyExpected p code source) code proof
      return (⟨code,h⟩ : Piece env ctx p source bodyExpected)
    if let some reducedSource := leadingLet source then
      let reduced ← body env conv exposure ctx p fuel reducedSource
      return ← finishBody reduced.code reduced.checked.proof
    let args := source.getAppArgs.toList
    let head := source.getAppFn.constName?
    if head == some ``ite then
      let [_ty,condition,d,yes,no] := args | none
      let v ← nonzeroValue condition
      let e ← scalar env conv exposure ctx p fuel v
      let a ← body env conv exposure ctx p fuel yes
      let b ← body env conv exposure ctx p fuel no
      return ← finishBody (app ``HybridWord.Cmd.branch [e.code,a.code,b.code])
        (app ``WordFrontendFacts.branch ([e.code,a.code,b.code] ++ p.args ++
          [v,d,yes,no,e.checked.proof,a.checked.proof,b.checked.proof]))
    if head == some ``ForIn.forIn then
      let range ← args[args.length-3]?
      let initial ← args[args.length-2]?
      let fn ← args.getLast?
      if initial != p.s || range.getAppFn.constName? != some ``List.range then none else do
        let [nNat] := range.getAppArgs.toList | none
        if nNat.getAppFn.constName? != some ``BitVec.toNat then none else do
          let [width,n] := nNat.getAppArgs.toList | none
          let count ← scalar env conv exposure ctx p fuel n
          let .lam kn kt (.lam tn st fnBody ti) ki := fn | none
          if st != state || kt != .const ``Nat [] then none else do
            let stCore ← translate st
            let ktCore ← translate kt
            let ctx' := stCore.val::ktCore.val::ctx
            let p2 := p.lift.lift
            let index := app ``BitVec.ofNat [width.liftLooseBVars 0 2,.bvar 1]
            let p' := { p2 with s := .bvar 0,locals := index::p2.locals }
            let normalized ← stepBody env conv exposure ctx' fuel fnBody
            let b ← body env conv exposure ctx' p' fuel normalized.plain
            let composed := app ``WordLoopFacts.compose
              [evalCmd p' b.code,normalized.plain,fnBody,b.checked.proof,normalized.checked.proof]
            let proofNext := Lean.Expr.lam kn kt (.lam tn st composed ti) ki
            return ← finishBody (app ``HybridWord.Cmd.forRange [count.code,b.code])
              (app ``WordLoopFacts.forIn ([count.code,b.code] ++ p.args ++ [n,fn,count.checked.proof,proofNext]))
    if head == some ``List.foldlM then
      let fn ← args[args.length-3]?
      let initial ← args[args.length-2]?
      let range ← args.getLast?
      if initial != p.s || range.getAppFn.constName? != some ``List.range then none else do
        let [nNat] := range.getAppArgs.toList | none
        if nNat.getAppFn.constName? != some ``BitVec.toNat then none else do
          let [width,n] := nNat.getAppArgs.toList | none
          let count ← scalar env conv exposure ctx p fuel n
          let .lam tn st (.lam kn kt fnBody ki) ti := fn | none
          if st != state || kt != .const ``Nat [] then none else do
            let stCore ← translate st
            let ktCore ← translate kt
            let p2 := p.lift.lift
            let index := app ``BitVec.ofNat [width.liftLooseBVars 0 2,.bvar 0]
            let p' := { p2 with s := .bvar 1,locals := index::p2.locals }
            let b ← body env conv exposure (ktCore.val::stCore.val::ctx) p' fuel fnBody
            let proofNext := Lean.Expr.lam tn st (.lam kn kt b.checked.proof ki) ti
            return ← finishBody (app ``HybridWord.Cmd.forRange [count.code,b.code])
              (app ``WordFrontendFacts.forRange ([count.code,b.code] ++ p.args ++ [n,fn,count.checked.proof,proofNext]))
    if head == some ``HybridWord.State.write then
      let [st,a,j,e] := args | none
      if st != p.s || a.hasLooseBVars then none else do
        let ja ← scalar env conv exposure ctx p fuel j
        let ea ← scalar env conv exposure ctx p fuel e
        return ← finishBody (app ``HybridWord.Cmd.store [a,ja.code,ea.code])
          (app ``WordFrontendFacts.store ([a,ja.code,ea.code] ++ p.args ++ [j,e,ja.checked.proof,ea.checked.proof]))
    if head == some ``Pure.pure || head == some ``Option.some then
      let value ← args.getLast?
      let surface := head == some ``Pure.pure
      if value == p.s then
        return ← finishBody (.const ``HybridWord.Cmd.skip [])
          (app (if surface then ``WordFrontendFacts.skipPure else ``WordFrontendFacts.skip) p.args)
      if value.getAppFn.constName? == some ``HybridWord.State.set then
        let [st,r,e] := value.getAppArgs.toList | none
        if st != p.s || r.hasLooseBVars then none else do
          let ea ← scalar env conv exposure ctx p fuel e
          return ← finishBody (app ``HybridWord.Cmd.assign [r,ea.code])
            (app (if surface then ``WordFrontendFacts.assignPure else ``WordFrontendFacts.assign)
              ([r,ea.code] ++ p.args ++ [e,ea.checked.proof]))
    if head == some ``Bind.bind then
      let first ← args[args.length-2]?
      let next ← args.getLast?
      let .lam binder ty nextBody info := next | none
      let tyCore ← translate ty
      if ty == word then
        let value ← read env conv exposure ctx p fuel first
        let p' := { p.lift with locals := .bvar 0 :: p.lift.locals }
        let b ← body env conv exposure (tyCore.val::ctx) p' fuel nextBody
        let proofNext := Lean.Expr.lam binder ty b.checked.proof info
        return ← finishBody (app ``HybridWord.Cmd.letValue [value.code,b.code])
          (app ``WordFrontendFacts.bindValue
            ([value.code,b.code] ++ p.args ++ [first,next,value.checked.proof,proofNext]))
      if ty == state then
        let a ← body env conv exposure ctx p fuel first
        let p' := { p.lift with s := .bvar 0 }
        let b ← body env conv exposure (tyCore.val::ctx) p' fuel nextBody
        let proofNext := Lean.Expr.lam binder ty b.checked.proof info
        return ← finishBody (app ``HybridWord.Cmd.seq [a.code,b.code])
          (app ``WordFrontendFacts.sequence
            ([a.code,b.code] ++ p.args ++ [first,next,a.checked.proof,proofNext]))
    none

def parameters : Inputs := ⟨.bvar 3,.bvar 2,.bvar 1,.bvar 0,[]⟩
def closeLambda (e : Lean.Expr) : Lean.Expr :=
  Lean.Expr.lam `i word (.lam `x word (.lam `y word (.lam `s state e .default) .default) .default) .default
def closeForall (e : Lean.Expr) : Lean.Expr :=
  Lean.Expr.forallE `i word (.forallE `x word (.forallE `y word (.forallE `s state e .default) .default) .default) .default

def specification (name : Lean.Name) (code : Lean.Expr) : Lean.Expr :=
  closeForall (bodyExpected parameters code (app name [parameters.i,parameters.x,parameters.y,parameters.s]))

structure Result (native : Lean.Environment) (name : Lean.Name) where
  library : LeanEntryEnvironment.Loaded native name
  code : Lean.Expr
  closed : code.hasLooseBVars = false
  proof : Artifact library.model [] (specification name code)

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

def compile (native : Lean.Environment) (name : Lean.Name) (fuel : Nat := 64) :
    Option (Result native name) := do
  let lib ← load native name
  let source := LeanSourceEntry.strip lib.source.declaration.value
  let .lam _ wi (.lam _ wx (.lam _ wy (.lam _ st original _) _) _) _ := source | none
  if !(compatible lib.model lib.conversion [] wi word) ||
      !(compatible lib.model lib.conversion [] wx word) || !(compatible lib.model lib.conversion [] wy word) ||
      !(compatible lib.model lib.conversion [] st state) then none else do
    let parsed ← body lib.model lib.conversion lib.exposure context parameters fuel original
    if closed : parsed.code.hasLooseBVars = false then
      let sourceApp ← translate (app name [parameters.i,parameters.x,parameters.y,parameters.s])
      let rules : List (LeanTypeReduction.Rule lib.model) := [⟨native,name,lib.source,lib.registered⟩]
      let reduced ← LeanTypeReduction.step rules lib.conversion 0 context lib.exposure sourceApp.val
      let target ← translate (evalCmd parameters parsed.code)
      let expected ← translate (bodyExpected parameters parsed.code (app name [parameters.i,parameters.x,parameters.y,parameters.s]))
      let heq ← check lib.model 0 context eqHead (.forallE optionState (.forallE optionState (.sort .zero)))
      let ht ← checkWith lib.model lib.conversion 0 context target.val optionState lib.exposure
      if typeSame : reduced.val.2 = optionState then
        if before : parsed.checked.core.val = equality target.val reduced.val.1 then
          if after : expected.val = equality target.val sourceApp.val then
            have reduction : lib.model.IsDefEq 0 context sourceApp.val reduced.val.1 optionState :=
              by simpa only [typeSame] using reduced.property
            have cast := result_congr heq.down ht.down reduction
            let named : Artifact lib.model context
                (bodyExpected parameters parsed.code (app name [parameters.i,parameters.x,parameters.y,parameters.s])) :=
              ⟨parsed.code,parsed.checked.proof,expected,parsed.checked.proofCore,
                by rw [after]; exact .defeq cast.symm (before ▸ parsed.checked.correct)⟩
            let proof ← closeArtifact lib.model named
            return ⟨lib,parsed.code,closed,proof⟩
          else none
        else none
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
