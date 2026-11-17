import IRComparison.Frontend.WordScalarEnvironment
import IRComparison.Frontend.WordRetainedConversion
import IRComparison.Frontend.WordBinder

/-! Single traversal of ordinary Lean bodies, pure State expressions and
ForInStep continuations. No iteration expansion or normalized-body reparse.
Helper calls always retain scalar arguments. The runtime traversal and the
independent source induction have no direct-substitution mode. -/
namespace IRComparison.WordFrontend.StructuralBody
open Lean4Lean LeanTyped LeanTypeInference

inductive Mode where
  | body | value | step
  deriving DecidableEq, BEq

def Mode.expected : Mode → Inputs → Lean.Expr → Lean.Expr → Lean.Expr
  | .body,p,code,source => bodyExpected p code source
  | .value,p,code,source => bodyExpected p code (someExpr state source)
  | .step,p,code,source => stepExpected (evalCmd p code) source

abbrev Child := ScalarEnvironment.Child

structure LetParts (source : Lean.Expr) where
  name : Lean.Name
  type : Lean.Expr
  value : Child source
  body : Child source

def letParts : (source : Lean.Expr) → Option (LetParts source)
  | .letE name ty value body _ => some ⟨name,ty,
      ⟨value,by simp only [syntaxSize]; omega⟩,
      ⟨body,by simp only [syntaxSize]; omega⟩⟩
  | _ => none

structure LambdaParts (source : Lean.Expr) where
  name : Lean.Name
  type : Lean.Expr
  body : Child source
  info : Lean.BinderInfo

def lambdaParts (child : Child source) : Option (LambdaParts source) :=
  match h : child.val with
  | .lam name ty body info => some ⟨name,ty,⟨body,by
      have smaller := child.property
      rw [h] at smaller
      simp only [syntaxSize] at smaller
      omega⟩,info⟩
  | _ => none

def arguments (child : Child source) : List (Child source) :=
  (ScalarEnvironment.arguments child.val).map (ScalarEnvironment.below child)

/-- A first-order administrative continuation captures its lexical scope.
Its arguments are source values, never parser functions. This prevents a
recursive function environment and does not introduce a user-facing DSL. -/
structure Continuation (env : VEnv) where
  apply : (ctx : List VExpr) → (p : Inputs) → (mode : Mode) → List Lean.Expr →
    Option ((source : Lean.Expr) × Piece env ctx p source mode.expected)

abbrev Continuations (env : VEnv) := Nat → Option (Continuation env)
def underFunctions (fs : Continuations env) : Continuations env
  | 0 => none
  | n+1 => fs n

/-- Ordinary binder traversal needs no term reconstruction. Only actual
administrative applications/aliases carry an explicit substitution. -/
inductive Substitution where
  | identity
  | bindings (lookup : Nat → Lean.Expr)

def Substitution.reference : Substitution → Nat → Lean.Expr
  | .identity => Lean.Expr.bvar
  | .bindings lookup => lookup

def Substitution.apply (σ : Substitution) (source : Lean.Expr) : Lean.Expr :=
  match σ with
  | .identity => source
  | .bindings lookup => LeanBindings.substitute lookup source

def under : Substitution → Substitution
  | .identity => .identity
  | .bindings lookup => .bindings (LeanBindings.underSubst lookup)

theorem Substitution.apply_eq (σ : Substitution) (source : Lean.Expr) :
    σ.apply source = LeanBindings.substitute σ.reference source := by
  cases σ with
  | identity => exact (LeanBindings.substitute_id source).symm
  | bindings => rfl

theorem under_reference (σ : Substitution) :
    (under σ).reference = LeanBindings.underSubst σ.reference := by
  cases σ with
  | identity =>
    funext n
    cases n <;> rfl
  | bindings => rfl

/-- The body and parameter list are subterms of the original lambda chain. -/
def lambdaChain : (source : Lean.Expr) → Option (List Lean.Expr × Child source)
  | .lam _ ty body _ =>
    match lambdaChain body with
    | some (types,child) => some (ty::types,⟨child.val,by
        have h := child.property
        simp only [syntaxSize]; omega⟩)
    | none => some ([ty],⟨body,by simp only [syntaxSize]; omega⟩)
  | _ => none

def continuationParts (child : Child source) : Option (List Lean.Expr × Child source) := do
  let (types,body) ← lambdaChain child.val
  return (types,ScalarEnvironment.below child body)

def applicationHead : (source : Lean.Expr) → Option (Child source)
  | .app f _ =>
    match applicationHead f with
    | some child => some ⟨child.val,by have h := child.property; simp only [syntaxSize]; omega⟩
    | none => some ⟨f,by simp only [syntaxSize]; omega⟩
  | _ => none

/-- The recursive callback only accepts children of the original source.
Captured continuations retain this same callback; calling a helper never
restarts traversal on the substituted body. -/
abbrev Recursor (env : VEnv) (raw : Lean.Expr) :=
  (ctx : List VExpr) → (p : Inputs) → (mode : Mode) →
    (σ : Substitution) → Continuations env →
    (child : Child raw) → Option (Piece env ctx p (σ.apply child.val) mode.expected)

/-- Arguments occupy the innermost de Bruijn positions in reverse order.
The remaining positions refer to the captured scope, shifted only by the
actual number of intervening binders. This is not a traversal budget. -/
def closureReference (captureDepth targetDepth : Nat) (σ : Substitution)
    (args : List Lean.Expr) (n : Nat) : Lean.Expr :=
  match args.reverse[n]? with
  | some arg => arg
  | none => LeanBindings.rename (· + (targetDepth - captureDepth)) (σ.reference (n - args.length))

def closureSubstitution (captureDepth targetDepth : Nat) (σ : Substitution)
    (args : List Lean.Expr) : Substitution :=
  .bindings (closureReference captureDepth targetDepth σ args)

def closureFunctions (fs : Continuations env) (arity : Nat) : Continuations env :=
  fun n => if n < arity then none else fs (n - arity)

def captureContinuation (rec : Recursor env raw) (captureDepth : Nat)
    (σ : Substitution) (fs : Continuations env) (arity : Nat) (body : Child raw) :
    Continuation env :=
  ⟨fun targetCtx targetInputs targetMode args => do
    if args.length != arity then none else do
      let bindings := closureSubstitution captureDepth targetCtx.length σ args
      let functions := closureFunctions fs args.length
      let parsed ← rec targetCtx targetInputs targetMode bindings functions body
      return ⟨bindings.apply body.val,parsed⟩⟩

/-- Ordinary local function values and aliases share the same captured scope.
This helper is used by both let binding and direct/local application. -/
def makeContinuation (rec : Recursor env raw) (captureDepth : Nat)
    (σ : Substitution) (fs : Continuations env) (value : Child raw) : Option (Continuation env) := do
  if let .bvar index := value.val then
    if let some cached := fs index then return cached
  let (types,body) ← continuationParts value
  return captureContinuation rec captureDepth σ fs types.length body

/-- Removing a function-valued lexical binder retains the source value in
its substitution and the captured callback in a separate function environment. -/
def letSubstitution (σ : Substitution) (value : Lean.Expr) : Substitution :=
  .bindings (fun | 0 => σ.apply value | n+1 => σ.reference n)

def letContinuations (fs : Continuations env) (value : Option (Continuation env)) : Continuations env :=
  fun | 0 => value | n+1 => fs n

/-- One common certificate operation for ordinary bodies, pure state values
and loop continuations. Traversal is separate from type checking. -/
def finishBody (env : VEnv) (conv : Conversion env) (exposure : Exposure env)
    (ctx : List VExpr) (p : Inputs) (mode : Mode) (source : Lean.Expr)
    (code : ClosedTerm) (proof : Lean.Expr) (known : KnownTypes env 0 := noKnownTypes env 0) :
    Option (Piece env ctx p source mode.expected) := do
  let h ← finish env conv exposure ctx (mode.expected p code source) code proof known
  return ⟨code.val,h,code.closed,code.represented⟩

/-- Administrative let/application changes the source of an existing
certificate, keeping its generated command and binding-aware traversal. -/
def retargetPiece (conv : Conversion env) (mode : Mode) (source : Lean.Expr)
    (parsed : Piece env ctx p previous mode.expected) :
    Option (Piece env ctx p source mode.expected) := do
  let checked ← parsed.checked.retarget conv (mode.expected p parsed.code source)
  return ⟨parsed.code,checked,parsed.closed,parsed.represented⟩


/-- Retained actuals add one administrative let per scalar argument. If the
ordinary conversion does not connect the certificate, traverse that prefix
with a bound derived from the actual argument count. Every result remains
a typed equality; this does not treat budget sufficiency as an assumption. -/
def retargetRetainedPiece (conv : Conversion env) (exposure : Exposure env)
    (argumentCount : Nat) (mode : Mode) (source : Lean.Expr)
    (parsed : Piece env ctx p previous mode.expected) :
    Option (Piece env ctx p source mode.expected) :=
  (retargetPiece conv mode source parsed).orElse fun _ =>
    retargetPiece (RetainedConversion.conversion conv exposure argumentCount) mode source parsed

theorem retargetRetainedPiece_of_retarget
    (parsed : Piece env ctx p previous mode.expected)
    (success : retargetPiece conv mode source parsed = some result) :
    retargetRetainedPiece conv exposure argumentCount mode source parsed = some result := by
  simp only [retargetRetainedPiece,success,Option.orElse_some]

/-- Use the same letValue code and proof constructor as an ordinary source
let. This operation adds no new command or evaluation semantics. -/
def bindArgument (env : VEnv) (conv : Conversion env) (exposure : Exposure env)
    (ctx : List VExpr) (p : Inputs) (mode : Mode) (annotation : WordBinder.Annotation) (value : Lean.Expr)
    (initial : Piece env ctx p value scalarExpected)
    (next : (source : Lean.Expr) × Piece env (annotation.core::ctx)
      {p.lift with locals := .bvar 0::p.lift.locals} source mode.expected) :
    Option ((source : Lean.Expr) × Piece env ctx p source mode.expected) := do
  let ⟨nextSource,next⟩ := next
  let source := Lean.Expr.letE `_argument annotation.native value nextSource false
  let code := ClosedTerm.app ``HybridWord.Cmd.letValue [initial.closedTerm,next.closedTerm]
  let fact := if mode == .step then ``WordLoopFacts.letValue else ``WordFrontendFacts.letValue
  let proof := app fact ([initial.code,next.code] ++ p.args ++
    [value,.lam `_argument annotation.native nextSource .default,initial.checked.proof,
      .lam `_argument annotation.native next.checked.proof .default])
  let result ← finishBody env conv exposure ctx p mode source code proof
    (initial.checked.known.orElse next.checked.known)
  return ⟨source,result⟩

/-- `do` elaboration passes a PUnit token to join-point continuations.
It is not a scalar runtime value and needs no IR local. Use its checked
source type rather than treating a failed scalar parse as permission to
substitute an arbitrary expression. -/
def unitArgument (env : VEnv) (conv : Conversion env) (exposure : Exposure env)
    (ctx : List VExpr) (value : Lean.Expr) : Bool :=
  ((do
    let core ← translate value
    let ty ← inferWith env conv 0 ctx core.val exposure (noKnownTypes env 0)
    if ty.val == VExpr.const ``PUnit [.succ .zero] then some () else none) : Option Unit).isSome

/-- Preserve a scalar actual's inferred BV32 spelling in its administrative
let. Word remains the default, including when inference cannot classify the
spelling, so this does not add a rejection condition to existing calls. -/
def argumentAnnotation (env : VEnv) (conv : Conversion env) (exposure : Exposure env)
    (ctx : List VExpr) (value : Lean.Expr) : WordBinder.Annotation :=
  let inferred := do
    let core ← translate value
    let ty ← inferWith env conv 0 ctx core.val exposure (noKnownTypes env 0)
    return ty.val
  if inferred == some Arithmetic.bitvecType then .bitvec else .word

/-- Bind scalar actual arguments before entering a helper. The continuation
receives references to retained values, so a later State update cannot turn
an argument into a read from an unavailable earlier State. State arguments
are aliases of the current State, not copies. Arguments are processed in
source order and the existing letValue certificate preserves failure. -/
def retainArguments (env : VEnv) (conv : Conversion env) (exposure : Exposure env)
    (continuation : Continuation env) (ctx : List VExpr) (p : Inputs) (mode : Mode)
    (args : List Lean.Expr) (saved : List Lean.Expr := []) :
    Option ((source : Lean.Expr) × Piece env ctx p source mode.expected) := do
  match args with
  | [] => continuation.apply ctx p mode saved
  | value::rest =>
    if sameTerm value p.s || unitArgument env conv exposure ctx value then
      retainArguments env conv exposure continuation ctx p mode rest (saved ++ [value])
    else do
      if mode == .value then none else do
        let initial ← ScalarEnvironment.parse env conv exposure ctx p value
        let annotation := argumentAnnotation env conv exposure ctx value
        let nextInputs := {p.lift with locals := .bvar 0::p.lift.locals}
        let ⟨nextSource,next⟩ ← retainArguments env conv exposure continuation (annotation.core::ctx) nextInputs mode
          (rest.map (LeanBindings.rename Nat.succ))
          ((saved.map (LeanBindings.rename Nat.succ)) ++ [.bvar 0])
        bindArgument env conv exposure ctx p mode annotation value initial ⟨nextSource,next⟩
termination_by args.length


def node (env : VEnv) (conv : Conversion env) (exposure : Exposure env)
    (raw : Lean.Expr)
    (rec : Recursor env raw)
    (ctx : List VExpr) (p : Inputs) (mode : Mode) (σ : Substitution) (fs : Continuations env) :
    Option (Piece env ctx p (Substitution.apply σ raw) mode.expected) := do
  let term := Substitution.apply σ
  let source := term raw
  let scalarCall := fun ctx p e => ScalarEnvironment.parse env conv exposure ctx p (term e)
  let readCall := fun ctx p e => readStep env conv exposure ctx p (ScalarEnvironment.parse env conv exposure ctx p) (term e)
  let bodyCall := fun ctx p => rec ctx p mode σ fs
  let underCall := fun ctx p => rec ctx p mode (under σ) (underFunctions fs)
  let fact (ordinary loop : Lean.Name) := if mode == .step then loop else ordinary
  let finishBody (code : ClosedTerm) (proof : Lean.Expr) (known : KnownTypes env 0 := noKnownTypes env 0) :=
    finishBody env conv exposure ctx p mode source code proof known
  if mode == .value then
    if sameTerm source p.s then
      return ← finishBody (.const ``HybridWord.Cmd.skip) (app ``WordFrontendFacts.skip p.args)
    if raw.getAppFn.constName? == some ``HybridWord.State.set then
      let [st,r,e] := raw.getAppArgs.toList | none
      if !sameTerm (term st) p.s then none else do
        let register ← closedTerm (term r)
        let value ← scalarCall ctx p e
        return ← finishBody (known := value.checked.known)
          (.app ``HybridWord.Cmd.assign [register,value.closedTerm])
          (app ``WordFrontendFacts.assign ([term r,value.code] ++ p.args ++ [term e,value.checked.proof]))
    none
  if let some ⟨binder,ty,value,nextBody⟩ := letParts raw then
    if sameTerm (term ty) state && sameTerm (term value) p.s then
      let tyCore ← translate (term ty)
      let p' := { p.lift with s := .bvar 0 }
      let b ← underCall (tyCore.val::ctx) p' nextBody
      return ← finishBody (known := b.checked.known) b.closedTerm
        (app (fact ``WordFrontendFacts.letStateAlias ``WordLoopFacts.letStateAlias) ([b.code] ++ p.args ++
          [.lam binder (term ty) (Substitution.apply (under σ) nextBody) .default,.lam binder (term ty) b.checked.proof .default]))
    if !sameTerm (term ty) state && compatible env conv ctx (term ty) word then
      let e ← scalarCall ctx p value
      let tyCore ← translate (term ty)
      let p' := { p.lift with locals := .bvar 0 :: p.lift.locals }
      let b ← underCall (tyCore.val::ctx) p' nextBody
      let next := Lean.Expr.lam binder (term ty) (Substitution.apply (under σ) nextBody) .default
      let proofNext := Lean.Expr.lam binder (term ty) b.checked.proof .default
      return ← finishBody (known := e.checked.known.orElse b.checked.known)
        (.app ``HybridWord.Cmd.letValue [e.closedTerm,b.closedTerm])
        (app (fact ``WordFrontendFacts.letValue ``WordLoopFacts.letValue) ([e.code,b.code] ++ p.args ++
          [term value,next,e.checked.proof,proofNext]))
    if compatible env conv ctx (term ty) state && !sameTerm (term value) p.s then
      let a ← rec ctx p .value σ fs value
      let tyCore ← translate (term ty)
      let p' := { p.lift with s := .bvar 0 }
      let b ← underCall (tyCore.val::ctx) p' nextBody
      let next := Lean.Expr.lam binder (term ty) (Substitution.apply (under σ) nextBody) .default
      let proofNext := Lean.Expr.lam binder (term ty) b.checked.proof .default
      return ← finishBody (known := a.checked.known.orElse b.checked.known) (.app ``HybridWord.Cmd.seq [a.closedTerm,b.closedTerm])
        (app (fact ``WordFrontendFacts.letState ``WordLoopFacts.letState) ([a.code,b.code] ++ p.args ++
          [term value,next,a.checked.proof,proofNext]))
  if let some parts := letParts raw then
    let continuation := makeContinuation rec ctx.length σ fs parts.value
    let nextSubst := letSubstitution σ parts.value
    let nextFunctions := letContinuations fs continuation
    let parsed ← rec ctx p mode nextSubst nextFunctions parts.body
    return ← retargetPiece conv mode source parsed
  if let some head := applicationHead raw then
    if let some continuation := makeContinuation rec ctx.length σ fs head then
      let ⟨_,parsed⟩ ← retainArguments env conv exposure continuation ctx p mode
        (raw.getAppArgs.toList.map term)
      return ← retargetRetainedPiece conv exposure raw.getAppArgs.size mode source parsed
  let args := ScalarEnvironment.arguments raw
  let head := raw.getAppFn.constName?
  match head with
  | some ``ite => do
    let [_ty,condition,d,yes,no] := args | none
    let v ← nonzeroValue condition
    let e ← scalarCall ctx p v
    let a ← bodyCall ctx p yes
    let b ← bodyCall ctx p no
    return ← finishBody (known := e.checked.known.orElse (a.checked.known.orElse b.checked.known))
      (.app ``HybridWord.Cmd.branch [e.closedTerm,a.closedTerm,b.closedTerm])
      (app (fact ``WordFrontendFacts.branch ``WordLoopFacts.branchCmd) ([e.code,a.code,b.code] ++ p.args ++
        [term v,term d,term yes,term no,e.checked.proof,a.checked.proof,b.checked.proof]))
  | some ``ForIn.forIn => do
    if mode != .body then none else do
      let range ← args[args.length-3]?
      let initial ← args[args.length-2]?
      let fn ← args.getLast?
      if sameTerm (term initial) p.s && range.val.getAppFn.constName? == some ``HybridWord.range then
        let [start,stop,stride] := range.val.getAppArgs.toList | none
        let startCode ← closedTerm (term start)
        let stopCode ← closedTerm (term stop)
        let strideCode ← closedTerm (term stride)
        do
          let some ⟨kn,kt,inner,ki⟩ := lambdaParts fn | none
          let some ⟨tn,st,fnBody,ti⟩ := lambdaParts inner | none
          if !compatible env conv ctx (term st) state || !compatible env conv ctx (term kt) word then none else do
            let stCore ← translate (term st)
            let ktCore ← translate (term kt)
            let ctx' := stCore.val::ktCore.val::ctx
            let p2 := p.lift.lift
            let p' := { p2 with s := .bvar 0,locals := .bvar 1::p2.locals }
            let b ← rec ctx' p' .step (under (under σ)) (underFunctions (underFunctions fs)) fnBody
            let proofNext := Lean.Expr.lam kn (term kt) (.lam tn (term st) b.checked.proof ti) ki
            return ← finishBody (known := b.checked.known)
              (.app ``HybridWord.Cmd.forStatic [startCode,stopCode,strideCode,b.closedTerm])
              (app ``WordLoopFacts.forStatic ([term start,term stop,term stride,b.code] ++ p.args ++ [term fn,proofNext]))
      if !sameTerm (term initial) p.s || range.val.getAppFn.constName? != some ``List.range then none else do
        let [nNat] := range.val.getAppArgs.toList | none
        if nNat.getAppFn.constName? != some ``BitVec.toNat then none else do
          let [width,n] := nNat.getAppArgs.toList | none
          let count ← scalarCall ctx p n
          let some ⟨kn,kt,inner,ki⟩ := lambdaParts fn | none
          let some ⟨tn,st,fnBody,ti⟩ := lambdaParts inner | none
          if !compatible env conv ctx (term st) state || !sameTerm (term kt) (.const ``Nat []) then none else do
            let stCore ← translate (term st)
            let ktCore ← translate (term kt)
            let ctx' := stCore.val::ktCore.val::ctx
            let p2 := p.lift.lift
            let index := app ``BitVec.ofNat [LeanBindings.rename (· + 2) (term width),.bvar 1]
            let p' := { p2 with s := .bvar 0,locals := index::p2.locals }
            let b ← rec ctx' p' .step (under (under σ)) (underFunctions (underFunctions fs)) fnBody
            let proofNext := Lean.Expr.lam kn (term kt) (.lam tn (term st) b.checked.proof ti) ki
            return ← finishBody (known := count.checked.known.orElse (b.checked.known))
              (.app ``HybridWord.Cmd.forRange [count.closedTerm,b.closedTerm])
              (app ``WordLoopFacts.forIn ([count.code,b.code] ++ p.args ++ [term n,term fn,count.checked.proof,proofNext]))
  | some ``List.foldlM => do
    if mode != .body then none else do
      let fn ← args[args.length-3]?
      let initial ← args[args.length-2]?
      let range ← args.getLast?
      if !sameTerm (term initial) p.s || range.val.getAppFn.constName? != some ``List.range then none else do
        let [nNat] := range.val.getAppArgs.toList | none
        if nNat.getAppFn.constName? != some ``BitVec.toNat then none else do
          let [width,n] := nNat.getAppArgs.toList | none
          let count ← scalarCall ctx p n
          let some ⟨tn,st,inner,ti⟩ := lambdaParts fn | none
          let some ⟨kn,kt,fnBody,ki⟩ := lambdaParts inner | none
          if !compatible env conv ctx (term st) state || !sameTerm (term kt) (.const ``Nat []) then none else do
            let stCore ← translate (term st)
            let ktCore ← translate (term kt)
            let p2 := p.lift.lift
            let index := app ``BitVec.ofNat [LeanBindings.rename (· + 2) (term width),.bvar 0]
            let p' := { p2 with s := .bvar 1,locals := index::p2.locals }
            let b ← rec (ktCore.val::stCore.val::ctx) p' mode (under (under σ)) (underFunctions (underFunctions fs)) fnBody
            let proofNext := Lean.Expr.lam tn (term st) (.lam kn (term kt) b.checked.proof ki) ti
            return ← finishBody (known := count.checked.known.orElse b.checked.known)
              (.app ``HybridWord.Cmd.forRange [count.closedTerm,b.closedTerm])
              (app ``WordFrontendFacts.forRange ([count.code,b.code] ++ p.args ++ [term n,term fn,count.checked.proof,proofNext]))
  | some ``HybridWord.State.copy => do
    if mode != .body then none else do
      let [st,destination,origin,count] := args | none
      if !sameTerm (term st) p.s then none else do
        let destinationCode ← closedTerm (term destination)
        let originCode ← closedTerm (term origin)
        let countCode ← closedTerm (term count)
        return ← finishBody (.app ``HybridWord.Cmd.copy [destinationCode,originCode,countCode])
          (app ``WordFrontendFacts.copy ([term destination,term origin,term count] ++ p.args))
  | some ``HybridWord.State.write => do
    if mode != .body then none else do
      let [st,a,j,e] := args | none
      if !sameTerm (term st) p.s then none else do
        let arrayCode ← closedTerm (term a)
        let ja ← scalarCall ctx p j
        let ea ← scalarCall ctx p e
        return ← finishBody (known := ja.checked.known.orElse ea.checked.known)
          (.app ``HybridWord.Cmd.store [arrayCode,ja.closedTerm,ea.closedTerm])
          (app ``WordFrontendFacts.store ([term a,ja.code,ea.code] ++ p.args ++ [term j,term e,ja.checked.proof,ea.checked.proof]))
  | some ``Pure.pure | some ``Option.some => do
    let value ← args.getLast?
    if mode == .step then
      if value.val.getAppFn.constName? != some ``ForInStep.yield then none else do
        let original ← (arguments value).getLast?
        let parsed ← rec ctx p .value σ fs original
        return ← finishBody (known := parsed.checked.known) parsed.closedTerm
          (app ``WordLoopFacts.compose [evalCmd p parsed.code,someExpr state (term original),source,
            parsed.checked.proof,app ``WordLoopFacts.someYield [term original]])
    else
      let surface := head == some ``Pure.pure
      if sameTerm (term value) p.s then
        return ← finishBody (.const ``HybridWord.Cmd.skip)
          (app (if surface then ``WordFrontendFacts.skipPure else ``WordFrontendFacts.skip) p.args)
      if value.val.getAppFn.constName? == some ``HybridWord.State.set then
        let [st,r,e] := value.val.getAppArgs.toList | none
        if !sameTerm (term st) p.s then none else do
          let registerCode ← closedTerm (term r)
          let ea ← scalarCall ctx p e
          return ← finishBody (known := ea.checked.known)
            (.app ``HybridWord.Cmd.assign [registerCode,ea.closedTerm])
            (app (if surface then ``WordFrontendFacts.assignPure else ``WordFrontendFacts.assign)
              ([term r,ea.code] ++ p.args ++ [term e,ea.checked.proof]))
      none
  | some ``Bind.bind => do
    let first ← args[args.length-2]?
    let next ← args.getLast?
    let some ⟨binder,ty,nextBody,info⟩ := lambdaParts next | none
    let tyCore ← translate (term ty)
    if sameTerm (term ty) (.const ``PUnit [.succ .zero]) then
      let b ← underCall (tyCore.val::ctx) p.lift nextBody
      let proofNext := Lean.Expr.lam binder (term ty) b.checked.proof info
      return ← finishBody (known := b.checked.known) b.closedTerm
        (app (fact ``WordFrontendFacts.unitSequence ``WordLoopFacts.unitSequence)
          ([b.code] ++ p.args ++ [term next,proofNext]))
    -- An exact State binder is the state continuation. Do not ask the
    -- general alias converter whether it might instead be a Word binder.
    if !sameTerm (term ty) state && compatible env conv ctx (term ty) word then
      let value ← readCall ctx p first
      let p' := { p.lift with locals := .bvar 0 :: p.lift.locals }
      let b ← underCall (tyCore.val::ctx) p' nextBody
      let proofNext := Lean.Expr.lam binder (term ty) b.checked.proof info
      let code := ClosedTerm.app ``HybridWord.Cmd.letValue [value.closedTerm,b.closedTerm]
      let proof := app (fact ``WordFrontendFacts.bindValue ``WordLoopFacts.bindValue)
        ([value.code,b.code] ++ p.args ++ [term first,term next,value.checked.proof,proofNext])
      if mode != .value && !sameTerm (term ty) word then
        let canonical := Lean.mkApp2 (bindHead word (if mode == .step then stepType else state)) (term first) (term next)
        let parsed ← StructuralBody.finishBody env conv exposure ctx p mode canonical code proof
          (value.checked.known.orElse b.checked.known)
        return ← retargetPiece conv mode source parsed
      return ← finishBody (known := value.checked.known.orElse b.checked.known) code proof
    if compatible env conv ctx (term ty) state then
      let a ← rec ctx p .body σ fs first
      let p' := { p.lift with s := .bvar 0 }
      let b ← underCall (tyCore.val::ctx) p' nextBody
      let proofNext := Lean.Expr.lam binder (term ty) b.checked.proof info
      return ← finishBody (known := a.checked.known.orElse b.checked.known) (.app ``HybridWord.Cmd.seq [a.closedTerm,b.closedTerm])
        (app (fact ``WordFrontendFacts.sequence ``WordLoopFacts.sequence)
          ([a.code,b.code] ++ p.args ++ [term first,term next,a.checked.proof,proofNext]))
    none
  | _ => none

/-- Every recursive call carries a proof that its input is a strict child
of the original expression. This is neither a parser budget nor a dynamic
size check; all witnesses are erased in executable code. -/
def visit (env : VEnv) (conv : Conversion env) (exposure : Exposure env)
    (source : Lean.Expr) (ctx : List VExpr) (p : Inputs) (mode : Mode)
    (σ : Substitution) (fs : Continuations env) :
    Option (Piece env ctx p (Substitution.apply σ source) mode.expected) :=
  node env conv exposure source (fun nextCtx nextInputs nextMode substitution functions child =>
    visit env conv exposure child.val nextCtx nextInputs nextMode substitution functions )
    ctx p mode σ fs 
termination_by syntaxSize source

/-- The ordinary entry uses the single structural traversal. Helper calls
always retain scalar argument values before traversing their bodies. -/
abbrev visitRetained (env : VEnv) (conv : Conversion env) (exposure : Exposure env)
    (source : Lean.Expr) (ctx : List VExpr) (p : Inputs) (mode : Mode)
    (σ : Substitution) (fs : Continuations env) :
    Option (Piece env ctx p (Substitution.apply σ source) mode.expected) :=
  visit env conv exposure source ctx p mode σ fs


def bodyRetained (env : VEnv) (conv : Conversion env) (exposure : Exposure env)
    (ctx : List VExpr) (p : Inputs) (source : Lean.Expr) :
    Option (Piece env ctx p source bodyExpected) :=
  visit env conv exposure source ctx p .body .identity (fun _ => none)

def compileRetained (native : Lean.Environment) (name : Lean.Name) : Option (Result native name) :=
  compileWith bodyRetained native name


end IRComparison.WordFrontend.StructuralBody
