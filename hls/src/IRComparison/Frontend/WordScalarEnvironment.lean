import IRComparison.Frontend.WordLoadingCompleteness

/-! Scalar source traversal with lexical bindings. The recursion is on the
original Lean.Expr, never on its substituted/normalized result. Source terms
are instantiated only to state/check connection equalities. Each let value is
compiled once and its certificate is reused at references.

The cache is not a second source AST: it contains successful typed artifacts
for subexpressions of the original Lean term. Administrative function forms
are handled by the enclosing structural traversal. There is no fallback to
the archived fuel-driven parser. -/
namespace IRComparison.WordFrontend.ScalarEnvironment
open Lean4Lean LeanTyped LeanTypeInference

structure Binding (env : VEnv) (ctx : List VExpr) (p : Inputs) where
  source : Lean.Expr
  piece : Piece env ctx p source scalarExpected

abbrev Bindings (env : VEnv) (ctx : List VExpr) (p : Inputs) := List (Binding env ctx p)

/-- A free position outside the lexical environment still denotes a parameter
of the surrounding body context; it is not lost or treated as a fresh value. -/
def reference (bindings : Bindings env ctx p) (n : Nat) : Lean.Expr :=
  match bindings[n]? with
  | some bound => bound.source
  | none => .bvar (n - bindings.length)

def materialize (bindings : Bindings env ctx p) (source : Lean.Expr) : Lean.Expr :=
  match bindings with
  | [] => source
  | _::_ => LeanBindings.substitute (reference bindings) source

/-- A lexical reference reuses exactly its own binding. No search over
materialized expressions is needed, and unrelated expressions are not used as
substitutes for the selected variable. Retargeting still constructs evidence. -/
def lookup (conv : Conversion env) (raw : Lean.Expr) (bindings : Bindings env ctx p) :
    Option (Piece env ctx p (materialize bindings raw) scalarExpected) := do
  let .bvar n := raw | none
  let bound ← bindings[n]?
  let checked ← bound.piece.checked.retarget conv
    (scalarExpected p bound.piece.code (materialize bindings (.bvar n)))
  return ⟨bound.piece.code,checked,bound.piece.closed,bound.piece.represented⟩

@[simp] theorem lookup_empty (conv : Conversion env) (raw : Lean.Expr) :
    lookup (ctx := ctx) (p := p) conv raw [] = none := by
  cases raw <;> rfl

/-- Every requested recursive argument is an actual proper subexpression.
The witness is constructed by the application-spine traversal, not checked
against an arbitrary parser budget. -/
abbrev Child (source : Lean.Expr) := {e : Lean.Expr // syntaxSize e < syntaxSize source}

def arguments : (source : Lean.Expr) → List (Child source)
  | .app f a =>
    (arguments f).map (fun child => ⟨child.val,by
      have h := child.property
      simp only [syntaxSize]; omega⟩) ++
    [⟨a,by simp only [syntaxSize]; omega⟩]
  | _ => []

def below (outer : Child source) (inner : Child outer.val) : Child source :=
  ⟨inner.val,Nat.lt_trans inner.property outer.property⟩

def conditionValue (condition : Child source) : Option (Child source) := do
  if condition.val.getAppFn.constName? != some ``Eq then none else do
    let [_ty,test,_truth] := arguments condition.val | none
    if test.val.getAppFn.constName? != some ``bne then none else do
      let [_ty,_instance,v,z] := arguments test.val | none
      if z.val.getAppFn.constName? != some ``OfNat.ofNat then none else do
        let [_ty,zero,_instance] := arguments z.val | none
        match zero.val with
        | .lit (.natVal 0) => return below condition (below test v)
        | _ => none

/-- The shared certificate-producing leaf operation. Source transports only
change its type index; they do not rerun syntax traversal. -/
def finishScalar (env : VEnv) (conv : Conversion env) (exposure : Exposure env)
    (ctx : List VExpr) (p : Inputs) (source : Lean.Expr) (code : ClosedTerm)
    (proof : Lean.Expr) (known : KnownTypes env 0 := noKnownTypes env 0) :
    Option (Piece env ctx p source scalarExpected) := do
  let h ← finish env conv exposure ctx (scalarExpected p code source) code proof known
  return ⟨code.val,h,code.closed,code.represented⟩

def node (env : VEnv) (conv : Conversion env) (exposure : Exposure env)
    (ctx : List VExpr) (p : Inputs) (bindings : Bindings env ctx p)
    (raw : Lean.Expr)
    (rec : (child : Child raw) → Option (Piece env ctx p (materialize bindings child.val) scalarExpected)) : Option (Piece env ctx p (materialize bindings raw) scalarExpected) := do
  let source := materialize bindings raw
  let finishScalar (code : ClosedTerm) (proof : Lean.Expr) (known : KnownTypes env 0 := noKnownTypes env 0) :=
    finishScalar env conv exposure ctx p source code proof known
  for (v,ctor,fact) in [(p.i,``HybridWord.Expr.index,``WordFrontendFacts.index),
      (p.x,``HybridWord.Expr.left,``WordFrontendFacts.left),(p.y,``HybridWord.Expr.right,``WordFrontendFacts.right)] do
    if sameTerm source v then return ← finishScalar (.const ctor) (app fact p.args)
  for k in List.range p.locals.length do
    if (p.locals[k]?.map (sameTerm source)).getD false then
      return ← finishScalar (.app ``HybridWord.Expr.local [.bindingIndex k]) (← localFact p k p.locals)
  let args := arguments raw
  let head := raw.getAppFn.constName?
  if head == some ``ite then
    let [_ty,condition,d,yes,no] := args | none
    let v ← conditionValue condition
    let e ← rec v
    let a ← rec yes
    let b ← rec no
    return ← finishScalar (known := e.checked.known.orElse (a.checked.known.orElse b.checked.known))
      (.app ``HybridWord.Expr.select [e.closedTerm,a.closedTerm,b.closedTerm])
      (app ``WordFrontendFacts.select ([e.code,a.code,b.code] ++ p.args ++
        [materialize bindings v,materialize bindings d,materialize bindings yes,materialize bindings no,e.checked.proof,a.checked.proof,b.checked.proof]))
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
        (app fact ([a.code,b.code] ++ p.args ++ [materialize bindings u,materialize bindings v,a.checked.proof,b.checked.proof]))
  if head == some ``Neg.neg then
    let v ← args.getLast?
    let a ← rec v
    return ← finishScalar (known := a.checked.known) (.app ``HybridWord.Expr.neg [a.closedTerm])
      (app ``WordFrontendFacts.neg ([a.code] ++ p.args ++ [materialize bindings v,a.checked.proof]))
  if head == some ``HybridWord.State.regs then
    let [s,r] := args | none
    if sameTerm (materialize bindings s) p.s then
      let register ← closedTerm (materialize bindings r)
      return ← finishScalar (.app ``HybridWord.Expr.reg [register]) (app ``WordFrontendFacts.register (materialize bindings r::p.args))
  none

/-- Descent is measured on the original expression, including below a lexical
binder. Instantiated source terms are only used in equality certificates. No
fuel or runtime iteration count participates in this recursion. -/
def visit (env : VEnv) (conv : Conversion env) (exposure : Exposure env)
    (ctx : List VExpr) (p : Inputs) : (source : Lean.Expr) →
    (bindings : Bindings env ctx p) →
    Option (Piece env ctx p (materialize bindings source) scalarExpected)
  | .letE name ty value next flag, bindings => do
    let valuePiece ← visit env conv exposure ctx p value bindings
    let parsed ← visit env conv exposure ctx p next
      (⟨materialize bindings value,valuePiece⟩ :: bindings)
    let checked ← parsed.checked.retarget conv
      (scalarExpected p parsed.code (materialize bindings (.letE name ty value next flag)))
    return ⟨parsed.code,checked,parsed.closed,parsed.represented⟩
  | .app (.lam name ty next info) value, bindings => do
    let valuePiece ← visit env conv exposure ctx p value bindings
    let parsed ← visit env conv exposure ctx p next
      (⟨materialize bindings value,valuePiece⟩ :: bindings)
    let checked ← parsed.checked.retarget conv
      (scalarExpected p parsed.code (materialize bindings (.app (.lam name ty next info) value)))
    return ⟨parsed.code,checked,parsed.closed,parsed.represented⟩
  | raw, bindings =>
    match lookup conv raw bindings with
    | some result => some result
    | none => node env conv exposure ctx p bindings raw (fun child =>
        visit env conv exposure ctx p child.val bindings)
termination_by source _ => syntaxSize source
decreasing_by
  all_goals first
    | exact child.property
    | simp_all [syntaxSize] <;> omega

@[simp] theorem reference_nil (n : Nat) :
    reference ([] : Bindings env ctx p) n = .bvar n := by
  simp [reference]

@[simp] theorem materialize_nil (source : Lean.Expr) :
    materialize ([] : Bindings env ctx p) source = source := rfl

theorem materialize_eq_substitute (bindings : Bindings env ctx p) (source : Lean.Expr) :
    materialize bindings source = LeanBindings.substitute (reference bindings) source := by
  cases bindings with
  | nil =>
    simp only [materialize,show reference ([] : Bindings env ctx p) = Lean.Expr.bvar by
      funext n; exact reference_nil n,LeanBindings.substitute_id]
  | cons => rfl

def parse (env : VEnv) (conv : Conversion env) (exposure : Exposure env)
    (ctx : List VExpr) (p : Inputs) (source : Lean.Expr) :
    Option (Piece env ctx p source scalarExpected) :=
  visit env conv exposure ctx p source []

/-- Extending the lexical environment obeys ordinary de Bruijn lookup.
This covers shadowing and arbitrarily many older scalar bindings. -/
@[simp] theorem reference_cons_zero (bound : Binding env ctx p) (bindings : Bindings env ctx p) :
    reference (bound :: bindings) 0 = bound.source := rfl

@[simp] theorem reference_cons_succ (bound : Binding env ctx p) (bindings : Bindings env ctx p) (n : Nat) :
    reference (bound :: bindings) (n+1) = reference bindings n := by
  simp only [reference,List.getElem?_cons_succ,List.length_cons,Nat.add_sub_add_right]

/-- Materializing a lexical binder agrees with the already proved native
substitution, including under further binders. This is an equality of source
terms for certificates, not a recursive parser call on the substituted term. -/
theorem materialize_cons (bound : Binding env ctx p) (bindings : Bindings env ctx p)
    (body : Lean.Expr) :
    materialize (bound :: bindings) body =
      LeanBindings.instantiate bound.source
        (LeanBindings.substitute (LeanBindings.underSubst (reference bindings)) body) := by
  simp only [materialize_eq_substitute,LeanBindings.instantiate,LeanBindings.substitute_comp]
  congr 1
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    simp only [reference_cons_succ,LeanBindings.underSubst,
      LeanBindings.substitute_rename]
    exact (LeanBindings.substitute_id (reference bindings n)).symm

/-- Lexical expansion preserves the original application structure. -/
theorem materialize_app (bindings : Bindings env ctx p) (f a : Lean.Expr) :
    materialize bindings (.app f a) =
      .app (materialize bindings f) (materialize bindings a) := by
  cases bindings <;> rfl

end IRComparison.WordFrontend.ScalarEnvironment
