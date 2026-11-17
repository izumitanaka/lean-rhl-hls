import IRComparison.Frontend.NativeBody
import NativeRHL.ExprAnalysis

namespace IRComparison.LeanScalar


/-- A total scalar native value. Only total expressions may be substituted
    for eager let bindings; partial array reads must not use this rule. -/
structure Binding where
  native : Int → Int → Int → State → Int
  code : NativeBody.ValueCode (fun i x y s => some (native i x y s))

abbrev Layout := List (Option Binding)

def environment (layout : Layout) (i x y : Int) (s : State) (index : Nat) : Int :=
  match layout[index]? with
  | some (some b) => b.native i x y s
  | _ => 0

theorem environment_cons (b : Binding) (layout : Layout) (i x y : Int) (s : State) :
    environment (some b :: layout) i x y s =
      NativeRHL.ExprAnalysis.bind (environment layout i x y s) (b.native i x y s) := by
  funext n
  cases n <;> rfl

structure Artifact (layout : Layout) (source : Lean.Expr) extends Binding where
  denotes : ∀ i x y s, NativeRHL.ExprAnalysis.Denotes source (environment layout i x y s) (native i x y s)

def constant (n : Int) : Binding := ⟨fun _ _ _ _ => n, NativeBody.literal n⟩

inductive Op where
  | add | sub | mul | div

def Op.surfaceHead : Op → Lean.Expr
  | .add => NativeRHL.ExprAnalysis.addHead
  | .sub => NativeRHL.ExprAnalysis.subHead
  | .mul => NativeRHL.ExprAnalysis.mulHead
  | .div => NativeRHL.ExprAnalysis.divHead

def Op.primitive : Op → Lean.Name
  | .add => ``Int.add
  | .sub => ``Int.sub
  | .mul => ``Int.mul
  | .div => ``Int.ediv

/-- Shared by code generation and the formal source bridge. The result records
    the exact standard instance, not merely the spelling of the operator. -/
def checkBinaryHead (head : Lean.Expr) : Option {op : Op // head = op.surfaceHead} := do
  if let some h := NativeRHL.ExprAnalysis.checkAddHead head then
    return ⟨.add, h.down⟩
  if let some h := NativeRHL.ExprAnalysis.checkSubHead head then
    return ⟨.sub, h.down⟩
  if let some h := NativeRHL.ExprAnalysis.checkMulHead head then
    return ⟨.mul, h.down⟩
  if let some h := NativeRHL.ExprAnalysis.checkDivHead head then
    return ⟨.div, h.down⟩
  none

def meaning : Op → Int → Int → Int
  | .add => Int.add
  | .sub => Int.sub
  | .mul => Int.mul
  | .div => Int.ediv

def binary (op : Op) (a b : Binding) : Binding where
  native := fun i x y s => meaning op (a.native i x y s) (b.native i x y s)
  code := by
    cases op
    · exact NativeBody.add a.code b.code
    · exact NativeBody.sub a.code b.code
    · exact NativeBody.mul a.code b.code
    · exact NativeBody.divide a.code b.code

private def combine (op : Op) (a : Artifact layout left) (b : Artifact layout right)
    (rule : ∀ env x y, NativeRHL.ExprAnalysis.Denotes left env x → NativeRHL.ExprAnalysis.Denotes right env y →
      NativeRHL.ExprAnalysis.Denotes source env (meaning op x y)) : Artifact layout source :=
  { binary op a.toBinding b.toBinding with
    denotes := fun i x y s => rule _ _ _ (a.denotes i x y s) (b.denotes i x y s) }

private def literal (n : Int) (rule : ∀ env, NativeRHL.ExprAnalysis.Denotes source env n) : Artifact layout source :=
  { constant n with denotes := fun i x y s => rule (environment layout i x y s) }

def surfaceBinary (op : Op) (a : Artifact layout left) (b : Artifact layout right) :
    Artifact layout (.app (.app op.surfaceHead left) right) :=
  combine op a b (by
    intro env x y ha hb
    cases op
    · exact .surfaceAdd ha hb
    · exact .surfaceSub ha hb
    · exact .surfaceMul ha hb
    · exact .surfaceDiv ha hb)

private def negative (a : Artifact layout arg)
    (rule : ∀ env v, NativeRHL.ExprAnalysis.Denotes arg env v → NativeRHL.ExprAnalysis.Denotes source env (-v)) : Artifact layout source where
  native := fun i x y s => -(a.native i x y s)
  code := {
    expr := .sub (.lit 0) a.code.expr
    correct := by intros; simp [Expr.eval, a.code.correct] }
  denotes := fun i x y s => rule _ _ (a.denotes i x y s)

private def conditional (c : Artifact layout test) (a : Artifact layout yes) (b : Artifact layout no) :
    Artifact layout (NativeRHL.ExprAnalysis.conditional test decision yes no) where
  native := fun i x y s => if c.native i x y s ≠ 0 then a.native i x y s else b.native i x y s
  code := {
    expr := .select c.code.expr a.code.expr b.code.expr
    correct := by
      intro i x y s
      by_cases h : c.native i x y s = 0 <;> simp [Expr.eval, c.code.correct, a.code.correct, b.code.correct, h] }
  denotes := fun i x y s => .branch (c.denotes i x y s) (a.denotes i x y s) (b.denotes i x y s)

/-- Pure recursive parsing of actual Lean.Expr. Evidence is constructed by
    the parser; it is not a semantic premise supplied for each input. -/
def compile (layout : Layout) : (source : Lean.Expr) → Option (Artifact layout source)
  | .bvar n =>
      match h : layout[n]? with
      | some (some b) => some { b with
          denotes := by intro i x y s; simpa [environment, h] using
            (NativeRHL.ExprAnalysis.Denotes.variable (env := environment layout i x y s) (index := n)) }
      | _ => none
  | .app (.const ``Int.ofNat []) (.lit (.natVal n)) =>
      some (literal (Int.ofNat n) (fun _ => .literal))
  | .app (.const ``Int.ofNat [])
      (.app (.app (.app (.const ``OfNat.ofNat [.zero]) (.const ``Nat [])) (.lit (.natVal n)))
        (.app (.const ``instOfNatNat []) (.lit (.natVal m)))) =>
      if same : n = m then
        some (literal (Int.ofNat n) (by intro env; subst m; exact .elaboratedLiteral))
      else none
  | .app (.app (.app (.const ``OfNat.ofNat [.zero]) (.const ``Int [])) (.lit (.natVal n)))
        (.app (.const ``instOfNat []) (.lit (.natVal m))) =>
      if same : n = m then
        some (literal (Int.ofNat n) (by intro env; subst m; exact .surfaceLiteral))
      else none
  | .app (.const ``Int.neg []) arg => do
      let a ← compile layout arg
      return negative a (fun _ _ h => .neg h)
  | .app (.app (.app (.const ``Neg.neg [.zero]) (.const ``Int [])) (.const ``Int.instNegInt [])) arg => do
      let a ← compile layout arg
      return negative a (fun _ _ h => .surfaceNeg h)
  | .app (.app (.const ``Int.add []) left) right => do
      let a ← compile layout left
      let b ← compile layout right
      return combine .add a b (fun _ _ _ ha hb => .add ha hb)
  | .app (.app (.const ``Int.sub []) left) right => do
      let a ← compile layout left
      let b ← compile layout right
      return combine .sub a b (fun _ _ _ ha hb => .sub ha hb)
  | .app (.app (.const ``Int.mul []) left) right => do
      let a ← compile layout left
      let b ← compile layout right
      return combine .mul a b (fun _ _ _ ha hb => .mul ha hb)
  | .app (.app (.const ``Int.ediv []) left) right => do
      let a ← compile layout left
      let b ← compile layout right
      return combine .div a b (fun _ _ _ ha hb => .div ha hb)
  | NativeRHL.ExprAnalysis.conditional test decision yes no => do
      let c ← compile layout test
      let a ← compile layout yes
      let b ← compile layout no
      return conditional c a b
  | .app (.app head left) right => do
      let a ← compile layout left
      let b ← compile layout right
      let ⟨op, same⟩ ← checkBinaryHead head
      return same ▸ surfaceBinary op a b
  | .letE name (.const ``Int []) value body nonDependent => do
      let a ← compile layout value
      let b ← compile (some a.toBinding :: layout) body
      return { b.toBinding with
        denotes := by
          intro i x y s
          apply NativeRHL.ExprAnalysis.Denotes.letValue (a.denotes i x y s)
          simpa only [environment_cons] using b.denotes i x y s }
  | .mdata data body => do
      let a ← compile layout body
      return { a.toBinding with denotes := fun i x y s => .metadata (a.denotes i x y s) }
  | _ => none

/-- Semantic boundary is explicit: this theorem uses the existing fragment
    relation, not an assertion that arbitrary named Lean functions were quoted faithfully. -/
theorem compile_surfaceBinary (op : Op)
    (ha : compile layout left = some a) (hb : compile layout right = some b) :
    compile layout (.app (.app op.surfaceHead left) right) = some (surfaceBinary op a b) := by
  cases op <;>
    simp [Op.surfaceHead, NativeRHL.ExprAnalysis.addHead, NativeRHL.ExprAnalysis.subHead,
      NativeRHL.ExprAnalysis.mulHead, NativeRHL.ExprAnalysis.divHead, compile, ha, hb,
      checkBinaryHead, NativeRHL.ExprAnalysis.checkAddHead, NativeRHL.ExprAnalysis.checkSubHead,
      NativeRHL.ExprAnalysis.checkMulHead, NativeRHL.ExprAnalysis.checkDivHead]

theorem compile_correct (layout : Layout) (source : Lean.Expr) (a : Artifact layout source)
    (_accepted : compile layout source = some a) (i x y : Int) (s : State) :
    NativeRHL.ExprAnalysis.Denotes source (environment layout i x y s) (a.native i x y s) ∧
    a.code.expr.eval i x y s = some (a.native i x y s) :=
  ⟨a.denotes i x y s, a.code.correct i x y s⟩

/-- The same parsed pure expression feeds both IRs directly. -/
def storeBody (a : Artifact layout source) (array : Nat) :
    NativeBody.Code (fun i x y s => s.write array i (a.native i x y s)) :=
  NativeBody.store array NativeBody.index a.code

def initialLayout : Layout := [
  some ⟨fun _ _ y _ => y, NativeBody.right⟩,
  some ⟨fun _ x _ _ => x, NativeBody.left⟩,
  some ⟨fun i _ _ _ => i, NativeBody.index⟩]

/-- A proof view of the exact input expression, not a new input AST. -/
inductive ThreeIntLambdas : Lean.Expr → Lean.Expr → Prop where
  | intro : ThreeIntLambdas
      (.lam a (.const ``Int []) (.lam b (.const ``Int [])
        (.lam c (.const ``Int []) body ci) bi) ai) body

structure FunctionArtifact (source : Lean.Expr) where
  body : Lean.Expr
  shape : ThreeIntLambdas source body
  scalar : Artifact initialLayout body

/-- Term-variable scope, including type annotations and decision arguments.
    This does not assert typing or validate constant declarations. -/
def wellScoped (depth : Nat) : Lean.Expr → Bool
  | .bvar n => n < depth
  | .fvar _ | .mvar _ => false
  | .app f a => wellScoped depth f && wellScoped depth a
  | .lam _ ty body _ | .forallE _ ty body _ =>
      wellScoped depth ty && wellScoped (depth+1) body
  | .letE _ ty value body _ =>
      wellScoped depth ty && wellScoped depth value && wellScoped (depth+1) body
  | .mdata _ body | .proj _ _ body => wellScoped depth body
  | _ => true

/-- Three Int binders, checked exactly. The result retains a proof that its
    body came from this actual source, including binder positions. -/
private def compileFunctionUnchecked : (source : Lean.Expr) → Option (FunctionArtifact source)
  | .lam _ (.const ``Int []) (.lam _ (.const ``Int [])
      (.lam _ (.const ``Int []) body _) _) _ => do
      let a ← compile initialLayout body
      return ⟨body,.intro,a⟩
  | _ => none

/-- Top-level definitions cannot contain unresolved term variables, even in
    proof arguments ignored by scalar evaluation. Typing is a separate boundary. -/
def compileFunction (source : Lean.Expr) : Option (FunctionArtifact source) :=
  if wellScoped 0 source then compileFunctionUnchecked source else none

theorem compileFunction_wellScoped (source : Lean.Expr) (result : FunctionArtifact source)
    (accepted : compileFunction source = some result) : wellScoped 0 source = true := by
  unfold compileFunction at accepted
  split at accepted
  · assumption
  · contradiction

theorem compileFunction_correct (source : Lean.Expr) (result : FunctionArtifact source)
    (_accepted : compileFunction source = some result) (i x y : Int) (s : State) :
    ThreeIntLambdas source result.body ∧
    NativeRHL.ExprAnalysis.Denotes result.body (environment initialLayout i x y s)
      (result.scalar.native i x y s) ∧
    result.scalar.code.expr.eval i x y s = some (result.scalar.native i x y s) :=
  ⟨result.shape, result.scalar.denotes i x y s, result.scalar.code.correct i x y s⟩

/-- A three-Int source cannot acquire a dependence on the target memory state. -/
theorem FunctionArtifact.state_independent (result : FunctionArtifact source)
    (i x y : Int) (s t : State) :
    result.scalar.native i x y s = result.scalar.native i x y t := by
  have same : environment initialLayout i x y s = environment initialLayout i x y t := by
    funext n
    match n with
    | 0 | 1 | 2 | _+3 => rfl
  exact NativeRHL.ExprAnalysis.denotes_unique (result.scalar.denotes i x y s)
    (same ▸ result.scalar.denotes i x y t)

/-- Both full optimization paths now consume the result of the actual parser.
    The right-hand side deliberately names the parsed native function, not an
    unrelated caller-provided named function. Closing that quotation boundary
    is a separate, still outstanding, general proof. -/
theorem FunctionArtifact.imperative_correct (result : FunctionArtifact source)
    (input : Input) (start stride : Int) (count : Nat) (l r : Int) (s : State) :
    (NativeBody.compileImperative (storeBody result.scalar 0) start stride count l r).eval input s =
      NativeLoop.run (NativeLoop.readBody input
        (fun i x y s => s.write 0 i (result.scalar.native i x y s)) l r) start stride count s :=
  NativeBody.compileImperative_correct (storeBody result.scalar 0) input start stride count l r s

theorem FunctionArtifact.functional_correct (result : FunctionArtifact source)
    (input : Input) (start stride : Int) (count : Nat) (l r : Int) (s : State) :
    (NativeBody.compileFunctional (storeBody result.scalar 0) start stride count l r).eval input s =
      NativeLoop.run (NativeLoop.readBody input
        (fun i x y s => s.write 0 i (result.scalar.native i x y s)) l r) start stride count s :=
  NativeBody.compileFunctional_correct (storeBody result.scalar 0) input start stride count l r s

end IRComparison.LeanScalar
