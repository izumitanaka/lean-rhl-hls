import IRComparison.Frontend.LeanTyped

namespace IRComparison.LeanArithmetic
open Lean4Lean LeanTyped

variable {env : VEnv} {U : Nat} {context : List VExpr}

def factName : LeanScalar.Op → Lean.Name
  | .add => ``Standard.add
  | .sub => ``Standard.sub
  | .mul => ``Standard.mul
  | .div => ``Standard.div

/-- A fixed library fact is linked to the very operator selected by the scalar
    compiler. A different theorem with a similar-looking name is insufficient. -/
structure OperatorFact (nativeEnv : Lean.Environment) (op : LeanScalar.Op) where
  view : BinaryFactView nativeEnv (factName op)
  leftMatches : view.left = op.surfaceHead
  rightMatches : view.right = .const op.primitive []

def checkSurface (op : LeanScalar.Op) (head : Lean.Expr) :
    Option (PLift (head = op.surfaceHead)) :=
  match op with
  | .add => NativeRHL.ExprAnalysis.checkAddHead head
  | .sub => NativeRHL.ExprAnalysis.checkSubHead head
  | .mul => NativeRHL.ExprAnalysis.checkMulHead head
  | .div => NativeRHL.ExprAnalysis.checkDivHead head

def checkPrimitive (op : LeanScalar.Op) :
    (head : Lean.Expr) → Option (PLift (head = .const op.primitive []))
  | .const name [] => if h : name = op.primitive then some ⟨by rw [h]⟩ else none
  | _ => none

def loadOperator (nativeEnv : Lean.Environment) (op : LeanScalar.Op) :
    Option (OperatorFact nativeEnv op) := do
  let view ← viewBinaryFact nativeEnv (factName op)
  let hl ← checkSurface op view.left
  let hr ← checkPrimitive op view.right
  return ⟨view, hl.down, hr.down⟩

theorem OperatorFact.left_represents (fact : OperatorFact nativeEnv op) :
    Represents op.surfaceHead fact.view.leftCore.val :=
  fact.leftMatches ▸ fact.view.leftCore.property

theorem OperatorFact.right_represents (fact : OperatorFact nativeEnv op) :
    Represents (.const op.primitive []) fact.view.rightCore.val :=
  fact.rightMatches ▸ fact.view.rightCore.property

theorem OperatorFact.right_exact (fact : OperatorFact nativeEnv op) :
    fact.view.rightCore.val = .const op.primitive [] := by
  exact fact.right_represents.unique (.constant rfl)

/-- Environment lookup is needed after all standard declarations have been
    imported; the fact need not have been the LAST declaration installed. -/
theorem OperatorFact.apply (fact : OperatorFact nativeEnv op)
    (registered : env.constants (factName op) = some fact.view.signature)
    (hx : env.HasType U context x intType) (hy : env.HasType U context y intType) :
    env.HasType U context (.app (.app (.const (factName op) []) x) y)
      (eqInt (.app (.app fact.view.leftCore.val x) y)
        (.app (.app (.const op.primitive []) x) y)) := by
  have proof := apply_binary_fact registered
    (fact.view.leftCore.property.closed 0 fact.view.leftScope)
    (fact.view.rightCore.property.closed 0 fact.view.rightScope)
    fact.view.leftCore.property.levelWF fact.view.rightCore.property.levelWF hx hy
  simpa only [fact.right_exact] using proof

/-- The binary branch's result, sharing the actual compiler's head recognition
    and code constructor. The formal equality here normalizes the operator;
    recursive child equalities and the evaluation bridge remain separate. -/
structure BinaryArtifact (nativeEnv : Lean.Environment) (layout : LeanScalar.Layout)
    (source : Lean.Expr) where
  op : LeanScalar.Op
  left : Lean.Expr
  right : Lean.Expr
  sourceShape : source = .app (.app op.surfaceHead left) right
  leftCode : LeanScalar.Artifact layout left
  rightCode : LeanScalar.Artifact layout right
  leftAccepted : LeanScalar.compile layout left = some leftCode
  rightAccepted : LeanScalar.compile layout right = some rightCode
  fact : OperatorFact nativeEnv op
  leftCore : {v : VExpr // Represents left v}
  rightCore : {v : VExpr // Represents right v}

def compileBinary (nativeEnv : Lean.Environment) (layout : LeanScalar.Layout) :
    (source : Lean.Expr) → Option (BinaryArtifact nativeEnv layout source)
  | .app (.app head left) right => do
      let ⟨op, same⟩ ← LeanScalar.checkBinaryHead head
      match hl : LeanScalar.compile layout left with
      | none => none
      | some leftCode =>
        match hr : LeanScalar.compile layout right with
        | none => none
        | some rightCode => do
          let fact ← loadOperator nativeEnv op
          let leftCore ← translate left
          let rightCore ← translate right
          return ⟨op, left, right, by rw [same], leftCode, rightCode, hl, hr, fact, leftCore, rightCore⟩
  | _ => none

def BinaryArtifact.code (a : BinaryArtifact nativeEnv layout source) :
    LeanScalar.Artifact layout source :=
  a.sourceShape ▸ LeanScalar.surfaceBinary a.op a.leftCode a.rightCode

/-- The certificate describes the original scalar compiler's result, not a
    second compiler that merely happens to agree on the examples. -/
theorem BinaryArtifact.same_compiler (a : BinaryArtifact nativeEnv layout source) :
    LeanScalar.compile layout source = some a.code := by
  cases a with
  | mk op left right shape lc rc hl hr fact leftCore rightCore =>
    cases shape
    exact LeanScalar.compile_surfaceBinary op hl hr

def BinaryArtifact.sourceCore (a : BinaryArtifact nativeEnv layout source) : VExpr :=
  .app (.app a.fact.view.leftCore.val a.leftCore.val) a.rightCore.val

def BinaryArtifact.normalizedCore (a : BinaryArtifact nativeEnv layout source) : VExpr :=
  .app (.app (.const a.op.primitive []) a.leftCore.val) a.rightCore.val

def BinaryArtifact.proofTerm (a : BinaryArtifact nativeEnv layout source) : VExpr :=
  .app (.app (.const (factName a.op) []) a.leftCore.val) a.rightCore.val

theorem BinaryArtifact.represents_source (a : BinaryArtifact nativeEnv layout source) :
    Represents source a.sourceCore := by
  apply Eq.mpr (congrArg (fun e => Represents e a.sourceCore) a.sourceShape)
  exact .app (.app a.fact.left_represents a.leftCore.property) a.rightCore.property

/-- General soundness of the operator normalization constructed by the parser.
    Neither a per-input proof check nor a supplied source/target equality. -/
theorem BinaryArtifact.normalization_correct (a : BinaryArtifact nativeEnv layout source)
    (registered : env.constants (factName a.op) = some a.fact.view.signature)
    (hx : env.HasType U context a.leftCore.val intType)
    (hy : env.HasType U context a.rightCore.val intType) :
    env.HasType U context a.proofTerm (eqInt a.sourceCore a.normalizedCore) :=
  a.fact.apply registered hx hy

theorem BinaryArtifact.code_value (a : BinaryArtifact nativeEnv layout source)
    (i x y : Int) (s : State) :
    a.code.code.expr.eval i x y s = some
      (LeanScalar.meaning a.op (a.leftCode.native i x y s) (a.rightCode.native i x y s)) := by
  have native : a.code.native i x y s =
      LeanScalar.meaning a.op (a.leftCode.native i x y s) (a.rightCode.native i x y s) := by
    cases a with
    | mk op left right shape lc rc hl hr fact leftCore rightCore =>
      cases shape
      rfl
  exact (a.code.code.correct i x y s).trans (congrArg some native)

theorem compileBinary_correct
    (a : BinaryArtifact nativeEnv layout source)
    (_accepted : compileBinary nativeEnv layout source = some a)
    (registered : env.constants (factName a.op) = some a.fact.view.signature)
    (hx : env.HasType U context a.leftCore.val intType)
    (hy : env.HasType U context a.rightCore.val intType) :
    LeanScalar.compile layout source = some a.code ∧
    Represents source a.sourceCore ∧
    env.HasType U context a.proofTerm (eqInt a.sourceCore a.normalizedCore) :=
  ⟨a.same_compiler, a.represents_source, a.normalization_correct registered hx hy⟩

end IRComparison.LeanArithmetic
