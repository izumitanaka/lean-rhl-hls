import IRComparison.Frontend.WordAnnotatedStepRead

/-! Named-source certificate construction preserves the generated code.
Used to carry source-derived static conditions to the executable backend. -/
namespace IRComparison.WordFrontend
open Lean4Lean LeanTypeInference LeanTyped

/-- Certificate construction and retargeting retain the command term. These
facts connect source-derived declaration checks without inspecting proof terms. -/
theorem StructuralBody.finishBody_code
    (success : StructuralBody.finishBody env conv exposure ctx p mode source code proof known = some piece) :
    piece.code = code.val := by
  unfold StructuralBody.finishBody at success
  cases h : finish env conv exposure ctx (mode.expected p code source) code proof known with
  | none => simp [h] at success
  | some certificate => simp only [h,bind,Option.bind,pure,Option.pure_def,Option.some.injEq] at success; cases success; rfl

theorem StructuralBody.retargetPiece_code
    {parsed : Piece env ctx p previous mode.expected}
    (success : StructuralBody.retargetPiece conv mode source parsed = some piece) :
    piece.code = parsed.code := by
  unfold StructuralBody.retargetPiece at success
  cases h : parsed.checked.retarget conv (mode.expected p parsed.code source) with
  | none => simp [h] at success
  | some certificate => simp only [h,bind,Option.bind,pure,Option.pure_def,Option.some.injEq] at success; cases success; rfl

/-- The named-source wrapper changes only the proof, not the generated code.
The parsing premise is compositional: source completeness derives it before
this lemma is used, and it is not an input condition of the totality theorem. -/
theorem compileWith_code_of_body
    (parseBody : (env : VEnv) → Conversion env → Exposure env →
      (ctx : List VExpr) → (p : Inputs) → (source : Lean.Expr) →
      Option (Piece env ctx p source bodyExpected))
    (loaded : load native name = some lib)
    (shape : LeanSourceEntry.strip lib.source.declaration.value =
      .lam ni word (.lam nx word (.lam ny word (.lam ns state original bs) byInfo) bx) bi)
    (parsed : parseBody lib.model lib.conversion lib.exposure context parameters original = some piece)
    (success : compileWith parseBody native name = some result) : result.code = piece.code := by
  simp only [compileWith,loaded,bind,Option.bind,shape,closeLambda] at success
  split at success
  · contradiction
  · simp only [parsed] at success
    repeat first
      | (solve | contradiction)
      | (dsimp only [pure,Option.pure_def] at success; split at success)
      | split at success
    all_goals cases success <;> rfl

end IRComparison.WordFrontend
