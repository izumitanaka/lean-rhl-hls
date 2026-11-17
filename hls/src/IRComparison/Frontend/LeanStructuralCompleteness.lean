import IRComparison.Frontend.LeanReductionCompleteness
import IRComparison.Frontend.LeanStructuralConversion
import IRComparison.Frontend.LeanCastTyping

namespace IRComparison.LeanStructuralConversion
open Lean4Lean LeanTypeInference
variable {env : VEnv} {base : Conversion env} {exposure : Exposure env}
  {U : Nat} {ctx : List VExpr}

theorem prove_base_complete
    (accepted : base U ctx a b = some result) (fuel : Nat) (exposure : Exposure env) :
    ∃ equation, prove env base exposure U (fuel+1) ctx a b = some equation ∧
      equation.type = .sort result.val := by
  rw [prove]
  simp only [accepted,bind,Option.bind]
  exact ⟨_,rfl,rfl⟩

/-- The recursive conversion callback used inside one step of `prove`. -/
def recursiveConversion (env : VEnv) (base : Conversion env) (exposure : Exposure env)
    (fuel : Nat) : Conversion env := withSearch base (fun levels context left right =>
      prove env base exposure levels fuel context left right)

theorem recursive_covers_base (coverage : Conversion.Covers base U casts)
    (fuel : Nat) (exposure : Exposure env) :
    Conversion.Covers (recursiveConversion env base exposure fuel) U casts := by
  intro ctx actual expected cast
  obtain ⟨result,accepted⟩ := coverage ctx actual expected cast
  simp only [recursiveConversion,withSearch,accepted,bind,Option.bind]
  exact ⟨_,rfl⟩

theorem prove_reflexive_cast_complete
    (typed : CastTyping env U casts ctx e ty)
    (notAlias : base U ctx e e = none)
    (coverage : Conversion.Covers (recursiveConversion env base exposure fuel) U casts) :
    ∃ equation, prove env base exposure U (fuel+1) ctx e e = some equation ∧
      equation.type = ty := by
  obtain ⟨⟨actual,h⟩,inferred,same⟩ := typed.infer_complete
    (known := noKnownTypes env U) (by intro _ _ _ h; cases h) coverage exposure
  dsimp only at same
  subst actual
  refine ⟨⟨ty,h⟩,?_,rfl⟩
  rw [prove]
  simp only [notAlias,bind,Option.bind,pure,Option.pure_def,dif_pos rfl,dite_true]
  change (inferWith env (recursiveConversion env base exposure fuel) U ctx e exposure >>= fun t =>
    some (⟨t.val,t.property⟩ : Equation env U ctx e e)) = _
  rw [inferred]
  rfl

theorem prove_reflexive_complete
    (typed : DirectTyping env U ctx e ty)
    (notAlias : base U ctx e e = none) (fuel : Nat) (exposure : Exposure env) :
    ∃ equation, prove env base exposure U (fuel+1) ctx e e = some equation ∧
      equation.type = ty :=
  prove_reflexive_cast_complete (typed.withCasts (fun _ _ _ => False)) notAlias
    (fun _ _ _ h => False.elim h)

/-- A typed one-step computation on the expected side is enough. This also
covers applications that reduce several successive lambda binders in one
weak-head step, as in the native two-argument `for` continuation. -/
theorem prove_reduction_right_complete_types
    (right : LeanTypeReduction.Result env U ctx b)
    (rightStep : LeanTypeReduction.step [] (recursiveConversion env base exposure fuel) U ctx exposure b = some right)
    (rightTarget : right.val.1 = a) (rightType : right.val.2 = ty)
    (leftKind : ∀ result, LeanTypeReduction.step []
      (recursiveConversion env base exposure fuel) U ctx exposure a = some result → result.val.2 = leftType)
    (different : a ≠ b) (notAlias : base U ctx a b = none) :
    ∃ equation, prove env base exposure U (fuel+1) ctx a b = some equation ∧ (equation.type = leftType ∨ equation.type = ty) := by
  rcases right with ⟨⟨term,kind⟩,proof⟩
  dsimp only at rightTarget rightType
  subst term; subst kind
  cases left : LeanTypeReduction.step [] (recursiveConversion env base exposure fuel) U ctx exposure a with
  | none =>
    refine ⟨⟨ty,proof.symm⟩,?_,Or.inr rfl⟩
    rw [prove]
    simp only [notAlias,bind,Option.bind,pure,Option.pure_def,dif_neg different]
    unfold recursiveConversion at left rightStep
    rw [left]
    simp only
    rw [rightStep]
    simp only [dif_pos rfl,dite_true]
  | some first =>
    have kind := leftKind first left
    by_cases exactStep : first.val.1 = b
    · refine ⟨⟨first.val.2,exactStep ▸ first.property⟩,?_,Or.inl kind⟩
      rw [prove]
      simp only [notAlias,bind,Option.bind,pure,Option.pure_def,dif_neg different]
      unfold recursiveConversion at left
      rw [left]
      simp only [dif_pos exactStep,dite_true]
    · refine ⟨⟨ty,proof.symm⟩,?_,Or.inr rfl⟩
      rw [prove]
      simp only [notAlias,bind,Option.bind,pure,Option.pure_def,dif_neg different]
      unfold recursiveConversion at left rightStep
      rw [left]
      simp only [dif_neg exactStep]
      rw [rightStep]
      simp only [dif_pos rfl,dite_true]

theorem prove_reduction_right_complete
    (right : LeanTypeReduction.Result env U ctx b)
    (rightStep : LeanTypeReduction.step [] (recursiveConversion env base exposure fuel) U ctx exposure b = some right)
    (rightTarget : right.val.1 = a) (rightType : right.val.2 = ty)
    (leftKind : ∀ result, LeanTypeReduction.step []
      (recursiveConversion env base exposure fuel) U ctx exposure a = some result → result.val.2 = ty)
    (different : a ≠ b) (notAlias : base U ctx a b = none) :
    ∃ equation, prove env base exposure U (fuel+1) ctx a b = some equation ∧ equation.type = ty := by
  obtain ⟨equation,success,kind⟩ := prove_reduction_right_complete_types
    right rightStep rightTarget rightType leftKind different notAlias
  exact ⟨equation,success,kind.elim id id⟩

/-- Single-beta specialization; source size does not consume search fuel. -/
theorem prove_beta_right_checked_complete
    (bodyTyped : CastTyping env U casts (domain :: ctx) body resultType)
    (argTyped : CheckedTyping env U casts ctx arg domain)
    (coverage : Conversion.Covers (recursiveConversion env base exposure fuel) U casts)
    (leftKind : ∀ result, LeanTypeReduction.step []
      (recursiveConversion env base exposure fuel) U ctx exposure (body.inst arg) = some result →
      result.val.2 = resultType.inst arg)
    (different : body.inst arg ≠ .app (.lam domain body) arg)
    (notAlias : base U ctx (body.inst arg) (.app (.lam domain body) arg) = none) :
    ∃ equation, prove env base exposure U (fuel+1) ctx
      (body.inst arg) (.app (.lam domain body) arg) = some equation ∧
      equation.type = resultType.inst arg := by
  obtain ⟨result,stepped,same⟩ := LeanTypeReduction.step_beta_checked_complete bodyTyped argTyped coverage [] exposure
  exact prove_reduction_right_complete result stepped (congrArg Prod.fst same) (congrArg Prod.snd same)
    leftKind different notAlias

theorem prove_beta_right_cast_complete
    (bodyTyped : CastTyping env U casts (domain :: ctx) body resultType)
    (argTyped : CastTyping env U casts ctx arg domain)
    (coverage : Conversion.Covers (recursiveConversion env base exposure fuel) U casts)
    (leftKind : ∀ result, LeanTypeReduction.step []
      (recursiveConversion env base exposure fuel) U ctx exposure (body.inst arg) = some result →
      result.val.2 = resultType.inst arg)
    (different : body.inst arg ≠ .app (.lam domain body) arg)
    (notAlias : base U ctx (body.inst arg) (.app (.lam domain body) arg) = none) :
    ∃ equation, prove env base exposure U (fuel+1) ctx
      (body.inst arg) (.app (.lam domain body) arg) = some equation ∧
      equation.type = resultType.inst arg :=
  prove_beta_right_checked_complete bodyTyped (.exact argTyped) coverage leftKind different notAlias

/-- Quantifier congruence is the outer step of a continuation's pointwise
certificate. The child proof is under the actual binder, not a closed-body
assumption. -/
theorem prove_forall_complete
    (different : VExpr.forallE da ba ≠ .forallE db bb)
    (notAlias : base U ctx (.forallE da ba) (.forallE db bb) = none)
    (domain : Equation env U ctx da db)
    (domainProved : prove env base exposure U fuel ctx da db = some domain)
    (domainType : domain.type = .sort u)
    (body : Equation env U (da::ctx) ba bb)
    (bodyProved : prove env base exposure U fuel (da::ctx) ba bb = some body)
    (bodyType : body.type = .sort v) :
    ∃ result, prove env base exposure U (fuel+1) ctx (.forallE da ba) (.forallE db bb) = some result ∧
      result.type = .sort (.imax u v) := by
  rcases domain with ⟨dt,hd⟩
  rcases body with ⟨bt,hb⟩
  dsimp only at domainType bodyType
  subst dt; subst bt
  rw [prove]
  simp only [notAlias,bind,Option.bind,pure,Option.pure_def,dif_neg different,
    LeanTypeReduction.step,domainProved,bodyProved]
  exact ⟨_,rfl,rfl⟩

/-- Typed congruence below a constant head. The subderivations compose at a
budget one larger than theirs; no bound on source-program depth is added. -/
theorem prove_application_complete
    (leftHead : LeanTypeReduction.constantHead fa = some (leftName,leftLevels))
    (rightHead : LeanTypeReduction.constantHead fb = some (rightName,rightLevels))
    (different : VExpr.app fa xa ≠ .app fb xb)
    (notAlias : base U ctx (.app fa xa) (.app fb xb) = none)
    (function : Equation env U ctx fa fb)
    (functionProved : prove env base exposure U fuel ctx fa fb = some function)
    (functionType : function.type = .forallE domain codomain)
    (argument : Equation env U ctx xa xb)
    (argumentProved : prove env base exposure U fuel ctx xa xb = some argument)
    (argumentType : argument.type = domain) :
    ∃ result, prove env base exposure U (fuel+1) ctx (.app fa xa) (.app fb xb) = some result ∧
      result.type = codomain.inst xa := by
  have leftStopped (c : Conversion env) :=
    LeanTypeReduction.step_constantHead_missing (U := U) (ctx := ctx) (.app fa xa) leftHead []
      (by simp) c exposure
  have rightStopped (c : Conversion env) :=
    LeanTypeReduction.step_constantHead_missing (U := U) (ctx := ctx) (.app fb xb) rightHead []
      (by simp) c exposure
  rcases function with ⟨functionTy,functionProof⟩
  rcases argument with ⟨argumentTy,argumentProof⟩
  dsimp only at functionType argumentType
  subst functionTy; subst argumentTy
  rw [prove]
  simp only [notAlias,bind,Option.bind,pure,Option.pure_def,dif_neg different,leftStopped,rightStopped,
    functionProved,argumentProved,dif_pos rfl]
  exact ⟨_,rfl,rfl⟩

/-- Application congruence also checks the argument's inferred alias type.
This is the existing converter branch used by a BitVec-annotated local passed
to an Option.some Word certificate. -/
theorem prove_application_cast_complete
    (leftHead : LeanTypeReduction.constantHead fa = some (leftName,leftLevels))
    (rightHead : LeanTypeReduction.constantHead fb = some (rightName,rightLevels))
    (different : VExpr.app fa xa ≠ .app fb xb)
    (notAlias : base U ctx (.app fa xa) (.app fb xb) = none)
    (function : Equation env U ctx fa fb)
    (functionProved : prove env base exposure U fuel ctx fa fb = some function)
    (functionType : function.type = .forallE domain codomain)
    (argument : Equation env U ctx xa xb)
    (argumentProved : prove env base exposure U fuel ctx xa xb = some argument)
    (argumentCast : argument.type ≠ domain →
      ∃ cast, recursiveConversion env base exposure fuel U ctx argument.type domain = some cast) :
    ∃ result, prove env base exposure U (fuel+1) ctx (.app fa xa) (.app fb xb) = some result ∧
      result.type = codomain.inst xa := by
  by_cases same : argument.type = domain
  · exact prove_application_complete leftHead rightHead different notAlias
      function functionProved functionType argument argumentProved same
  · obtain ⟨cast,converted⟩ := argumentCast same
    have leftStopped (c : Conversion env) :=
      LeanTypeReduction.step_constantHead_missing (U := U) (ctx := ctx) (.app fa xa) leftHead []
        (by simp) c exposure
    have rightStopped (c : Conversion env) :=
      LeanTypeReduction.step_constantHead_missing (U := U) (ctx := ctx) (.app fb xb) rightHead []
        (by simp) c exposure
    rcases function with ⟨functionTy,functionProof⟩
    dsimp only at functionType
    subst functionTy
    rw [prove]
    simp only [notAlias,bind,Option.bind,pure,Option.pure_def,dif_neg different,leftStopped,rightStopped,
      functionProved,argumentProved,dif_neg same]
    change ∃ result, (recursiveConversion env base exposure fuel U ctx argument.type domain >>= _) = some result ∧ _
    rw [converted]
    exact ⟨_,rfl,rfl⟩

/-- Application congruence including coincident applications. The typing
premise is independent of search; the same budget covers inference in the
reflexive branch and conversions in the non-reflexive branch. -/
theorem prove_application_or_same_complete
    (leftHead : LeanTypeReduction.constantHead fa = some (leftName,leftLevels))
    (rightHead : LeanTypeReduction.constantHead fb = some (rightName,rightLevels))
    (notAlias : base U ctx (.app fa xa) (.app fb xb) = none)
    (typed : CastTyping env U casts ctx (.app fa xa) (codomain.inst xa))
    (coverage : Conversion.Covers (recursiveConversion env base exposure fuel) U casts)
    (function : Equation env U ctx fa fb)
    (functionProved : prove env base exposure U fuel ctx fa fb = some function)
    (functionType : function.type = .forallE domain codomain)
    (argument : Equation env U ctx xa xb)
    (argumentProved : prove env base exposure U fuel ctx xa xb = some argument)
    (argumentCast : argument.type = domain ∨ casts ctx argument.type domain) :
    ∃ result, prove env base exposure U (fuel+1) ctx (.app fa xa) (.app fb xb) = some result ∧
      result.type = codomain.inst xa := by
  by_cases same : VExpr.app fa xa = .app fb xb
  · rw [← same] at notAlias ⊢
    exact prove_reflexive_cast_complete typed notAlias coverage
  · apply prove_application_cast_complete leftHead rightHead same notAlias
      function functionProved functionType argument argumentProved
    intro different
    cases argumentCast with
    | inl h => exact False.elim (different h)
    | inr h => exact coverage _ _ _ h

/-- Equality congruence around a single beta computation. The shared eqHead
usually is `Eq (Option State) (Cmd.eval ...)`; its entire size is handled by
ordinary inference, not by recursively comparing all source commands. -/
theorem prove_beta_argument_complete
    (prefixTyped : CastTyping env U casts ctx eqHead
      (.forallE (resultType.inst arg) (.sort u)))
    (bodyTyped : CastTyping env U casts (domain::ctx) body resultType)
    (argTyped : CastTyping env U casts ctx arg domain)
    (coverage : Conversion.Covers (recursiveConversion env base exposure fuel) U casts)
    (prefixHead : LeanTypeReduction.constantHead eqHead = some (prefixName,prefixLevels))
    (leftKind : ∀ result, LeanTypeReduction.step []
      (recursiveConversion env base exposure fuel) U ctx exposure (body.inst arg) = some result →
      result.val.2 = resultType.inst arg)
    (different : body.inst arg ≠ .app (.lam domain body) arg)
    (prefixNotAlias : base U ctx eqHead eqHead = none)
    (valueNotAlias : base U ctx (body.inst arg) (.app (.lam domain body) arg) = none)
    (wholeNotAlias : base U ctx (.app eqHead (body.inst arg))
      (.app eqHead (.app (.lam domain body) arg)) = none) :
    ∃ equation, prove env base exposure U (fuel+2) ctx
      (.app eqHead (body.inst arg)) (.app eqHead (.app (.lam domain body) arg)) = some equation ∧
      equation.type = .sort u := by
  obtain ⟨fn,fnProved,fnType⟩ := prove_reflexive_cast_complete prefixTyped prefixNotAlias coverage
  obtain ⟨value,valueProved,valueType⟩ := prove_beta_right_cast_complete
    bodyTyped argTyped coverage leftKind different valueNotAlias
  exact prove_application_complete prefixHead prefixHead
    (fun same => different (VExpr.app.inj same).2) wholeNotAlias
    fn fnProved fnType value valueProved valueType

/-- Transport the complete dependent result, so both its expression indices
and the success equation change together. -/
theorem prove_left_congr (same : a = b)
    (complete : ∃ equation : Equation env U ctx a c,
      prove env base exposure U fuel ctx a c = some equation ∧ equation.type = ty) :
    ∃ equation : Equation env U ctx b c,
      prove env base exposure U fuel ctx b c = some equation ∧ equation.type = ty := by
  cases same
  exact complete

theorem conversion_base_complete
    (accepted : base U ctx a b = some result) (exposure : Exposure env) :
    ∃ converted, conversion env base exposure U ctx a b = some converted := by
  simp only [conversion,ordinary,accepted,bind,Option.bind,Option.orElse_some]
  exact ⟨_,rfl⟩

theorem recursive_conversion_of_prove
    (equation : Equation env U ctx a b)
    (proved : prove env base exposure U fuel ctx a b = some equation)
    (kind : equation.type = .sort u) :
    ∃ result, recursiveConversion env base exposure fuel U ctx a b = some result := by
  cases first : base U ctx a b with
  | some result =>
    simp only [recursiveConversion,withSearch,first,bind,Option.bind]
    exact ⟨_,rfl⟩
  | none =>
    rcases equation with ⟨ty,h⟩
    dsimp only at kind
    subst ty
    simp only [recursiveConversion,withSearch,first,proved,bind,Option.bind]
    exact ⟨_,rfl⟩

/-- Source-type conversion coverage remains available independently of the
administrative fallback, which uses it when checking its own binders. -/
theorem ordinary_of_prove
    (equation : Equation env U ctx a b)
    (proved : prove env base exposure U 64 ctx a b = some equation)
    (kind : equation.type = .sort u) :
    ∃ result, ordinary env base exposure U ctx a b = some result := by
  cases first : base U ctx a b with
  | some result => simp only [ordinary,first,bind,Option.bind]; exact ⟨_,rfl⟩
  | none =>
    rcases equation with ⟨ty,h⟩
    dsimp only at kind
    subst ty
    simp only [ordinary,first,proved,bind,Option.bind]
    exact ⟨_,rfl⟩

/-- A sort-valued structural derivation reaches the real public converter. -/
theorem conversion_of_prove
    (equation : Equation env U ctx a b)
    (proved : prove env base exposure U 64 ctx a b = some equation)
    (kind : equation.type = .sort u) :
    ∃ result, conversion env base exposure U ctx a b = some result := by
  cases first : base U ctx a b with
  | some result => exact conversion_base_complete first exposure
  | none =>
    rcases equation with ⟨ty,h⟩
    dsimp only at kind
    subst ty
    simp only [conversion,ordinary,first,proved,bind,Option.bind,Option.orElse_some]
    exact ⟨_,rfl⟩

end IRComparison.LeanStructuralConversion
