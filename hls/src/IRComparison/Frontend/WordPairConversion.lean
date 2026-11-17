import IRComparison.Frontend.WordStepConversion

/-! The fixed two-binder certificate transport used by natural-count loops.
Source nesting is handled by the syntax induction; this conversion only
accounts for abstracting and applying the two iterator arguments. -/
namespace IRComparison.WordFrontend.Certificate.Pair
open Lean4Lean LeanTyped LeanTypeInference
open Arithmetic (SourceCasts continuation2Value continuation2Value_ne)

set_option maxHeartbeats 1500000

def actual (first second ty lhs rhs : VExpr) : VExpr :=
  .forallE first (.forallE second (equalValues ty lhs rhs))

def required (first second ty lhs rhs : VExpr) : VExpr :=
  actual first second ty lhs (continuation2Value first second rhs)

def prefixEq (ty lhs : VExpr) : VExpr :=
  .app (.app (.const ``Eq [.succ .zero]) ty) lhs

theorem prefix_typed
    (eqDeclared : env.constants ``Eq = some eqSignature)
    (tyTyped : DirectTyping env 0 ctx ty (.sort (.succ .zero)))
    (tyClosed : ty.ClosedN 0)
    (lhsTyped : CastTyping env 0 (SourceCasts env) ctx lhs ty) :
    CastTyping env 0 (SourceCasts env) ctx (prefixEq ty lhs)
      (.forallE ty (.sort .zero)) := by
  have eqTyped : CastTyping env 0 (SourceCasts env) ctx (.const ``Eq [.succ .zero])
      (.forallE (.sort (.succ .zero)) (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)))) :=
    .constant eqDeclared (by simp [VLevel.WF]) rfl
  have first := CastTyping.application eqTyped (tyTyped.withCasts _)
  simp only [VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,tyClosed.lift_eq] at first
  simpa only [prefixEq,VExpr.inst,tyClosed.instN_eq (Nat.zero_le _)] using
    CastTyping.application first lhsTyped

theorem equality_beta2_proved (setup : Arithmetic.AliasSetup env)
    (arithmetic : Arithmetic.Signatures env) (closed : ClosedConstantTypes env)
    (first second : Lean.Name)
    (secondDeclared : env.constants second = some ⟨0,.sort (.succ .zero)⟩)
    (tyTyped : DirectTyping env 0 (.const second []::.const first []::ctx) ty (.sort (.succ .zero)))
    (tyClosed : ty.ClosedN 0) (notSort : ∀ u, ty ≠ .sort u)
    (lhsTyped : CastTyping env 0 (SourceCasts env) (.const second []::.const first []::ctx) lhs ty)
    (rhsTyped : CastTyping env 0 (SourceCasts env) (.const second []::.const first []::ctx) rhs ty)
    (rhsForm : Arithmetic.ValueForm setup (.const second []::.const first []::ctx) rhs ty)
    (eqDeclared : env.constants ``Eq = some eqSignature)
    (eqFresh : ∀ r ∈ setup.rules, ``Eq ≠ r.name) (fuel : Nat) :
    ∃ equation, LeanStructuralConversion.prove env setup.basic setup.exposure 0 (fuel+6)
      (.const second []::.const first []::ctx)
      (equalValues ty lhs rhs)
      (equalValues ty lhs (continuation2Value (.const first []) (.const second []) rhs)) = some equation ∧
      equation.type = .sort .zero := by
  have prefixTyped := prefix_typed eqDeclared tyTyped tyClosed lhsTyped
  have prefixNone : setup.basic 0 (.const second []::.const first []::ctx)
      (prefixEq ty lhs) (prefixEq ty lhs) = none :=
    setup.basic_no_reduction _ _ rfl rfl eqFresh eqFresh rfl
  obtain ⟨fn,fnProved,fnType⟩ := LeanStructuralConversion.prove_reflexive_cast_complete
    prefixTyped prefixNone (setup.covers_source_recursive arithmetic closed fuel)
  have secondType : DirectTyping env 0 ctx (.const second []) (.sort (.succ .zero)) :=
    .constant secondDeclared (by simp) rfl
  obtain ⟨value,valueProved,valueType⟩ := setup.value_beta2_proved arithmetic closed
    (by trivial) (by trivial) secondType tyClosed notSort rhsTyped rhsForm fuel
  have wholeNone : setup.basic 0 (.const second []::.const first []::ctx)
      (equalValues ty lhs rhs)
      (equalValues ty lhs (continuation2Value (.const first []) (.const second []) rhs)) = none :=
    setup.basic_no_reduction _ _ rfl rfl eqFresh eqFresh rfl
  simpa only [VExpr.inst] using LeanStructuralConversion.prove_application_complete
    (leftName := ``Eq) (rightName := ``Eq) rfl rfl
    (fun same => continuation2Value_ne (.const first []) (.const second []) rhs (VExpr.app.inj same).2)
    wholeNone fn fnProved fnType value valueProved valueType

/-- Both iterator binders are accounted for in the existing fixed conversion
budget. The source body is never unfolded a number of times chosen by fuel. -/
theorem conversion (setup : Arithmetic.AliasSetup env)
    (arithmetic : Arithmetic.Signatures env) (closed : ClosedConstantTypes env)
    (first second : Lean.Name)
    (firstDeclared : env.constants first = some ⟨0,.sort (.succ .zero)⟩)
    (secondDeclared : env.constants second = some ⟨0,.sort (.succ .zero)⟩)
    (firstFresh : ∀ r ∈ setup.rules, first ≠ r.name)
    (secondFresh : ∀ r ∈ setup.rules, second ≠ r.name)
    (tyTyped : DirectTyping env 0 (.const second []::.const first []::ctx) ty (.sort (.succ .zero)))
    (tyClosed : ty.ClosedN 0) (notSort : ∀ u, ty ≠ .sort u)
    (lhsTyped : CastTyping env 0 (SourceCasts env) (.const second []::.const first []::ctx) lhs ty)
    (rhsTyped : CastTyping env 0 (SourceCasts env) (.const second []::.const first []::ctx) rhs ty)
    (rhsForm : Arithmetic.ValueForm setup (.const second []::.const first []::ctx) rhs ty)
    (eqDeclared : env.constants ``Eq = some eqSignature)
    (eqFresh : ∀ r ∈ setup.rules, ``Eq ≠ r.name) :
    ∃ result, setup.conversion 0 ctx
      (actual (.const first []) (.const second []) ty lhs rhs)
      (required (.const first []) (.const second []) ty lhs rhs) = some result := by
  obtain ⟨eq,eqProved,eqType⟩ := equality_beta2_proved setup arithmetic closed first second
    secondDeclared tyTyped tyClosed notSort lhsTyped rhsTyped rhsForm eqDeclared eqFresh 56
  have secondType : DirectTyping env 0 (.const first []::ctx) (.const second []) (.sort (.succ .zero)) :=
    .constant secondDeclared (by simp) rfl
  obtain ⟨secondEq,secondProved,secondKind⟩ := LeanStructuralConversion.prove_reflexive_complete
    secondType (setup.basic_no_reduction _ _ rfl rfl secondFresh secondFresh rfl) 61 setup.exposure
  have innerDifferent :
      VExpr.forallE (.const second []) (equalValues ty lhs rhs) ≠
      .forallE (.const second [])
        (equalValues ty lhs (continuation2Value (.const first []) (.const second []) rhs)) := by
    intro same
    exact continuation2Value_ne _ _ _ (VExpr.app.inj (VExpr.forallE.inj same).2).2
  obtain ⟨pointwise,pointwiseProved,pointwiseKind⟩ := LeanStructuralConversion.prove_forall_complete
    innerDifferent (by rfl) secondEq secondProved secondKind eq eqProved eqType
  have firstType : DirectTyping env 0 ctx (.const first []) (.sort (.succ .zero)) :=
    .constant firstDeclared (by simp) rfl
  obtain ⟨firstEq,firstProved,firstKind⟩ := LeanStructuralConversion.prove_reflexive_complete
    firstType (setup.basic_no_reduction _ _ rfl rfl firstFresh firstFresh rfl) 62 setup.exposure
  have outerDifferent : actual (.const first []) (.const second []) ty lhs rhs ≠
      required (.const first []) (.const second []) ty lhs rhs := by
    intro same
    exact innerDifferent (VExpr.forallE.inj same).2
  obtain ⟨equation,proved,kind⟩ := LeanStructuralConversion.prove_forall_complete
    outerDifferent (by rfl) firstEq firstProved firstKind pointwise pointwiseProved pointwiseKind
  exact LeanStructuralConversion.conversion_of_prove equation proved kind

end IRComparison.WordFrontend.Certificate.Pair
