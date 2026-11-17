import IRComparison.Frontend.WordAnnotatedBinaryConversion

/-! The two ordinary type spellings of unary negation. Conversion compares
only the fixed header; its operand is typed once, independently of its size. -/
namespace IRComparison.WordFrontend.AnnotatedNeg
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic
set_option maxHeartbeats 1800000

def header (annotation : WordBinder.Annotation) : VExpr :=
  applications (.const ``Neg.neg [.zero]) [annotation.core,.app (.const ``BitVec.instNeg []) width]
def nativeHeader (annotation : WordBinder.Annotation) : Lean.Expr :=
  Lean.mkApp2 (.const ``Neg.neg [.zero]) annotation.native (app ``BitVec.instNeg [nativeWidth])
theorem represented (annotation : WordBinder.Annotation) : Represents (nativeHeader annotation) (header annotation) :=
  .app (.app (.constant rfl) annotation.represented) (.app (.constant rfl) width_represents)

theorem header_typed (library : Signatures env) (annotation : WordBinder.Annotation) :
    CastTyping env 0 (SourceCasts env) ctx (header annotation) (.forallE annotation.core annotation.core) := by
  cases annotation with
  | word => exact library.negHeader_typed.mono (fun _ _ _ h => .arithmetic h)
  | bitvec =>
    have method : DirectTyping env 0 ctx (.const ``Neg.neg [.zero])
        (.forallE (.sort (.succ .zero)) (.forallE (.app (.const ``Neg [.zero]) (.bvar 0))
          (.forallE (.bvar 1) (.bvar 2)))) :=
      .constant library.negMethod (by simp [VLevel.WF]) rfl
    have first := DirectTyping.application method library.bitvec_typed
    have bc : bitvecType.ClosedN 0 := WordSpelling.closed .bitvec
    simp only [VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,Nat.reduceAdd,VExpr.lift,VExpr.liftN,
      bc.liftN_eq (Nat.zero_le _)] at first
    have inst : DirectTyping env 0 ctx (.const ``BitVec.instNeg []) negInstanceSignature :=
      .constant library.negInstance (by simp) rfl
    have arg := DirectTyping.application inst library.width_typed
    simp only [negInstanceSignature,natType,VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ] at arg
    have result := DirectTyping.application first arg
    simpa only [header,applications,WordBinder.Annotation.core,VExpr.inst,bc.instN_eq (Nat.zero_le _)] using
      result.withCasts (SourceCasts env)

theorem value_typed (library : Signatures env) (annotation : WordBinder.Annotation)
    (value : CheckedTyping env 0 (SourceCasts env) ctx v wordType) :
    CheckedTyping env 0 (SourceCasts env) ctx (.app (header annotation) v) wordType := by
  apply annotation.result
  have result := CastTyping.checkedApplication (header_typed library annotation) (annotation.argument value)
  simpa only [annotation.closed.instN_eq (Nat.zero_le _)] using result

private theorem method_none (setup : AliasSetup env)
    (fresh : ∀ r ∈ setup.rules, ``Neg.neg ≠ r.name)
    (left : LeanTypeReduction.constantHead a = some (``Neg.neg,[.zero]))
    (right : LeanTypeReduction.constantHead b = some (``Neg.neg,[.zero])) :
    setup.basic 0 ctx a b = none :=
  setup.basic_values_none (ty := wordType) (.constant left fresh (by decide))
    (.constant right fresh (by decide)) (by intro u h; cases h)

theorem header_proved (setup : AliasSetup env) (library : Signatures env)
    (closed : ClosedConstantTypes env) (annotation : WordBinder.Annotation)
    (fresh : ∀ r ∈ setup.rules, ``Neg.neg ≠ r.name) (fuel : Nat) :
    ∃ result, LeanStructuralConversion.prove env setup.basic setup.exposure 0 (fuel+7) ctx
      negHeader (header annotation) = some result ∧ result.type = .forallE wordType wordType := by
  have method : DirectTyping env 0 ctx (.const ``Neg.neg [.zero])
      (.forallE (.sort (.succ .zero)) (.forallE (.app (.const ``Neg [.zero]) (.bvar 0))
        (.forallE (.bvar 1) (.bvar 2)))) :=
    .constant library.negMethod (by simp [VLevel.WF]) rfl
  obtain ⟨fn,hfn,tfn⟩ := LeanStructuralConversion.prove_reflexive_complete method
    (method_none setup fresh rfl rfl) (fuel+4) setup.exposure
  obtain ⟨ty,hty,tty⟩ := setup.spelling_proved library .word (AnnotatedBinary.spelling annotation) (fuel+4)
  have first := CastTyping.application (method.withCasts (SourceCasts env))
    ((WordBinder.Annotation.word.type_typed library).withCasts (SourceCasts env))
  obtain ⟨pref,hp,tp⟩ := LeanStructuralConversion.prove_application_or_same_complete
    (leftName := ``Neg.neg) (rightName := ``Neg.neg) rfl rfl (method_none setup fresh rfl rfl)
    first (setup.covers_source_recursive library closed (fuel+1)) fn hfn tfn ty hty (.inl tty)
  simp only [WordBinder.Annotation.core,wordType,VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,
    VExpr.instVar_lower,VExpr.lift,VExpr.liftN,liftVar,Nat.reduceLT,ite_false,ite_true,Nat.reduceAdd] at first tp
  have instanceTyped : DirectTyping env 0 ctx (.const ``BitVec.instNeg []) negInstanceSignature :=
    .constant library.negInstance (by simp) rfl
  have instanceValue := DirectTyping.application instanceTyped library.width_typed
  have instanceForm : ValueForm setup ctx (.const ``BitVec.instNeg []) negInstanceSignature :=
    .declaredConstant library.negInstance (by decide)
  have instanceNone := setup.basic_values_none (instanceForm.application (arg := width))
    (instanceForm.application (arg := width)) (by intro u h; cases h)
  obtain ⟨arg,ha,ta⟩ := LeanStructuralConversion.prove_reflexive_complete instanceValue instanceNone (fuel+5) setup.exposure
  have final : CastTyping env 0 (SourceCasts env) ctx negHeader (.forallE wordType wordType) :=
    library.negHeader_typed.mono (fun _ _ _ h => SourceCasts.arithmetic h)
  obtain ⟨result,done,kind⟩ := LeanStructuralConversion.prove_application_or_same_complete
    (leftName := ``Neg.neg) (rightName := ``Neg.neg) rfl rfl (method_none setup fresh rfl rfl)
    final (setup.covers_source_recursive library closed (fuel+2)) pref hp tp arg ha
    (.inr (by rw [ta]; simpa only [negInstanceSignature,natType,VExpr.inst,VExpr.instVar_zero] using
      (SourceCasts.arithmetic Casts.negInstance (env := env) (ctx := ctx))))
  exact ⟨result,done,kind⟩

theorem value_proved (setup : AliasSetup env) (library : Signatures env)
    (closed : ClosedConstantTypes env) (annotation operand : WordBinder.Annotation)
    (value : CastTyping env 0 (SourceCasts env) ctx v operand.core)
    (form : ValueForm setup ctx v operand.core)
    (fresh : ∀ r ∈ setup.rules, ``Neg.neg ≠ r.name) (fuel : Nat) :
    ∃ result, LeanStructuralConversion.prove env setup.basic setup.exposure 0 (fuel+8) ctx
      (.app negHeader v) (.app (header annotation) v) = some result ∧ result.type = wordType := by
  obtain ⟨fn,hf,tf⟩ := header_proved setup library closed annotation fresh fuel
  obtain ⟨arg,ha,ta⟩ := LeanStructuralConversion.prove_reflexive_cast_complete value
    (setup.basic_values_none form form (by cases operand <;> intro u h <;> cases h))
    (setup.covers_source_recursive library closed (fuel+2))
  have target := CastTyping.checkedApplication (library.negHeader_typed.mono (fun _ _ _ h => SourceCasts.arithmetic h))
    (operand.result value)
  have cast : arg.type = wordType ∨ SourceCasts env ctx arg.type wordType := by
    rw [ta]; cases operand
    · exact .inl rfl
    · exact .inr .bitvecValue
  obtain ⟨result,done,kind⟩ := LeanStructuralConversion.prove_application_or_same_complete
    (leftName := ``Neg.neg) (rightName := ``Neg.neg) rfl rfl (method_none setup fresh rfl rfl)
    target (setup.covers_source_recursive library closed (fuel+3)) fn hf tf arg ha cast
  exact ⟨result,done,kind⟩

end IRComparison.WordFrontend.AnnotatedNeg
