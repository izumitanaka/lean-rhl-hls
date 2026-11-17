import IRComparison.Frontend.WordAnnotatedNeg
import IRComparison.Frontend.WordAnnotatedLiteral

/-! Type-spelling conversions for ordinary Lean nonzero conditions.
The source operands and branches remain unchanged; only fixed elaboration
headers are compared. No parser success or source-size fuel is assumed. -/
namespace IRComparison.WordFrontend.AnnotatedCondition
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic
set_option maxHeartbeats 2400000
set_option linter.unusedSimpArgs false

def dictionary (annotation : WordBinder.Annotation) : VExpr :=
  applications (.const ``instBEqOfDecidableEq [.zero])
    [annotation.core,.app (.const ``instDecidableEqBitVec []) width]
def header (annotation : WordBinder.Annotation) : VExpr :=
  applications (.const ``bne [.zero]) [annotation.core,dictionary annotation]
def test (annotation : WordBinder.Annotation) (v : VExpr) : VExpr :=
  applications (header annotation) [v,AnnotatedLiteral.core annotation 0]

theorem dictionary_typed (library : Branch.BooleanLibrary env) (scalars : Signatures env)
    (annotation : WordBinder.Annotation) :
    CastTyping env 0 (SourceCasts env) ctx (dictionary annotation)
      (.app (.const ``BEq [.zero]) annotation.core) := by
  have instanceTyped : DirectTyping env 0 ctx (.const ``instDecidableEqBitVec []) Branch.bitvecDecisionSignature.type :=
    .constant library.bitvecInstance (by simp) rfl
  have argument := DirectTyping.application instanceTyped scalars.width_typed
  simp only [Branch.bitvecDecisionSignature,natType,VExpr.inst,VExpr.instVar_zero] at argument
  have method : DirectTyping env 0 ctx (.const ``instBEqOfDecidableEq [.zero])
      (.forallE (.sort (.succ .zero)) (.forallE (.app (.const ``DecidableEq [.succ .zero]) (.bvar 0))
        (.app (.const ``BEq [.zero]) (.bvar 1)))) :=
    .constant library.beqInstance (by simp [VLevel.WF]) rfl
  have first := CastTyping.application (method.withCasts (SourceCasts env))
    ((annotation.type_typed scalars).withCasts (SourceCasts env))
  simp only [VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower,
    annotation.closed.liftN_eq (Nat.zero_le _),VExpr.lift,VExpr.liftN,liftVar,Nat.reduceLT,ite_false,ite_true,Nat.reduceAdd] at first
  cases annotation with
  | word => exact .convertedApplication first (argument.withCasts _) (.decisionInstance library.decidableEq)
  | bitvec =>
    simpa only [dictionary,applications,VExpr.inst,(WordBinder.Annotation.closed .bitvec).instN_eq (Nat.zero_le _)] using
      CastTyping.application first (argument.withCasts (SourceCasts env))

theorem header_typed (library : Branch.BooleanLibrary env) (scalars : Signatures env)
    (annotation : WordBinder.Annotation) :
    CastTyping env 0 (SourceCasts env) ctx (header annotation)
      (.forallE annotation.core (.forallE annotation.core boolType)) := by
  have method : DirectTyping env 0 ctx (.const ``bne [.zero])
      (.forallE (.sort (.succ .zero)) (.forallE (.app (.const ``BEq [.zero]) (.bvar 0))
        (.forallE (.bvar 1) (.forallE (.bvar 2) boolType)))) :=
    .constant library.bneMethod (by simp [VLevel.WF]) rfl
  have first := CastTyping.application (method.withCasts (SourceCasts env))
    ((annotation.type_typed scalars).withCasts (SourceCasts env))
  simp only [boolType,VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower,
    annotation.closed.liftN_eq (Nat.zero_le _),VExpr.lift,VExpr.liftN,liftVar,Nat.reduceLT,ite_false,ite_true,Nat.reduceAdd] at first
  have result := CastTyping.application first (dictionary_typed library scalars annotation)
  simpa only [header,applications,boolType,VExpr.inst,annotation.closed.instN_eq (Nat.zero_le _)] using result

private theorem instance_form (library : Branch.BooleanLibrary env) (setup : AliasSetup env)
    (annotation : WordBinder.Annotation) :
    ValueForm setup ctx (dictionary annotation) (.app (.const ``BEq [.zero]) annotation.core) := by
  have fn : ValueForm setup ctx (.const ``instBEqOfDecidableEq [.zero])
      (.forallE (.sort (.succ .zero)) (.forallE (.app (.const ``DecidableEq [.succ .zero]) (.bvar 0))
        (.app (.const ``BEq [.zero]) (.bvar 1)))) :=
    .declaredConstant library.beqInstance (by decide)
  have first := fn.application (arg := annotation.core)
  simp only [VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower,
    annotation.closed.liftN_eq (Nat.zero_le _),VExpr.lift,VExpr.liftN,liftVar,Nat.reduceLT,ite_false,ite_true,Nat.reduceAdd] at first
  have result := first.application (arg := .app (.const ``instDecidableEqBitVec []) width)
  simpa only [dictionary,applications,VExpr.inst,annotation.closed.instN_eq (Nat.zero_le _)] using result

private theorem method_none (setup : AliasSetup env)
    (fresh : ∀ r ∈ setup.rules, ``bne ≠ r.name)
    (left : LeanTypeReduction.constantHead a = some (``bne,[.zero]))
    (right : LeanTypeReduction.constantHead b = some (``bne,[.zero])) :
    setup.basic 0 ctx a b = none :=
  setup.basic_values_none (ty := boolType) (.constant left fresh (by decide))
    (.constant right fresh (by decide)) (by intro u h; cases h)

theorem dictionary_proved (setup : AliasSetup env) (library : Branch.BooleanLibrary env) (scalars : Signatures env)
    (closed : ClosedConstantTypes env) (original annotation : WordBinder.Annotation) (fuel : Nat) :
    ∃ result, LeanStructuralConversion.prove env setup.basic setup.exposure 0 (fuel+7) ctx
      (dictionary original) (dictionary annotation) = some result ∧
      result.type = .app (.const ``BEq [.zero]) original.core := by
  have method : DirectTyping env 0 ctx (.const ``instBEqOfDecidableEq [.zero])
      (.forallE (.sort (.succ .zero)) (.forallE (.app (.const ``DecidableEq [.succ .zero]) (.bvar 0))
        (.app (.const ``BEq [.zero]) (.bvar 1)))) :=
    .constant library.beqInstance (by simp [VLevel.WF]) rfl
  have form : ValueForm setup ctx (.const ``instBEqOfDecidableEq [.zero])
      (.forallE (.sort (.succ .zero)) (.forallE (.app (.const ``DecidableEq [.succ .zero]) (.bvar 0))
        (.app (.const ``BEq [.zero]) (.bvar 1)))) :=
    .declaredConstant library.beqInstance (by decide)
  obtain ⟨fn,hf,tf⟩ := LeanStructuralConversion.prove_reflexive_complete method
    (setup.basic_values_none form form (by intro u h; cases h)) (fuel+4) setup.exposure
  obtain ⟨ty,ht,tt⟩ := setup.spelling_proved scalars (AnnotatedBinary.spelling original) (AnnotatedBinary.spelling annotation) (fuel+4)
  have first := CastTyping.application (method.withCasts (SourceCasts env))
    ((original.type_typed scalars).withCasts (SourceCasts env))
  have firstNone := setup.basic_values_none_of_types (form.application (arg := original.core))
    (form.application (arg := annotation.core)) (by intro u h; cases h) (by intro u h; cases h)
  obtain ⟨pref,hp,tp⟩ := LeanStructuralConversion.prove_application_or_same_complete
    (leftName := ``instBEqOfDecidableEq) (rightName := ``instBEqOfDecidableEq) rfl rfl firstNone
    first (setup.covers_source_recursive scalars closed (fuel+1)) fn hf tf ty ht (.inl tt)
  simp only [wordType,VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower,
    original.closed.liftN_eq (Nat.zero_le _),VExpr.lift,VExpr.liftN,liftVar,Nat.reduceLT,ite_false,ite_true,Nat.reduceAdd] at tp
  have instanceTyped : DirectTyping env 0 ctx (.const ``instDecidableEqBitVec []) Branch.bitvecDecisionSignature.type :=
    .constant library.bitvecInstance (by simp) rfl
  have argTyped := DirectTyping.application instanceTyped scalars.width_typed
  have argForm : ValueForm setup ctx (.const ``instDecidableEqBitVec []) Branch.bitvecDecisionSignature.type :=
    .declaredConstant library.bitvecInstance (by decide)
  obtain ⟨arg,ha,ta⟩ := LeanStructuralConversion.prove_reflexive_complete argTyped
    (setup.basic_values_none (argForm.application (arg := width)) (argForm.application (arg := width)) (by intro u h; cases h))
    (fuel+5) setup.exposure
  obtain ⟨result,done,kind⟩ := LeanStructuralConversion.prove_application_or_same_complete
    (leftName := ``instBEqOfDecidableEq) (rightName := ``instBEqOfDecidableEq) rfl rfl
    (setup.basic_values_none_of_types (instance_form library setup original) (instance_form library setup annotation)
      (by intro u h; cases h) (by intro u h; cases h))
    (by simpa only [VExpr.inst,original.closed.instN_eq (Nat.zero_le _)] using dictionary_typed library scalars original) (setup.covers_source_recursive scalars closed (fuel+2)) pref hp tp arg ha
    (by
      rw [ta]
      simp only [VExpr.inst,VExpr.instVar_zero]
      cases original with
      | word => exact .inr (.decisionInstance library.decidableEq)
      | bitvec => exact .inl rfl)
  exact ⟨result,done,by simpa only [VExpr.inst,original.closed.instN_eq (Nat.zero_le _),boolType] using kind⟩

theorem header_proved (setup : AliasSetup env) (library : Branch.BooleanLibrary env) (scalars : Signatures env)
    (closed : ClosedConstantTypes env) (original annotation : WordBinder.Annotation)
    (fresh : ∀ r ∈ setup.rules, ``bne ≠ r.name) (fuel : Nat) :
    ∃ result, LeanStructuralConversion.prove env setup.basic setup.exposure 0 (fuel+9) ctx
      (header original) (header annotation) = some result ∧
      result.type = .forallE original.core (.forallE original.core boolType) := by
  have method : DirectTyping env 0 ctx (.const ``bne [.zero])
      (.forallE (.sort (.succ .zero)) (.forallE (.app (.const ``BEq [.zero]) (.bvar 0))
        (.forallE (.bvar 1) (.forallE (.bvar 2) boolType)))) :=
    .constant library.bneMethod (by simp [VLevel.WF]) rfl
  obtain ⟨fn,hf,tf⟩ := LeanStructuralConversion.prove_reflexive_complete method
    (method_none setup fresh rfl rfl) (fuel+6) setup.exposure
  obtain ⟨ty,ht,tt⟩ := setup.spelling_proved scalars (AnnotatedBinary.spelling original) (AnnotatedBinary.spelling annotation) (fuel+6)
  have first := CastTyping.application (method.withCasts (SourceCasts env))
    ((original.type_typed scalars).withCasts (SourceCasts env))
  obtain ⟨pref,hp,tp⟩ := LeanStructuralConversion.prove_application_or_same_complete
    (leftName := ``bne) (rightName := ``bne) rfl rfl (method_none setup fresh rfl rfl)
    first (setup.covers_source_recursive scalars closed (fuel+3)) fn hf tf ty ht (.inl tt)
  simp only [boolType,wordType,VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower,
    original.closed.liftN_eq (Nat.zero_le _),VExpr.lift,VExpr.liftN,liftVar,Nat.reduceLT,ite_false,ite_true,Nat.reduceAdd] at tp
  obtain ⟨arg,ha,ta⟩ := dictionary_proved setup library scalars closed original annotation (fuel+1)
  obtain ⟨result,done,kind⟩ := LeanStructuralConversion.prove_application_or_same_complete
    (leftName := ``bne) (rightName := ``bne) rfl rfl (method_none setup fresh rfl rfl)
    (by simpa only [VExpr.inst,original.closed.instN_eq (Nat.zero_le _),boolType] using header_typed library scalars original) (setup.covers_source_recursive scalars closed (fuel+4)) pref hp tp arg ha (.inl ta)
  exact ⟨result,done,by simpa only [VExpr.inst,original.closed.instN_eq (Nat.zero_le _),boolType] using kind⟩



theorem literal_proved (setup : AliasSetup env) (scalars : Signatures env)
    (closed : ClosedConstantTypes env) (original annotation : WordBinder.Annotation)
    (freshLiteral : ∀ r ∈ setup.rules, ``OfNat.ofNat ≠ r.name) (n fuel : Nat) :
    ∃ result, LeanStructuralConversion.prove env setup.basic setup.exposure 0 (fuel+8) ctx
      (AnnotatedLiteral.core original n) (AnnotatedLiteral.core annotation n) = some result ∧ result.type = original.core := by
  have method : DirectTyping env 0 ctx (.const ``OfNat.ofNat [.zero])
      (.forallE (.sort (.succ .zero)) (.forallE natType
        (.forallE (applications (.const ``OfNat [.zero]) [.bvar 1,.bvar 0]) (.bvar 2)))) :=
    .constant scalars.ofNat (by simp [VLevel.WF]) rfl
  have noBase {a b : VExpr} (ha : LeanTypeReduction.constantHead a = some (``OfNat.ofNat,[.zero]))
      (hb : LeanTypeReduction.constantHead b = some (``OfNat.ofNat,[.zero])) : setup.basic 0 ctx a b = none :=
    setup.basic_values_none (ty := wordType) (.constant ha freshLiteral (by decide))
      (.constant hb freshLiteral (by decide)) (by intro u h; cases h)
  obtain ⟨fn,hf,tf⟩ := LeanStructuralConversion.prove_reflexive_complete method (noBase rfl rfl) (fuel+4) setup.exposure
  obtain ⟨ty,ht,tt⟩ := setup.spelling_proved scalars (AnnotatedBinary.spelling original) (AnnotatedBinary.spelling annotation) (fuel+4)
  have first := CastTyping.application (method.withCasts (SourceCasts env))
    ((original.type_typed scalars).withCasts (SourceCasts env))
  obtain ⟨f1,h1,t1⟩ := LeanStructuralConversion.prove_application_or_same_complete
    (leftName := ``OfNat.ofNat) (rightName := ``OfNat.ofNat) rfl rfl (noBase rfl rfl)
    first (setup.covers_source_recursive scalars closed (fuel+1)) fn hf tf ty ht (.inl tt)
  simp only [natType,applications,VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,
    VExpr.instVar_lower,original.closed.liftN_eq (Nat.zero_le _),VExpr.lift,VExpr.liftN,Nat.reduceAdd] at first t1
  have number := scalars.literals.numeral_typed (ctx := ctx) (U := 0) n
  have numForm : ValueForm setup ctx (numeral n) natType := by
    apply LeanTyped.numeral_induction (fun e => ValueForm setup ctx e natType)
    · exact .constant rfl (setup.irreducibleNumeral _ (by simp)) (by decide)
    · intro a _; exact .constant rfl (setup.irreducibleNumeral _ (by simp)) (by decide)
    · intro a _; exact .constant rfl (setup.irreducibleNumeral _ (by simp)) (by decide)
  obtain ⟨num,hn,tn⟩ := LeanStructuralConversion.prove_reflexive_complete number
    (setup.basic_values_none numForm numForm (by intro u h; cases h)) (fuel+5) setup.exposure
  have second := CastTyping.application first (number.withCasts (SourceCasts env))
  obtain ⟨f2,h2,t2⟩ := LeanStructuralConversion.prove_application_or_same_complete
    (leftName := ``OfNat.ofNat) (rightName := ``OfNat.ofNat) rfl rfl (noBase rfl rfl)
    second (setup.covers_source_recursive scalars closed (fuel+2)) f1 h1 t1 num hn (.inl tn)
  simp only [VExpr.inst,VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ,original.closed.instN_eq (Nat.zero_le _),original.closed.liftN_eq (Nat.zero_le _),wordType,VExpr.lift,VExpr.liftN] at t2
  have dictionary : DirectTyping env 0 ctx (.const ``BitVec.instOfNat []) bitvecOfNatSignature :=
    .constant scalars.bitvecOfNat (by simp) rfl
  have d1 := DirectTyping.application dictionary scalars.width_typed
  simp only [bitvecOfNatSignature,natType,applications,VExpr.inst,Nat.reduceAdd,
    VExpr.instVar_succ,VExpr.instVar_zero,VExpr.instVar_lower] at d1
  have d2 := DirectTyping.application d1 number
  have df : ValueForm setup ctx (.const ``BitVec.instOfNat []) bitvecOfNatSignature :=
    .declaredConstant scalars.bitvecOfNat (by decide)
  have dform := (df.application (arg := width)).application (arg := numeral n)
  obtain ⟨arg,ha,ta⟩ := LeanStructuralConversion.prove_reflexive_complete d2
    (setup.basic_values_none dform dform (by intro u h; cases h)) (fuel+6) setup.exposure
  obtain ⟨result,done,kind⟩ := LeanStructuralConversion.prove_application_or_same_complete
    (leftName := ``OfNat.ofNat) (rightName := ``OfNat.ofNat) rfl rfl (noBase rfl rfl)
    (by simpa only [original.closed.instN_eq (Nat.zero_le _)] using AnnotatedLiteral.annotation_typed scalars original n)
    (setup.covers_source_recursive scalars closed (fuel+3)) f2 h2 t2 arg ha
    (by
      rw [ta]
      simp only [VExpr.inst,VExpr.inst_lift,VExpr.instVar_zero]
      cases original with
      | word => exact .inr (.arithmetic (.literalInstance n))
      | bitvec => exact .inl rfl)
  exact ⟨result,done,by simpa only [original.closed.instN_eq (Nat.zero_le _)] using kind⟩

theorem test_typed (library : Branch.BooleanLibrary env) (scalars : Signatures env)
    (annotation : WordBinder.Annotation) (value : CheckedTyping env 0 (SourceCasts env) ctx v wordType) :
    CastTyping env 0 (SourceCasts env) ctx (test annotation v) boolType := by
  have first := CastTyping.checkedApplication (header_typed library scalars annotation) (annotation.argument value)
  simp only [VExpr.inst,annotation.closed.instN_eq (Nat.zero_le _),boolType] at first
  simpa only [test,applications,VExpr.inst,boolType] using CastTyping.checkedApplication first
    (annotation.argument (AnnotatedLiteral.typed scalars annotation 0))

theorem test_proved (setup : AliasSetup env) (library : Branch.BooleanLibrary env) (scalars : Signatures env)
    (closed : ClosedConstantTypes env) (original annotation operand : WordBinder.Annotation)
    (value : CastTyping env 0 (SourceCasts env) ctx v operand.core)
    (form : ValueForm setup ctx v operand.core)
    (fresh : ∀ r ∈ setup.rules, ``bne ≠ r.name)
    (freshLiteral : ∀ r ∈ setup.rules, ``OfNat.ofNat ≠ r.name) (fuel : Nat) :
    ∃ result, LeanStructuralConversion.prove env setup.basic setup.exposure 0 (fuel+11) ctx
      (test original v) (test annotation v) = some result ∧ result.type = boolType := by
  obtain ⟨fn,hf,tf⟩ := header_proved setup library scalars closed original annotation fresh fuel
  obtain ⟨arg,ha,ta⟩ := LeanStructuralConversion.prove_reflexive_cast_complete value
    (setup.basic_values_none form form (by cases operand <;> intro u h <;> cases h))
    (setup.covers_source_recursive scalars closed (fuel+4))
  have first := CastTyping.checkedApplication (header_typed library scalars original) (original.argument (operand.result value))
  have cast : arg.type = original.core ∨ SourceCasts env ctx arg.type original.core := by
    rw [ta]; cases original <;> cases operand
    · exact .inl rfl
    · exact .inr .bitvecValue
    · exact .inr .wordValue
    · exact .inl rfl
  obtain ⟨f1,h1,t1⟩ := LeanStructuralConversion.prove_application_or_same_complete
    (leftName := ``bne) (rightName := ``bne) rfl rfl (method_none setup fresh rfl rfl)
    (by simpa only [VExpr.inst,original.closed.instN_eq (Nat.zero_le _),boolType] using first) (setup.covers_source_recursive scalars closed (fuel+5)) fn hf tf arg ha cast
  simp only [VExpr.inst,original.closed.instN_eq (Nat.zero_le _),boolType] at t1
  obtain ⟨zero,hz,tz⟩ := literal_proved setup scalars closed original annotation freshLiteral 0 (fuel+2)
  obtain ⟨result,done,kind⟩ := LeanStructuralConversion.prove_application_or_same_complete
    (leftName := ``bne) (rightName := ``bne) rfl rfl (method_none setup fresh rfl rfl)
    (test_typed library scalars original (operand.result value))
    (setup.covers_source_recursive scalars closed (fuel+6)) f1 h1 t1 zero hz (.inl tz)
  exact ⟨result,done,kind⟩



def condition (annotation : WordBinder.Annotation) (v : VExpr) : VExpr :=
  equalValues boolType (test annotation v) (.const ``Bool.true [])
def decision (annotation : WordBinder.Annotation) (v : VExpr) : VExpr :=
  applications (.const ``instDecidableEqBool []) [test annotation v,.const ``Bool.true []]
def nativeHeader (annotation : WordBinder.Annotation) : Lean.Expr :=
  Lean.mkApp2 (.const ``bne [.zero]) annotation.native
    (Lean.mkApp2 (.const ``instBEqOfDecidableEq [.zero]) annotation.native
      (.app (.const ``instDecidableEqBitVec []) nativeWidth))
def nativeTest (annotation : WordBinder.Annotation) (v : Lean.Expr) : Lean.Expr :=
  Lean.mkApp2 (nativeHeader annotation) v (AnnotatedLiteral.native annotation 0)
def nativeCondition (annotation : WordBinder.Annotation) (v : Lean.Expr) : Lean.Expr :=
  Lean.mkApp3 (.const ``Eq [.succ .zero]) (.const ``Bool []) (nativeTest annotation v) (.const ``Bool.true [])
def nativeDecision (annotation : WordBinder.Annotation) (v : Lean.Expr) : Lean.Expr :=
  Lean.mkApp2 (.const ``instDecidableEqBool []) (nativeTest annotation v) (.const ``Bool.true [])

theorem test_represents (annotation : WordBinder.Annotation) (value : Represents v vc) :
    Represents (nativeTest annotation v) (test annotation vc) :=
  .app (.app (.app (.app (.constant rfl) annotation.represented)
    (.app (.app (.constant rfl) annotation.represented) (.app (.constant rfl) width_represents))) value)
    (AnnotatedLiteral.represented annotation 0)
theorem condition_represents (annotation : WordBinder.Annotation) (value : Represents v vc) :
    Represents (nativeCondition annotation v) (condition annotation vc) :=
  .app (.app (.app (.constant rfl) (.constant rfl)) (test_represents annotation value)) (.constant rfl)
theorem decision_represents (annotation : WordBinder.Annotation) (value : Represents v vc) :
    Represents (nativeDecision annotation v) (decision annotation vc) :=
  .app (.app (.constant rfl) (test_represents annotation value)) (.constant rfl)

theorem condition_typed (library : Branch.BooleanLibrary env) (scalars : Signatures env)
    (annotation : WordBinder.Annotation) (value : CheckedTyping env 0 (SourceCasts env) ctx v wordType) :
    CastTyping env 0 (SourceCasts env) ctx (condition annotation v) (.sort .zero) ∧
    CastTyping env 0 (SourceCasts env) ctx (decision annotation v)
      (.app (.const ``Decidable []) (condition annotation v)) := by
  have tested := test_typed library scalars annotation value
  have boolean : CastTyping env 0 (SourceCasts env) ctx boolType (.sort (.succ .zero)) :=
    .constant library.boolean (by simp) rfl
  have truth : CastTyping env 0 (SourceCasts env) ctx (.const ``Bool.true []) boolType :=
    .constant library.truth (by simp) rfl
  have equality : CastTyping env 0 (SourceCasts env) ctx (.const ``Eq [.succ .zero])
      (.forallE (.sort (.succ .zero)) (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)))) :=
    .constant library.equality (by simp [VLevel.WF]) rfl
  have e1 := CastTyping.application equality boolean
  simp only [boolType,VExpr.inst,VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ,
    VExpr.lift,VExpr.liftN,Nat.reduceAdd] at e1
  have e2 := CastTyping.application e1 tested
  simp only [VExpr.inst] at e2
  have proposition := CastTyping.application e2 truth
  have instanceType : CastTyping env 0 (SourceCasts env) ctx (.const ``instDecidableEqBool [])
      (.app (.const ``DecidableEq [.succ .zero]) boolType) :=
    .constant library.boolInstance (by simp) rfl
  have d1 := CastTyping.functionApplication instanceType rfl
    (SourceCasts.decisionFunction library.equality library.decidable library.boolean) tested
  simp only [decEqFunction,boolType,applications,VExpr.inst,VExpr.instVar_lower,
    VExpr.instVar_zero,VExpr.instVar_succ,VExpr.lift,VExpr.liftN,Nat.reduceAdd] at d1
  refine ⟨proposition,?_⟩
  simpa only [decision,condition,equalValues,applications,VExpr.inst,
    VExpr.inst_lift,VExpr.instVar_zero] using CastTyping.application d1 truth

theorem condition_proved (setup : AliasSetup env) (library : Branch.BooleanLibrary env) (scalars : Signatures env)
    (closed : ClosedConstantTypes env) (original annotation operand : WordBinder.Annotation)
    (value : CastTyping env 0 (SourceCasts env) ctx v operand.core)
    (form : ValueForm setup ctx v operand.core)
    (fresh : ∀ r ∈ setup.rules, ``bne ≠ r.name)
    (freshLiteral : ∀ r ∈ setup.rules, ``OfNat.ofNat ≠ r.name)
    (freshEq : ∀ r ∈ setup.rules, ``Eq ≠ r.name) (fuel : Nat) :
    ∃ result, LeanStructuralConversion.prove env setup.basic setup.exposure 0 (fuel+13) ctx
      (condition original v) (condition annotation v) = some result ∧ result.type = .sort .zero := by
  have equality : DirectTyping env 0 ctx (.const ``Eq [.succ .zero])
      (.forallE (.sort (.succ .zero)) (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)))) :=
    .constant library.equality (by simp [VLevel.WF]) rfl
  have boolean : DirectTyping env 0 ctx boolType (.sort (.succ .zero)) :=
    .constant library.boolean (by simp) rfl
  have pref := DirectTyping.application equality boolean
  simp only [boolType,VExpr.inst,VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ,
    VExpr.lift,VExpr.liftN,Nat.reduceAdd] at pref
  obtain ⟨fn,hf,tf⟩ := LeanStructuralConversion.prove_reflexive_complete pref
    (setup.basic_no_reduction _ _ rfl rfl freshEq freshEq rfl) (fuel+10) setup.exposure
  obtain ⟨arg,ha,ta⟩ := test_proved setup library scalars closed original annotation operand value form fresh freshLiteral fuel
  have first := CastTyping.application (pref.withCasts (SourceCasts env))
    (test_typed library scalars original (operand.result value))
  obtain ⟨f1,h1,t1⟩ := LeanStructuralConversion.prove_application_or_same_complete
    (leftName := ``Eq) (rightName := ``Eq) rfl rfl
    (setup.basic_no_reduction _ _ rfl rfl freshEq freshEq rfl)
    first (setup.covers_source_recursive scalars closed (fuel+7)) fn hf tf arg ha (.inl ta)
  simp only [VExpr.inst] at t1
  have truth : DirectTyping env 0 ctx (.const ``Bool.true []) boolType :=
    .constant library.truth (by simp) rfl
  have truthForm : ValueForm setup ctx (.const ``Bool.true []) boolType :=
    .declaredConstant library.truth (by decide)
  obtain ⟨arg2,h2,t2⟩ := LeanStructuralConversion.prove_reflexive_complete truth
    (setup.basic_values_none truthForm truthForm (by intro u h; cases h)) (fuel+11) setup.exposure
  obtain ⟨result,done,kind⟩ := LeanStructuralConversion.prove_application_or_same_complete
    (leftName := ``Eq) (rightName := ``Eq) rfl rfl
    (setup.basic_no_reduction _ _ rfl rfl freshEq freshEq rfl)
    (condition_typed library scalars original (operand.result value)).1
    (setup.covers_source_recursive scalars closed (fuel+8)) f1 h1 t1 arg2 h2 (.inl t2)
  exact ⟨result,done,kind⟩



theorem decidable_proved (setup : AliasSetup env) (library : Branch.BooleanLibrary env) (scalars : Signatures env)
    (closed : ClosedConstantTypes env) (original annotation operand : WordBinder.Annotation)
    (value : CastTyping env 0 (SourceCasts env) ctx v operand.core)
    (form : ValueForm setup ctx v operand.core)
    (fresh : ∀ r ∈ setup.rules, ``bne ≠ r.name)
    (freshLiteral : ∀ r ∈ setup.rules, ``OfNat.ofNat ≠ r.name)
    (freshEq : ∀ r ∈ setup.rules, ``Eq ≠ r.name)
    (freshDecision : ∀ r ∈ setup.rules, ``Decidable ≠ r.name) (fuel : Nat) :
    ∃ result, LeanStructuralConversion.prove env setup.basic setup.exposure 0 (fuel+14) ctx
      (.app (.const ``Decidable []) (condition original v))
      (.app (.const ``Decidable []) (condition annotation v)) = some result ∧ result.type = .sort (.succ .zero) := by
  have decl : DirectTyping env 0 ctx (.const ``Decidable []) (.forallE (.sort .zero) (.sort (.succ .zero))) :=
    .constant library.decidable (by simp) rfl
  obtain ⟨fn,hf,tf⟩ := LeanStructuralConversion.prove_reflexive_complete decl
    (setup.basic_no_reduction _ _ rfl rfl freshDecision freshDecision rfl) (fuel+12) setup.exposure
  obtain ⟨arg,ha,ta⟩ := condition_proved setup library scalars closed original annotation operand value form fresh freshLiteral freshEq fuel
  obtain ⟨result,done,kind⟩ := LeanStructuralConversion.prove_application_or_same_complete
    (leftName := ``Decidable) (rightName := ``Decidable) rfl rfl
    (setup.basic_no_reduction _ _ rfl rfl freshDecision freshDecision rfl)
    (CastTyping.application (decl.withCasts (SourceCasts env)) (condition_typed library scalars original (operand.result value)).1)
    (setup.covers_source_recursive scalars closed (fuel+9)) fn hf tf arg ha (.inl ta)
  exact ⟨result,done,kind⟩

/-- Only the predicate annotation changes. This is a type conversion, not an
assumption that the source expression or the HLS parser succeeds. -/
inductive Casts (setup : AliasSetup env) : TypeCasts where
  | source : SourceCasts env ctx a b → Casts setup ctx a b
  | decision (library : Branch.BooleanLibrary env) (original annotation operand : WordBinder.Annotation)
      (value : CastTyping env 0 (SourceCasts env) ctx v operand.core)
      (form : ValueForm setup ctx v operand.core)
      (fresh : ∀ r ∈ setup.rules, ``bne ≠ r.name)
      (freshLiteral : ∀ r ∈ setup.rules, ``OfNat.ofNat ≠ r.name)
      (freshEq : ∀ r ∈ setup.rules, ``Eq ≠ r.name)
      (freshDecision : ∀ r ∈ setup.rules, ``Decidable ≠ r.name) :
      Casts setup ctx (.app (.const ``Decidable []) (condition original v))
        (.app (.const ``Decidable []) (condition annotation v))

instance : Arithmetic.Includes (Casts setup) := ⟨fun _ _ _ h => .source (.arithmetic h)⟩

theorem Casts.covered (setup : AliasSetup env) (scalars : Signatures env)
    (closed : ClosedConstantTypes env) (fuel : Nat) : Conversion.Covers
      (LeanStructuralConversion.recursiveConversion env setup.basic setup.exposure (fuel+14)) 0 (Casts setup) := by
  intro ctx actual expected cast
  cases cast with
  | source h => exact setup.covers_source_recursive scalars closed (fuel+10) ctx actual expected h
  | decision library original annotation operand value form fresh freshLiteral freshEq freshDecision =>
    obtain ⟨eq,he,te⟩ := decidable_proved setup library scalars closed original annotation operand
      value form fresh freshLiteral freshEq freshDecision fuel
    exact LeanStructuralConversion.recursive_conversion_of_prove eq he te

def choice (ty : VExpr) (annotation : WordBinder.Annotation) (v d a b : VExpr) : VExpr :=
  Branch.iteValue ty (condition annotation v) d a b

theorem choice_with_prefix_proved (setup : AliasSetup env) (library : Branch.BooleanLibrary env) (scalars : Signatures env)
    (closed : ClosedConstantTypes env) (annotation operand : WordBinder.Annotation)
    (value : CastTyping env 0 (SourceCasts env) ctx v operand.core) (form : ValueForm setup ctx v operand.core)
    (valueType : DirectTyping env 0 ctx ty (.sort (.succ .zero))) (tyClosed : ty.ClosedN 0)
    (decisionTyped : CastTyping env 0 (SourceCasts env) ctx d (.app (.const ``Decidable []) (condition annotation v)))
    (decisionForm : ValueForm setup ctx d (.app (.const ``Decidable []) (condition annotation v)))
    (left : CastTyping env 0 (SourceCasts env) ctx a leftType) (right : CastTyping env 0 (SourceCasts env) ctx b rightType)
    (leftCast : leftType = ty ∨ SourceCasts env ctx leftType ty)
    (rightCast : rightType = ty ∨ SourceCasts env ctx rightType ty)
    (leftForm : ValueForm setup ctx a leftType) (rightForm : ValueForm setup ctx b rightType)
    (notSortLeft : ∀ u, leftType ≠ .sort u) (notSortRight : ∀ u, rightType ≠ .sort u)
    (iteDeclared : env.constants ``ite = some Branch.iteSignature)
    (fresh : ∀ r ∈ setup.rules, ``bne ≠ r.name)
    (freshLiteral : ∀ r ∈ setup.rules, ``OfNat.ofNat ≠ r.name)
    (freshEq : ∀ r ∈ setup.rules, ``Eq ≠ r.name)
    (freshDecision : ∀ r ∈ setup.rules, ``Decidable ≠ r.name)
    (freshIte : ∀ r ∈ setup.rules, ``ite ≠ r.name) (fuel : Nat)
    (fn : LeanStructuralConversion.Equation env 0 ctx
      (.app (.const ``ite [.succ .zero]) ty) (.app (.const ``ite [.succ .zero]) resultType))
    (hf : LeanStructuralConversion.prove env setup.basic setup.exposure 0 (fuel+15) ctx
      (.app (.const ``ite [.succ .zero]) ty) (.app (.const ``ite [.succ .zero]) resultType) = some fn)
    (tf : fn.type = .forallE (.sort .zero) (.forallE (.app (.const ``Decidable []) (.bvar 0))
      (.forallE ty (.forallE ty ty)))) :
    ∃ result, LeanStructuralConversion.prove env setup.basic setup.exposure 0 (fuel+19) ctx
      (choice ty .word v d a b) (choice resultType annotation v d a b) = some result ∧ result.type = ty := by
  have embed : ∀ scope a b, SourceCasts env scope a b → Casts setup scope a b := fun _ _ _ h => .source h
  have method : DirectTyping env 0 ctx (.const ``ite [.succ .zero]) (Branch.iteSignature.type.instL [.succ .zero]) :=
    .constant iteDeclared (by simp [VLevel.WF]) rfl
  have prefixTyped := DirectTyping.application method valueType
  simp only [Branch.iteSignature,VExpr.instL,VLevel.inst,VExpr.inst,VExpr.instVar_zero,
    VExpr.instVar_succ,VExpr.instVar_lower,Nat.reduceAdd,List.map_nil,tyClosed.lift_eq] at prefixTyped
  have noBase {a b : VExpr} (ha : LeanTypeReduction.constantHead a = some (``ite,[.succ .zero]))
      (hb : LeanTypeReduction.constantHead b = some (``ite,[.succ .zero])) : setup.basic 0 ctx a b = none :=
    setup.basic_values_none (ty := wordType) (.constant ha freshIte (by decide))
      (.constant hb freshIte (by decide)) (by intro u h; cases h)
  obtain ⟨predicate,hp,tp⟩ := condition_proved setup library scalars closed .word annotation operand value form fresh freshLiteral freshEq (fuel+2)
  have first := CastTyping.application (prefixTyped.withCasts (Casts setup))
    ((condition_typed library scalars .word (operand.result value)).1.mono embed)
  obtain ⟨f1,h1,t1⟩ := LeanStructuralConversion.prove_application_or_same_complete
    (leftName := ``ite) (rightName := ``ite) rfl rfl (noBase rfl rfl)
    first (Casts.covered setup scalars closed (fuel+1)) fn hf tf predicate hp (.inl tp)
  simp only [VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower,
    Nat.reduceAdd,tyClosed.instN_eq (Nat.zero_le _)] at first t1
  obtain ⟨darg,hd,td⟩ := LeanStructuralConversion.prove_reflexive_cast_complete decisionTyped
    (setup.basic_values_none decisionForm decisionForm (by intro u h; cases h))
    (setup.covers_source_recursive scalars closed (fuel+11))
  have cast : Casts setup ctx (.app (.const ``Decidable []) (condition annotation v))
      (.app (.const ``Decidable []) (condition .word v)) :=
    .decision library annotation .word operand value form fresh freshLiteral freshEq freshDecision
  have second := CastTyping.convertedApplication first (decisionTyped.mono embed) cast
  obtain ⟨f2,h2,t2⟩ := LeanStructuralConversion.prove_application_or_same_complete
    (leftName := ``ite) (rightName := ``ite) rfl rfl (noBase rfl rfl)
    second (Casts.covered setup scalars closed (fuel+2)) f1 h1 t1 darg hd (.inr (td ▸ cast))
  simp only [VExpr.inst,tyClosed.instN_eq (Nat.zero_le _)] at second t2
  obtain ⟨aa,ha,ta⟩ := LeanStructuralConversion.prove_reflexive_cast_complete left
    (setup.basic_values_none leftForm leftForm notSortLeft) (setup.covers_source_recursive scalars closed (fuel+12))
  have checkedLeft : CheckedTyping env 0 (Casts setup) ctx a ty := by
    cases leftCast with
    | inl h => exact .exact (h ▸ left.mono embed)
    | inr h => exact .converted (left.mono embed) (.source h)
  have third := CastTyping.checkedApplication second checkedLeft
  obtain ⟨f3,h3,t3⟩ := LeanStructuralConversion.prove_application_or_same_complete
    (leftName := ``ite) (rightName := ``ite) rfl rfl (noBase rfl rfl)
    third (Casts.covered setup scalars closed (fuel+3)) f2 h2 t2 aa ha (by
      rw [ta]; exact leftCast.imp_right (fun h => Casts.source h))
  simp only [VExpr.inst,tyClosed.instN_eq (Nat.zero_le _)] at third t3
  obtain ⟨bb,hb,tb⟩ := LeanStructuralConversion.prove_reflexive_cast_complete right
    (setup.basic_values_none rightForm rightForm notSortRight) (setup.covers_source_recursive scalars closed (fuel+13))
  have checkedRight : CheckedTyping env 0 (Casts setup) ctx b ty := by
    cases rightCast with
    | inl h => exact .exact (h ▸ right.mono embed)
    | inr h => exact .converted (right.mono embed) (.source h)
  have final := CastTyping.checkedApplication third checkedRight
  obtain ⟨result,done,kind⟩ := LeanStructuralConversion.prove_application_or_same_complete
    (leftName := ``ite) (rightName := ``ite) rfl rfl (noBase rfl rfl)
    final (Casts.covered setup scalars closed (fuel+4)) f3 h3 t3 bb hb (by
      rw [tb]; exact rightCast.imp_right (fun h => Casts.source h))
  exact ⟨result,done,by simpa only [tyClosed.instN_eq (Nat.zero_le _)] using kind⟩




theorem choice_proved (setup : AliasSetup env) (library : Branch.BooleanLibrary env) (scalars : Signatures env)
    (closed : ClosedConstantTypes env) (annotation operand : WordBinder.Annotation)
    (value : CastTyping env 0 (SourceCasts env) ctx v operand.core) (form : ValueForm setup ctx v operand.core)
    (valueType : DirectTyping env 0 ctx ty (.sort (.succ .zero))) (tyClosed : ty.ClosedN 0)
    (decisionTyped : CastTyping env 0 (SourceCasts env) ctx d (.app (.const ``Decidable []) (condition annotation v)))
    (decisionForm : ValueForm setup ctx d (.app (.const ``Decidable []) (condition annotation v)))
    (left : CastTyping env 0 (SourceCasts env) ctx a ty) (right : CastTyping env 0 (SourceCasts env) ctx b ty)
    (leftForm : ValueForm setup ctx a ty) (rightForm : ValueForm setup ctx b ty)
    (notSort : ∀ u, ty ≠ .sort u)
    (iteDeclared : env.constants ``ite = some Branch.iteSignature)
    (fresh : ∀ r ∈ setup.rules, ``bne ≠ r.name)
    (freshLiteral : ∀ r ∈ setup.rules, ``OfNat.ofNat ≠ r.name)
    (freshEq : ∀ r ∈ setup.rules, ``Eq ≠ r.name)
    (freshDecision : ∀ r ∈ setup.rules, ``Decidable ≠ r.name)
    (freshIte : ∀ r ∈ setup.rules, ``ite ≠ r.name) (fuel : Nat) :
    ∃ result, LeanStructuralConversion.prove env setup.basic setup.exposure 0 (fuel+19) ctx
      (choice ty .word v d a b) (choice ty annotation v d a b) = some result ∧ result.type = ty := by
  have embed : ∀ scope a b, SourceCasts env scope a b → Casts setup scope a b := fun _ _ _ h => .source h
  have method : DirectTyping env 0 ctx (.const ``ite [.succ .zero]) (Branch.iteSignature.type.instL [.succ .zero]) :=
    .constant iteDeclared (by simp [VLevel.WF]) rfl
  have prefixTyped := DirectTyping.application method valueType
  simp only [Branch.iteSignature,VExpr.instL,VLevel.inst,VExpr.inst,VExpr.instVar_zero,
    VExpr.instVar_succ,VExpr.instVar_lower,Nat.reduceAdd,List.map_nil,tyClosed.lift_eq] at prefixTyped
  have noBase {a b : VExpr} (ha : LeanTypeReduction.constantHead a = some (``ite,[.succ .zero]))
      (hb : LeanTypeReduction.constantHead b = some (``ite,[.succ .zero])) : setup.basic 0 ctx a b = none :=
    setup.basic_values_none (ty := wordType) (.constant ha freshIte (by decide))
      (.constant hb freshIte (by decide)) (by intro u h; cases h)
  obtain ⟨fn,hf,tf⟩ := LeanStructuralConversion.prove_reflexive_complete prefixTyped (noBase rfl rfl) (fuel+14) setup.exposure
  exact choice_with_prefix_proved setup library scalars closed annotation operand value form valueType tyClosed
    decisionTyped decisionForm left right (.inl rfl) (.inl rfl) leftForm rightForm notSort notSort
    iteDeclared fresh freshLiteral freshEq freshDecision freshIte fuel fn hf tf

theorem scalar_choice_proved (setup : AliasSetup env) (library : Branch.BooleanLibrary env) (scalars : Signatures env)
    (closed : ClosedConstantTypes env) (resultAnnotation annotation operand oa ob : WordBinder.Annotation)
    (value : CastTyping env 0 (SourceCasts env) ctx v operand.core) (form : ValueForm setup ctx v operand.core)
    (decisionTyped : CastTyping env 0 (SourceCasts env) ctx d (.app (.const ``Decidable []) (condition annotation v)))
    (decisionForm : ValueForm setup ctx d (.app (.const ``Decidable []) (condition annotation v)))
    (left : CastTyping env 0 (SourceCasts env) ctx a oa.core) (right : CastTyping env 0 (SourceCasts env) ctx b ob.core)
    (leftForm : ValueForm setup ctx a oa.core) (rightForm : ValueForm setup ctx b ob.core)
    (iteDeclared : env.constants ``ite = some Branch.iteSignature)
    (fresh : ∀ r ∈ setup.rules, ``bne ≠ r.name)
    (freshLiteral : ∀ r ∈ setup.rules, ``OfNat.ofNat ≠ r.name)
    (freshEq : ∀ r ∈ setup.rules, ``Eq ≠ r.name)
    (freshDecision : ∀ r ∈ setup.rules, ``Decidable ≠ r.name)
    (freshIte : ∀ r ∈ setup.rules, ``ite ≠ r.name) (fuel : Nat) :
    ∃ result, LeanStructuralConversion.prove env setup.basic setup.exposure 0 (fuel+19) ctx
      (choice wordType .word v d a b) (choice resultAnnotation.core annotation v d a b) = some result ∧ result.type = wordType := by
  have method : DirectTyping env 0 ctx (.const ``ite [.succ .zero]) (Branch.iteSignature.type.instL [.succ .zero]) :=
    .constant iteDeclared (by simp [VLevel.WF]) rfl
  have noBase {a b : VExpr} (ha : LeanTypeReduction.constantHead a = some (``ite,[.succ .zero]))
      (hb : LeanTypeReduction.constantHead b = some (``ite,[.succ .zero])) : setup.basic 0 ctx a b = none :=
    setup.basic_values_none (ty := wordType) (.constant ha freshIte (by decide))
      (.constant hb freshIte (by decide)) (by intro u h; cases h)
  obtain ⟨fn,hf,tf⟩ := LeanStructuralConversion.prove_reflexive_complete method (noBase rfl rfl) (fuel+13) setup.exposure
  obtain ⟨arg,ha,ta⟩ := setup.spelling_proved scalars .word (AnnotatedBinary.spelling resultAnnotation) (fuel+13)
  have prefixTyped := DirectTyping.application method ((WordBinder.Annotation.word).type_typed scalars)
  obtain ⟨pref,hp,tp⟩ := LeanStructuralConversion.prove_application_or_same_complete
    (leftName := ``ite) (rightName := ``ite) rfl rfl (noBase rfl rfl)
    (prefixTyped.withCasts (SourceCasts env)) (setup.covers_source_recursive scalars closed (fuel+10)) fn hf tf arg ha (.inl ta)
  simp only [Branch.iteSignature,VExpr.instL,VLevel.inst,VExpr.inst,VExpr.instVar_zero,
    VExpr.instVar_succ,VExpr.instVar_lower,Nat.reduceAdd,List.map_nil,wordType,VExpr.lift,VExpr.liftN] at tp
  have lc : oa.core = wordType ∨ SourceCasts env ctx oa.core wordType := by
    cases oa; exact .inl rfl; exact .inr .bitvecValue
  have rc : ob.core = wordType ∨ SourceCasts env ctx ob.core wordType := by
    cases ob; exact .inl rfl; exact .inr .bitvecValue
  exact choice_with_prefix_proved setup library scalars closed annotation operand value form
    ((WordBinder.Annotation.word).type_typed scalars) (by trivial) decisionTyped decisionForm left right lc rc
    leftForm rightForm (by cases oa <;> intro u h <;> cases h) (by cases ob <;> intro u h <;> cases h)
    iteDeclared fresh freshLiteral freshEq freshDecision freshIte fuel pref hp tp

theorem choice_equality_proved (setup : AliasSetup env) (library : Branch.BooleanLibrary env) (scalars : Signatures env)
    (closed : ClosedConstantTypes env) (annotation operand : WordBinder.Annotation)
    (value : CastTyping env 0 (SourceCasts env) ctx v operand.core) (form : ValueForm setup ctx v operand.core)
    (valueType : DirectTyping env 0 ctx ty (.sort (.succ .zero))) (tyClosed : ty.ClosedN 0)
    (decisionTyped : CastTyping env 0 (SourceCasts env) ctx d (.app (.const ``Decidable []) (condition annotation v)))
    (decisionForm : ValueForm setup ctx d (.app (.const ``Decidable []) (condition annotation v)))
    (left : CastTyping env 0 (SourceCasts env) ctx a ty) (right : CastTyping env 0 (SourceCasts env) ctx b ty)
    (leftForm : ValueForm setup ctx a ty) (rightForm : ValueForm setup ctx b ty)
    (notSort : ∀ u, ty ≠ .sort u)
    (iteDeclared : env.constants ``ite = some Branch.iteSignature)
    (fresh : ∀ r ∈ setup.rules, ``bne ≠ r.name)
    (freshLiteral : ∀ r ∈ setup.rules, ``OfNat.ofNat ≠ r.name)
    (freshEq : ∀ r ∈ setup.rules, ``Eq ≠ r.name)
    (freshDecision : ∀ r ∈ setup.rules, ``Decidable ≠ r.name)
    (freshIte : ∀ r ∈ setup.rules, ``ite ≠ r.name)
    (prefixTyped : CastTyping env 0 (SourceCasts env) ctx
      (.app (.app (.const ``Eq [.succ .zero]) ty) lhs) (.forallE ty (.sort .zero))) (fuel : Nat) :
    ∃ result, LeanStructuralConversion.prove env setup.basic setup.exposure 0 (fuel+20) ctx
      (equalValues ty lhs (choice ty .word v d a b))
      (equalValues ty lhs (choice ty annotation v d a b)) = some result ∧ result.type = .sort .zero := by
  have embed : ∀ scope a b, SourceCasts env scope a b → Casts setup scope a b := fun _ _ _ h => .source h
  obtain ⟨fn,hf,tf⟩ := LeanStructuralConversion.prove_reflexive_cast_complete prefixTyped
    (setup.basic_no_reduction _ _ rfl rfl freshEq freshEq rfl)
    (setup.covers_source_recursive scalars closed (fuel+14))
  obtain ⟨arg,ha,ta⟩ := choice_proved setup library scalars closed annotation operand value form valueType tyClosed
    decisionTyped decisionForm left right leftForm rightForm notSort iteDeclared fresh freshLiteral freshEq freshDecision freshIte fuel
  have cast : Casts setup ctx (.app (.const ``Decidable []) (condition annotation v))
      (.app (.const ``Decidable []) (condition .word v)) :=
    .decision library annotation .word operand value form fresh freshLiteral freshEq freshDecision
  have chosen : CastTyping env 0 (Casts setup) ctx (choice ty .word v d a b) ty :=
    Branch.ite_checked_typed valueType tyClosed
      ((condition_typed library scalars .word (operand.result value)).1.mono embed)
      (.converted (decisionTyped.mono embed) cast) (.exact (left.mono embed)) (.exact (right.mono embed)) iteDeclared
  obtain ⟨result,done,kind⟩ := LeanStructuralConversion.prove_application_or_same_complete
    (leftName := ``Eq) (rightName := ``Eq) rfl rfl
    (setup.basic_no_reduction _ _ rfl rfl freshEq freshEq rfl)
    (CastTyping.application (prefixTyped.mono embed) chosen)
    (Casts.covered setup scalars closed (fuel+5)) fn hf tf arg ha (.inl ta)
  exact ⟨result,done,kind⟩



/-- Independent typing/shape conditions shared by all result types of `ite`.
This record contains no parser run or generated Entry. -/
structure ChoiceConditions (setup : AliasSetup env) (ctx : List VExpr)
    (ty v d a b lhs : VExpr) (annotation : WordBinder.Annotation) where
  library : Branch.BooleanLibrary env
  operand : WordBinder.Annotation
  value : CastTyping env 0 (SourceCasts env) ctx v operand.core
  form : ValueForm setup ctx v operand.core
  valueType : DirectTyping env 0 ctx ty (.sort (.succ .zero))
  tyClosed : ty.ClosedN 0
  decisionTyped : CastTyping env 0 (SourceCasts env) ctx d (.app (.const ``Decidable []) (condition annotation v))
  decisionForm : ValueForm setup ctx d (.app (.const ``Decidable []) (condition annotation v))
  left : CastTyping env 0 (SourceCasts env) ctx a ty
  right : CastTyping env 0 (SourceCasts env) ctx b ty
  leftForm : ValueForm setup ctx a ty
  rightForm : ValueForm setup ctx b ty
  notSort : ∀ u, ty ≠ .sort u
  iteDeclared : env.constants ``ite = some Branch.iteSignature
  fresh : ∀ r ∈ setup.rules, ``bne ≠ r.name
  freshLiteral : ∀ r ∈ setup.rules, ``OfNat.ofNat ≠ r.name
  freshEq : ∀ r ∈ setup.rules, ``Eq ≠ r.name
  freshDecision : ∀ r ∈ setup.rules, ``Decidable ≠ r.name
  freshIte : ∀ r ∈ setup.rules, ``ite ≠ r.name
  prefixTyped : CastTyping env 0 (SourceCasts env) ctx
    (.app (.app (.const ``Eq [.succ .zero]) ty) lhs) (.forallE ty (.sort .zero))

theorem ChoiceConditions.conversion {setup : AliasSetup env} (h : ChoiceConditions setup ctx ty v d a b lhs annotation)
    (scalars : Signatures env) (closed : ClosedConstantTypes env) :
    ∃ result, setup.conversion 0 ctx
      (equalValues ty lhs (choice ty .word v d a b))
      (equalValues ty lhs (choice ty annotation v d a b)) = some result := by
  obtain ⟨eq,he,te⟩ := choice_equality_proved setup h.library scalars closed annotation h.operand
    h.value h.form h.valueType h.tyClosed h.decisionTyped h.decisionForm h.left h.right h.leftForm h.rightForm
    h.notSort h.iteDeclared h.fresh h.freshLiteral h.freshEq h.freshDecision h.freshIte h.prefixTyped 44
  exact LeanStructuralConversion.conversion_of_prove eq he te

theorem Casts.covered_top (setup : AliasSetup env) (scalars : Signatures env)
    (closed : ClosedConstantTypes env) : Conversion.Covers setup.conversion 0 (Casts setup) := by
  intro ctx actual expected cast
  cases cast with
  | source h => exact setup.covers_source scalars closed ctx actual expected h
  | decision library original annotation operand value form fresh freshLiteral freshEq freshDecision =>
    obtain ⟨eq,he,te⟩ := decidable_proved setup library scalars closed original annotation operand
      value form fresh freshLiteral freshEq freshDecision 50
    exact LeanStructuralConversion.conversion_of_prove eq he te



theorem scalar_choice_typed (setup : AliasSetup env) (library : Branch.BooleanLibrary env) (scalars : Signatures env)
    (annotation operand oa ob : WordBinder.Annotation)
    (value : CastTyping env 0 (SourceCasts env) ctx v operand.core) (form : ValueForm setup ctx v operand.core)
    (decisionTyped : CastTyping env 0 (SourceCasts env) ctx d (.app (.const ``Decidable []) (condition annotation v)))
    (left : CastTyping env 0 (SourceCasts env) ctx a oa.core) (right : CastTyping env 0 (SourceCasts env) ctx b ob.core)
    (iteDeclared : env.constants ``ite = some Branch.iteSignature)
    (fresh : ∀ r ∈ setup.rules, ``bne ≠ r.name)
    (freshLiteral : ∀ r ∈ setup.rules, ``OfNat.ofNat ≠ r.name)
    (freshEq : ∀ r ∈ setup.rules, ``Eq ≠ r.name)
    (freshDecision : ∀ r ∈ setup.rules, ``Decidable ≠ r.name) :
    CastTyping env 0 (Casts setup) ctx (choice wordType .word v d a b) wordType := by
  have embed : ∀ scope a b, SourceCasts env scope a b → Casts setup scope a b := fun _ _ _ h => .source h
  exact Branch.ite_checked_typed ((WordBinder.Annotation.word).type_typed scalars) (by trivial)
    ((condition_typed library scalars .word (operand.result value)).1.mono embed)
    (.converted (decisionTyped.mono embed)
      (.decision library annotation .word operand value form fresh freshLiteral freshEq freshDecision))
    ((oa.result left).mono embed) ((ob.result right).mono embed) iteDeclared



/-- Shape and source typing for scalar choices. All fields concern the
original terms and library declarations, independently of compiler success. -/
structure ScalarConditions (setup : AliasSetup env) (ctx : List VExpr)
    (v d a b : VExpr) (annotation : WordBinder.Annotation) where
  library : Branch.BooleanLibrary env
  operand : WordBinder.Annotation
  leftAnnotation : WordBinder.Annotation
  rightAnnotation : WordBinder.Annotation
  value : CastTyping env 0 (SourceCasts env) ctx v operand.core
  form : ValueForm setup ctx v operand.core
  decisionTyped : CastTyping env 0 (SourceCasts env) ctx d (.app (.const ``Decidable []) (condition annotation v))
  decisionForm : ValueForm setup ctx d (.app (.const ``Decidable []) (condition annotation v))
  left : CastTyping env 0 (SourceCasts env) ctx a leftAnnotation.core
  right : CastTyping env 0 (SourceCasts env) ctx b rightAnnotation.core
  leftForm : ValueForm setup ctx a leftAnnotation.core
  rightForm : ValueForm setup ctx b rightAnnotation.core
  iteDeclared : env.constants ``ite = some Branch.iteSignature
  fresh : ∀ r ∈ setup.rules, ``bne ≠ r.name
  freshLiteral : ∀ r ∈ setup.rules, ``OfNat.ofNat ≠ r.name
  freshDecision : ∀ r ∈ setup.rules, ``Decidable ≠ r.name
  freshIte : ∀ r ∈ setup.rules, ``ite ≠ r.name

def scalarSource (resultAnnotation annotation : WordBinder.Annotation) (v d a b : Lean.Expr) : Lean.Expr :=
  Lean.mkApp5 (.const ``ite [.succ .zero]) resultAnnotation.native (nativeCondition annotation v) d a b

theorem scalarSource_represents (resultAnnotation annotation : WordBinder.Annotation)
    (vr : Represents v vc) (dr : Represents d dc) (ar : Represents a ac) (br : Represents b bc) :
    Represents (scalarSource resultAnnotation annotation v d a b)
      (choice resultAnnotation.core annotation vc dc ac bc) :=
  app_represents (.constant rfl) (.cons resultAnnotation.represented
    (.cons (condition_represents annotation vr) (.cons dr (.cons ar (.cons br .nil)))))

theorem scalarSource_typed (library : Branch.BooleanLibrary env) (scalars : Signatures env)
    (resultAnnotation annotation : WordBinder.Annotation)
    (value : CheckedTyping env 0 (SourceCasts env) ctx v wordType)
    (decisionTyped : CastTyping env 0 (SourceCasts env) ctx d (.app (.const ``Decidable []) (condition annotation v)))
    (left : CheckedTyping env 0 (SourceCasts env) ctx a wordType)
    (right : CheckedTyping env 0 (SourceCasts env) ctx b wordType)
    (iteDeclared : env.constants ``ite = some Branch.iteSignature) :
    CheckedTyping env 0 (SourceCasts env) ctx (choice resultAnnotation.core annotation v d a b) wordType :=
  resultAnnotation.result (Branch.ite_typed (resultAnnotation.type_typed scalars) resultAnnotation.closed
    (condition_typed library scalars annotation value).1 decisionTyped
    (resultAnnotation.argument left) (resultAnnotation.argument right) iteDeclared)

end IRComparison.WordFrontend.AnnotatedCondition
