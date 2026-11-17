import IRComparison.Frontend.WordAnnotatedBinary

/-! Fixed congruence for elaborated arithmetic headers. The recursion over
operands belongs to the source judgment; these proofs compare only the four
closed type/dictionary arguments of an arithmetic operator. -/
namespace IRComparison.WordFrontend.AnnotatedBinary
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic
set_option maxHeartbeats 2400000

private def liftedType (op : Binary) : VExpr :=
  .forallE (.sort (.succ .zero))
    (.forallE (.app (.const op.className [.zero]) (.bvar 0))
      (op.classApplication (.bvar 1) (.bvar 1) (.bvar 1)))
private def dictionaryTail (op : Binary) (ty : VExpr) : VExpr :=
  .forallE (.app (.const op.className [.zero]) ty) (op.classApplication ty ty ty)

private theorem lifted_form (setup : AliasSetup env) (library : Signatures env) (op : Binary) :
    ValueForm setup ctx (.const op.liftedInstance [.zero]) (liftedType op) :=
  .declaredConstant (library.lifted op) (by cases op <;> decide)

private theorem dictionary_prefix_form (setup : AliasSetup env) (library : Signatures env)
    (op : Binary) (annotation : WordBinder.Annotation) :
    ValueForm setup ctx (.app (.const op.liftedInstance [.zero]) annotation.core)
      (dictionaryTail op annotation.core) := by
  have form := (lifted_form (ctx := ctx) setup library op).application (arg := annotation.core)
  simpa only [liftedType,dictionaryTail,Binary.classApplication,applications,VExpr.inst,
    VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower,
    annotation.closed.liftN_eq (Nat.zero_le _),VExpr.lift,VExpr.liftN,liftVar,Nat.reduceLT,ite_false,ite_true,Nat.reduceAdd] using form

private theorem dictionary_form (setup : AliasSetup env) (library : Signatures env)
    (op : Binary) (annotation : WordBinder.Annotation) :
    ValueForm setup ctx (dictionary op annotation)
      (op.classApplication annotation.core annotation.core annotation.core) := by
  have form := (dictionary_prefix_form (ctx := ctx) setup library op annotation).application
    (arg := .app (.const op.instanceName []) width)
  simpa only [dictionary,dictionaryTail,Binary.classApplication,applications,VExpr.inst,
    annotation.closed.instN_eq (Nat.zero_le _)] using form

/-- The dictionary supplied by elaboration may itself use BitVec 32, even
when one or more method type arguments are spelled Word. -/
theorem dictionary_proved (setup : AliasSetup env) (library : Signatures env)
    (closed : ClosedConstantTypes env) (op : Binary) (annotation : WordBinder.Annotation) (fuel : Nat) :
    ∃ result, LeanStructuralConversion.prove env setup.basic setup.exposure 0 (fuel+7) ctx
      (dictionary op .word) (dictionary op annotation) = some result ∧
      result.type = op.classApplication wordType wordType wordType := by
  have headTyped : DirectTyping env 0 ctx (.const op.liftedInstance [.zero]) (liftedType op) :=
    .constant (library.lifted op) (by simp [VLevel.WF]) rfl
  have headNone := setup.basic_values_none (ctx := ctx) (lifted_form setup library op) (lifted_form setup library op)
    (by intro u h; cases h)
  obtain ⟨fn,hfn,tfn⟩ := LeanStructuralConversion.prove_reflexive_complete headTyped headNone (fuel+4) setup.exposure
  obtain ⟨ty,hty,tty⟩ := setup.spelling_proved library .word (spelling annotation) (fuel+4)
  have prefixTyped := DirectTyping.application headTyped ((WordBinder.Annotation.word).type_typed library)
  have prefixNone := setup.basic_values_none_of_types (ctx := ctx)
    (dictionary_prefix_form setup library op .word) (dictionary_prefix_form setup library op annotation)
    (by intro u h; cases h) (by intro u h; cases h)
  obtain ⟨applied,ha,ta⟩ := LeanStructuralConversion.prove_application_or_same_complete
    (leftName := op.liftedInstance) (rightName := op.liftedInstance) rfl rfl prefixNone
    (prefixTyped.withCasts (SourceCasts env))
    (setup.covers_source_recursive library closed (fuel+1)) fn hfn tfn ty hty (.inl tty)
  change applied.type = dictionaryTail op wordType at ta
  have instanceTyped : DirectTyping env 0 ctx (.const op.instanceName []) op.instanceSignature :=
    .constant (library.instances op) (by simp) rfl
  have instanceValue := DirectTyping.application instanceTyped library.width_typed
  have instanceForm : ValueForm setup ctx (.const op.instanceName []) op.instanceSignature :=
    .declaredConstant (library.instances op) (by cases op <;> decide)
  have instanceNone := setup.basic_values_none (instanceForm.application (arg := width))
    (instanceForm.application (arg := width)) (by intro u h; cases h)
  obtain ⟨arg,harg,targ⟩ := LeanStructuralConversion.prove_reflexive_complete instanceValue instanceNone (fuel+5) setup.exposure
  have noBase := setup.basic_values_none_of_types (ctx := ctx)
    (dictionary_form setup library op .word) (dictionary_form setup library op annotation)
    (by intro u h; cases h) (by intro u h; cases h)
  have leftTyped := dictionary_typed library op .word (ctx := ctx)
  obtain ⟨result,done,kind⟩ := LeanStructuralConversion.prove_application_or_same_complete
    (leftName := op.liftedInstance) (rightName := op.liftedInstance) rfl rfl noBase
    leftTyped (setup.covers_source_recursive library closed (fuel+2))
    applied ha ta arg harg (.inr (by rw [targ]; simpa only [VExpr.inst,VExpr.instVar_zero] using (SourceCasts.arithmetic (Casts.wordInstance op) (env := env) (ctx := ctx))))
  exact ⟨result,done,kind⟩

private theorem method_none (setup : AliasSetup env) (op : Binary)
    (fresh : ∀ r ∈ setup.rules, op.method ≠ r.name)
    (left : LeanTypeReduction.constantHead a = some (op.method,[.zero,.zero,.zero]))
    (right : LeanTypeReduction.constantHead b = some (op.method,[.zero,.zero,.zero])) :
    setup.basic 0 ctx a b = none :=
  setup.basic_values_none (ty := wordType)
    (.constant left fresh (by cases op <;> decide))
    (.constant right fresh (by cases op <;> decide)) (by intro u h; cases h)

/-- The complete binary header has a fixed congruence depth, independently
of the source operands and the surrounding lexical nesting. -/
theorem header_proved (setup : AliasSetup env) (library : Signatures env)
    (closed : ClosedConstantTypes env) (op : Binary) (a b c d : WordBinder.Annotation)
    (fresh : ∀ r ∈ setup.rules, op.method ≠ r.name) (fuel : Nat) :
    ∃ result, LeanStructuralConversion.prove env setup.basic setup.exposure 0 (fuel+11) ctx
      (header op .word .word .word .word) (header op a b c d) = some result ∧
      result.type = .forallE wordType (.forallE wordType wordType) := by
  have method : DirectTyping env 0 ctx (.const op.method [.zero,.zero,.zero])
      (.forallE (.sort (.succ .zero)) (.forallE (.sort (.succ .zero))
        (.forallE resultParameter (.forallE
          (op.classApplication (.bvar 2) (.bvar 1) (.bvar 0))
          (.forallE (.bvar 3) (.forallE (.bvar 3) (.bvar 3))))))) :=
    .constant (library.methods op) (by simp [VLevel.WF]) rfl
  obtain ⟨fn,hfn,tfn⟩ := LeanStructuralConversion.prove_reflexive_complete method
    (method_none setup op fresh rfl rfl) (fuel+6) setup.exposure
  obtain ⟨aa,ha,ta⟩ := setup.spelling_proved library .word (spelling a) (fuel+6)
  have first := CastTyping.application (method.withCasts (SourceCasts env))
    ((WordBinder.Annotation.word.type_typed library).withCasts (SourceCasts env))
  obtain ⟨f1,hf1,tf1⟩ := LeanStructuralConversion.prove_application_or_same_complete
    (leftName := op.method) (rightName := op.method) rfl rfl (method_none setup op fresh rfl rfl)
    first (setup.covers_source_recursive library closed (fuel+3)) fn hfn tfn aa ha (.inl ta)
  simp only [Binary.classApplication,applications,resultParameter,WordBinder.Annotation.core,wordType,VExpr.inst,
    VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower,VExpr.lift,VExpr.liftN,liftVar,Nat.reduceLT,ite_false,ite_true,Nat.reduceAdd] at first tf1
  obtain ⟨bb,hb,tb⟩ := setup.spelling_proved library .word (spelling b) (fuel+7)
  have second := CastTyping.application first
    ((WordBinder.Annotation.word.type_typed library).withCasts (SourceCasts env))
  obtain ⟨f2,hf2,tf2⟩ := LeanStructuralConversion.prove_application_or_same_complete
    (leftName := op.method) (rightName := op.method) rfl rfl (method_none setup op fresh rfl rfl)
    second (setup.covers_source_recursive library closed (fuel+4)) f1 hf1 tf1 bb hb (.inl tb)
  simp only [VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower,
    WordBinder.Annotation.core,wordType,VExpr.lift,VExpr.liftN,liftVar,Nat.reduceLT,ite_false,ite_true,Nat.reduceAdd] at second tf2
  obtain ⟨cc,hc,tc⟩ := setup.spelling_proved library .word (spelling c) (fuel+8)
  have third := CastTyping.convertedApplication second
    ((WordBinder.Annotation.word.type_typed library).withCasts (SourceCasts env))
    (SourceCasts.arithmetic Casts.resultType)
  obtain ⟨f3,hf3,tf3⟩ := LeanStructuralConversion.prove_application_or_same_complete
    (leftName := op.method) (rightName := op.method) rfl rfl (method_none setup op fresh rfl rfl)
    third (setup.covers_source_recursive library closed (fuel+5)) f2 hf2 tf2 cc hc
    (.inr (by rw [tc]; exact .arithmetic .resultType))
  simp only [VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower,
    WordBinder.Annotation.core,wordType,VExpr.lift,VExpr.liftN,liftVar,Nat.reduceLT,ite_false,ite_true,Nat.reduceAdd] at third tf3
  obtain ⟨dd,hd,td⟩ := dictionary_proved setup library closed op d (fuel+3)
  have final := CastTyping.application third (dictionary_typed library op .word)
  obtain ⟨result,done,kind⟩ := LeanStructuralConversion.prove_application_or_same_complete
    (leftName := op.method) (rightName := op.method) rfl rfl (method_none setup op fresh rfl rfl)
    final (setup.covers_source_recursive library closed (fuel+6)) f3 hf3 tf3 dd hd (.inl td)
  exact ⟨result,done,kind⟩

/-- Reflexive operands are inferred, not recursively compared. Consequently
the fixed header conversion does not impose a bound on operand syntax. -/
theorem value_proved (setup : AliasSetup env) (library : Signatures env)
    (closed : ClosedConstantTypes env) (op : Binary) (a b c d oa ob : WordBinder.Annotation)
    (left : CastTyping env 0 (SourceCasts env) ctx u oa.core)
    (right : CastTyping env 0 (SourceCasts env) ctx v ob.core)
    (leftForm : ValueForm setup ctx u oa.core) (rightForm : ValueForm setup ctx v ob.core)
    (fresh : ∀ r ∈ setup.rules, op.method ≠ r.name) (fuel : Nat) :
    ∃ result, LeanStructuralConversion.prove env setup.basic setup.exposure 0 (fuel+13) ctx
      (.app (.app (header op .word .word .word .word) u) v)
      (.app (.app (header op a b c d) u) v) = some result ∧ result.type = wordType := by
  obtain ⟨fn,hfn,tfn⟩ := header_proved setup library closed op a b c d fresh fuel
  obtain ⟨arg,harg,targ⟩ := LeanStructuralConversion.prove_reflexive_cast_complete left
    (setup.basic_values_none leftForm leftForm (by cases oa <;> intro u h <;> cases h))
    (setup.covers_source_recursive library closed (fuel+6))
  have first := CastTyping.checkedApplication (header_typed library op .word .word .word .word)
    (oa.result left)
  have argCast : arg.type = wordType ∨ SourceCasts env ctx arg.type wordType := by
    rw [targ]; cases oa
    · exact .inl rfl
    · exact .inr .bitvecValue
  obtain ⟨f1,hf1,tf1⟩ := LeanStructuralConversion.prove_application_or_same_complete
    (leftName := op.method) (rightName := op.method) rfl rfl (method_none setup op fresh rfl rfl)
    first (setup.covers_source_recursive library closed (fuel+7)) fn hfn tfn arg harg argCast
  change f1.type = .forallE wordType wordType at tf1
  change CastTyping env 0 (SourceCasts env) ctx _ (.forallE wordType wordType) at first
  obtain ⟨arg2,harg2,targ2⟩ := LeanStructuralConversion.prove_reflexive_cast_complete right
    (setup.basic_values_none rightForm rightForm (by cases ob <;> intro u h <;> cases h))
    (setup.covers_source_recursive library closed (fuel+7))
  have second := CastTyping.checkedApplication first (ob.result right)
  have argCast2 : arg2.type = wordType ∨ SourceCasts env ctx arg2.type wordType := by
    rw [targ2]; cases ob
    · exact .inl rfl
    · exact .inr .bitvecValue
  obtain ⟨result,done,kind⟩ := LeanStructuralConversion.prove_application_or_same_complete
    (leftName := op.method) (rightName := op.method) rfl rfl (method_none setup op fresh rfl rfl)
    second (setup.covers_source_recursive library closed (fuel+8)) f1 hf1 tf1 arg2 harg2 argCast2
  exact ⟨result,done,kind⟩

end IRComparison.WordFrontend.AnnotatedBinary
