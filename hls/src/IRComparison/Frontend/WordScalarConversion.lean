import IRComparison.Frontend.WordNegCompleteness
import IRComparison.Frontend.WordReturnCompleteness
import IRComparison.Frontend.WordLexicalScope
import IRComparison.Frontend.WordBinder
import IRComparison.Frontend.WordAnnotatedCondition

/-! Fixed congruence layers for scalar lexical certificate transports.
Source nesting is handled by the syntax induction, not by a larger conversion
budget. All typing premises describe source/library terms independently. -/
namespace IRComparison.WordFrontend.ScalarConversion
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic
variable {casts proofCasts : TypeCasts} [Arithmetic.Includes casts] [Arithmetic.Includes proofCasts]
set_option maxHeartbeats 1500000

def evalSignature : VExpr := inputsType (.forallE exprType (optionType wordType))
structure Signatures (env : VEnv) : Prop where
  word : env.constants ``HybridWord.Word = some ⟨0,.sort (.succ .zero)⟩
  option : env.constants ``Option = some optionSignature
  someDecl : env.constants ``Option.some = some Return.someSignature
  eq : env.constants ``Eq = some eqSignature
  eval : env.constants ``HybridWord.Expr.eval = some ⟨0,evalSignature⟩

theorem Signatures.word_typed (library : Signatures env) :
    DirectTyping env 0 ctx wordType (.sort (.succ .zero)) :=
  .constant library.word (by simp) rfl

theorem Signatures.option_typed (library : Signatures env) :
    DirectTyping env 0 ctx (optionType wordType) (.sort (.succ .zero)) := by
  have h : DirectTyping env 0 ctx (.const ``Option [.zero])
      (.forallE (.sort (.succ .zero)) (.sort (.succ .zero))) :=
    .constant library.option (by simp [VLevel.WF]) rfl
  exact .application h library.word_typed

theorem Signatures.some_typed (library : Signatures env) :
    DirectTyping env 0 ctx (.app (.const ``Option.some [.zero]) wordType)
      (.forallE wordType (optionType wordType)) := by
  have h : DirectTyping env 0 ctx (.const ``Option.some [.zero]) (Return.someSignature.type.instL [.zero]) :=
    .constant library.someDecl (by simp [VLevel.WF]) rfl
  simpa only [Return.someSignature,VExpr.instL,VLevel.inst,VExpr.inst,VExpr.instVar_zero,
    VExpr.instVar_succ,VExpr.instVar_lower,Nat.reduceAdd,List.map_nil,wordType,optionType,
    VExpr.lift,VExpr.liftN,liftVar,Nat.reduceLT,ite_true,ite_false] using
    DirectTyping.application h library.word_typed

theorem eval_typed (library : Signatures env) (inputs : InputsTyped env ctx p)
    (codeTyped : CastTyping env 0 casts ctx code exprType) :
    CastTyping env 0 casts ctx
      (scalarValue inputs.i.val inputs.x.val inputs.y.val inputs.s.val inputs.ls.val code)
      (optionType wordType) := by
  have h : CastTyping env 0 casts ctx (.const ``HybridWord.Expr.eval []) evalSignature :=
    .constant library.eval (by simp) rfl
  have first := inputs.apply_casts h
  simp only [InputsTyped.instantiate,evalSignature,inputsType,exprType,wordType,optionType,VExpr.inst] at first
  exact .application first codeTyped

def prefixEq (lhs : VExpr) : VExpr := .app (.app (.const ``Eq [.succ .zero]) (optionType wordType)) lhs

theorem prefix_typed (library : Signatures env)
    (left : CastTyping env 0 casts ctx lhs (optionType wordType)) :
    CastTyping env 0 casts ctx (prefixEq lhs) (.forallE (optionType wordType) (.sort .zero)) := by
  have h : CastTyping env 0 casts ctx (.const ``Eq [.succ .zero])
      (.forallE (.sort (.succ .zero)) (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)))) :=
    .constant library.eq (by simp [VLevel.WF]) rfl
  have first := CastTyping.application h (library.option_typed.withCasts casts)
  simp only [VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,optionType,wordType,VExpr.lift,VExpr.liftN] at first
  exact .application first left

theorem expected_typed (library : Signatures env)
    (left : CastTyping env 0 casts ctx lhs (optionType wordType))
    (right : CheckedTyping env 0 casts ctx rhs wordType) :
    CastTyping env 0 casts ctx (equalValues (optionType wordType) lhs (someValue wordType rhs)) (.sort .zero) :=
  .application (prefix_typed library left) (.checkedApplication (library.some_typed.withCasts casts) right)

/-- The only source reduction required here is one lexical beta step; the
surrounding `some` and equality contribute two fixed congruence layers. -/
theorem beta_expected_proved {body arg lhs : VExpr} (setup : AliasSetup env)
    (arithmetic : Arithmetic.Signatures env) (library : Signatures env)
    (closed : ClosedConstantTypes env) (annotation resultAnnotation : WordBinder.Annotation)
    (left : CastTyping env 0 (SourceCasts env) ctx lhs (optionType wordType))
    (bodyTyped : CastTyping env 0 (SourceCasts env) (annotation.core::ctx) body resultAnnotation.core)
    (argTyped : CheckedTyping env 0 (SourceCasts env) ctx arg annotation.core)
    (form : ∃ actual : WordBinder.Annotation, ValueForm setup ctx (body.inst arg) actual.core)
    (freshEq : ∀ r ∈ setup.rules, ``Eq ≠ r.name)
    (freshSome : ∀ r ∈ setup.rules, ``Option.some ≠ r.name) (fuel : Nat) :
    ∃ result, LeanStructuralConversion.prove env setup.basic setup.exposure 0 (fuel+7) ctx
      (equalValues (optionType wordType) lhs (someValue wordType (body.inst arg)))
      (equalValues (optionType wordType) lhs (someValue wordType (.app (.lam annotation.core body) arg))) = some result ∧
      result.type = .sort .zero := by
  obtain ⟨actual,form⟩ := form
  have eqNone : setup.basic 0 ctx
      (equalValues (optionType wordType) lhs (someValue wordType (body.inst arg)))
      (equalValues (optionType wordType) lhs (someValue wordType (.app (.lam annotation.core body) arg))) = none :=
    setup.basic_no_reduction _ _ rfl rfl freshEq freshEq rfl
  by_cases same : body.inst arg = .app (.lam annotation.core body) arg
  · have sameType : CheckedTyping env 0 (SourceCasts env) ctx (body.inst arg) wordType := by
      apply resultAnnotation.result
      have applied := CastTyping.checkedApplication
        (.lambda ((annotation.type_typed arithmetic).withCasts _) bodyTyped) argTyped
      simpa only [← same,resultAnnotation.closed.instN_eq (Nat.zero_le _)] using applied
    have reflexive := LeanStructuralConversion.prove_reflexive_cast_complete
      (expected_typed library left sameType)
      ((congrArg (fun rhs => setup.basic 0 ctx
        (equalValues (optionType wordType) lhs (someValue wordType (body.inst arg)))
        (equalValues (optionType wordType) lhs (someValue wordType rhs)) = none) same).mpr eqNone)
      (setup.covers_source_recursive arithmetic closed (fuel+2))
    exact (congrArg (fun rhs => ∃ result : LeanStructuralConversion.Equation env 0 ctx
      (equalValues (optionType wordType) lhs (someValue wordType (body.inst arg)))
      (equalValues (optionType wordType) lhs (someValue wordType rhs)),
      LeanStructuralConversion.prove env setup.basic setup.exposure 0 (fuel+7) ctx
        (equalValues (optionType wordType) lhs (someValue wordType (body.inst arg)))
        (equalValues (optionType wordType) lhs (someValue wordType rhs)) = some result ∧
      result.type = .sort .zero) same).mp (by simpa [Nat.add_assoc] using reflexive)
  · have someNone : setup.basic 0 ctx (.app (.const ``Option.some [.zero]) wordType)
        (.app (.const ``Option.some [.zero]) wordType) = none :=
      setup.basic_no_reduction _ _ rfl rfl freshSome freshSome rfl
    obtain ⟨fn,hfn,tfn⟩ := LeanStructuralConversion.prove_reflexive_complete
      library.some_typed someNone (fuel+4) setup.exposure
    obtain ⟨value,hvalue,tvalue⟩ := setup.scalar_beta_checked_domain_types arithmetic closed (annotation.type_typed arithmetic) resultAnnotation.closed
      (by cases resultAnnotation <;> intro u <;> simp [WordBinder.Annotation.core,wordType,bitvecType])
      bodyTyped argTyped (by cases actual <;> intro u <;> simp [WordBinder.Annotation.core,wordType,bitvecType]) form fuel
    have valueKind : ∃ a : WordBinder.Annotation, value.type = a.core :=
      tvalue.elim (fun h => ⟨actual,h⟩) (fun h => ⟨resultAnnotation,h⟩)
    obtain ⟨valueAnnotation,valueType⟩ := valueKind
    have optionNone : setup.basic 0 ctx (someValue wordType (body.inst arg))
        (someValue wordType (.app (.lam annotation.core body) arg)) = none :=
      setup.basic_no_reduction _ _ rfl rfl freshSome freshSome rfl
    obtain ⟨valueEq,hvalueEq,tvalueEq⟩ := LeanStructuralConversion.prove_application_cast_complete
      (leftName := ``Option.some) (rightName := ``Option.some) rfl rfl
      (fun h => same (VExpr.app.inj h).2) optionNone fn hfn tfn value hvalue (by
        intro different
        cases valueAnnotation with
        | word => exact False.elim (different valueType)
        | bitvec =>
          rw [valueType]
          simpa only [Nat.add_assoc] using
            (setup.covers_source_recursive arithmetic closed (fuel+1) ctx bitvecType wordType .bitvecValue))
    have prefixNone : setup.basic 0 ctx (prefixEq lhs) (prefixEq lhs) = none :=
      setup.basic_no_reduction _ _ rfl rfl freshEq freshEq rfl
    obtain ⟨eqFn,heqFn,teqFn⟩ := LeanStructuralConversion.prove_reflexive_cast_complete
      (prefix_typed library left) prefixNone (setup.covers_source_recursive arithmetic closed (fuel+1))
    have result := LeanStructuralConversion.prove_application_complete
      (leftName := ``Eq) (rightName := ``Eq) rfl rfl
      (fun h => same (VExpr.app.inj (VExpr.app.inj h).2).2) eqNone
      eqFn heqFn teqFn valueEq (by simpa [Nat.add_assoc] using hvalueEq) tvalueEq
    simpa [Nat.add_assoc,wordType,optionType,VExpr.inst] using result

/-- Lift an arithmetic-value conversion through the shared Some/Eq prefix.
Both unary and binary annotations use these same fixed congruence layers. -/
theorem expected_value_proved (setup : AliasSetup env) (arithmetic : Arithmetic.Signatures env)
    (library : Signatures env) (closed : ClosedConstantTypes env)
    (lhsTyped : CastTyping env 0 (SourceCasts env) ctx lhs (optionType wordType))
    (valueTyped : CastTyping env 0 (SourceCasts env) ctx original wordType)
    (freshEq : ∀ r ∈ setup.rules, ``Eq ≠ r.name)
    (freshSome : ∀ r ∈ setup.rules, ``Option.some ≠ r.name) (fuel : Nat)
    (hv : LeanStructuralConversion.prove env setup.basic setup.exposure 0 (fuel+13) ctx original updated = some value)
    (tv : value.type = wordType) :
    ∃ result, LeanStructuralConversion.prove env setup.basic setup.exposure 0 (fuel+15) ctx
      (equalValues (optionType wordType) lhs (someValue wordType original))
      (equalValues (optionType wordType) lhs (someValue wordType updated)) = some result ∧
      result.type = .sort .zero := by
  obtain ⟨fn,hfn,tfn⟩ := LeanStructuralConversion.prove_reflexive_complete library.some_typed
    (setup.basic_no_reduction _ _ rfl rfl freshSome freshSome rfl) (fuel+12) setup.exposure
  obtain ⟨wrapped,hw,tw⟩ := LeanStructuralConversion.prove_application_or_same_complete
    (leftName := ``Option.some) (rightName := ``Option.some) rfl rfl
    (setup.basic_no_reduction _ _ rfl rfl freshSome freshSome rfl)
    (.application (library.some_typed.withCasts (SourceCasts env)) valueTyped)
    (setup.covers_source_recursive arithmetic closed (fuel+9)) fn hfn tfn value hv (.inl tv)
  obtain ⟨eqFn,heq,teq⟩ := LeanStructuralConversion.prove_reflexive_cast_complete
    (prefix_typed library lhsTyped) (setup.basic_no_reduction _ _ rfl rfl freshEq freshEq rfl)
    (setup.covers_source_recursive arithmetic closed (fuel+9))
  obtain ⟨result,done,kind⟩ := LeanStructuralConversion.prove_application_or_same_complete
    (leftName := ``Eq) (rightName := ``Eq) rfl rfl
    (setup.basic_no_reduction _ _ rfl rfl freshEq freshEq rfl)
    (expected_typed library lhsTyped (.exact valueTyped))
    (setup.covers_source_recursive arithmetic closed (fuel+10)) eqFn heq teq wrapped hw (.inl tw)
  exact ⟨result,done,kind⟩

/-- Retain the actual elaborated arithmetic header in the source side of a
certificate, while using the generic arithmetic fact for its two children. -/
theorem binary_expected_proved (setup : AliasSetup env) (arithmetic : Arithmetic.Signatures env)
    (library : Signatures env) (closed : ClosedConstantTypes env)
    (op : Binary) (a b c d oa ob : WordBinder.Annotation)
    (lhsTyped : CastTyping env 0 (SourceCasts env) ctx lhs (optionType wordType))
    (left : CastTyping env 0 (SourceCasts env) ctx u oa.core)
    (right : CastTyping env 0 (SourceCasts env) ctx v ob.core)
    (leftForm : ValueForm setup ctx u oa.core) (rightForm : ValueForm setup ctx v ob.core)
    (fresh : ∀ r ∈ setup.rules, op.method ≠ r.name)
    (freshEq : ∀ r ∈ setup.rules, ``Eq ≠ r.name)
    (freshSome : ∀ r ∈ setup.rules, ``Option.some ≠ r.name) (fuel : Nat) :
    ∃ result, LeanStructuralConversion.prove env setup.basic setup.exposure 0 (fuel+15) ctx
      (equalValues (optionType wordType) lhs (someValue wordType (.app (.app op.header u) v)))
      (equalValues (optionType wordType) lhs
        (someValue wordType (.app (.app (AnnotatedBinary.header op a b c d) u) v))) = some result ∧
      result.type = .sort .zero := by
  obtain ⟨value,hv,tv⟩ := AnnotatedBinary.value_proved setup arithmetic closed op a b c d oa ob
    left right leftForm rightForm fresh fuel
  have valueTyped : CastTyping env 0 (SourceCasts env) ctx (.app (.app op.header u) v) wordType := by
    have first := CastTyping.checkedApplication ((arithmetic.header_typed op).mono (fun _ _ _ h => SourceCasts.arithmetic h)) (oa.result left)
    change CastTyping env 0 (SourceCasts env) ctx _ (.forallE wordType wordType) at first
    exact .checkedApplication first (ob.result right)
  exact expected_value_proved setup arithmetic library closed lhsTyped valueTyped freshEq freshSome fuel hv tv

theorem neg_expected_proved (setup : AliasSetup env) (arithmetic : Arithmetic.Signatures env)
    (library : Signatures env) (closed : ClosedConstantTypes env)
    (annotation operand : WordBinder.Annotation)
    (lhsTyped : CastTyping env 0 (SourceCasts env) ctx lhs (optionType wordType))
    (value : CastTyping env 0 (SourceCasts env) ctx v operand.core)
    (form : ValueForm setup ctx v operand.core)
    (fresh : ∀ r ∈ setup.rules, ``Neg.neg ≠ r.name)
    (freshEq : ∀ r ∈ setup.rules, ``Eq ≠ r.name)
    (freshSome : ∀ r ∈ setup.rules, ``Option.some ≠ r.name) (fuel : Nat) :
    ∃ result, LeanStructuralConversion.prove env setup.basic setup.exposure 0 (fuel+15) ctx
      (equalValues (optionType wordType) lhs (someValue wordType (.app negHeader v)))
      (equalValues (optionType wordType) lhs (someValue wordType (.app (AnnotatedNeg.header annotation) v))) = some result ∧
      result.type = .sort .zero := by
  obtain ⟨converted,done,kind⟩ := AnnotatedNeg.value_proved setup arithmetic closed annotation operand value form fresh (fuel+5)
  have typed := CastTyping.checkedApplication
    (arithmetic.negHeader_typed.mono (fun _ _ _ h => SourceCasts.arithmetic h)) (operand.result value)
  exact expected_value_proved setup arithmetic library closed lhsTyped typed freshEq freshSome fuel
    (by simpa [Nat.add_assoc] using done) kind

/-- A selected scalar may change both the condition annotation and the
result annotation. The unchanged operands are inferred once. -/
theorem select_expected_proved (setup : AliasSetup env) (arithmetic : Arithmetic.Signatures env)
    (library : Signatures env) (decisions : Branch.BooleanLibrary env) (closed : ClosedConstantTypes env)
    (resultAnnotation annotation operand oa ob : WordBinder.Annotation)
    (lhsTyped : CastTyping env 0 (SourceCasts env) ctx lhs (optionType wordType))
    (value : CastTyping env 0 (SourceCasts env) ctx v operand.core) (form : ValueForm setup ctx v operand.core)
    (decisionTyped : CastTyping env 0 (SourceCasts env) ctx d
      (.app (.const ``Decidable []) (AnnotatedCondition.condition annotation v)))
    (decisionForm : ValueForm setup ctx d (.app (.const ``Decidable []) (AnnotatedCondition.condition annotation v)))
    (left : CastTyping env 0 (SourceCasts env) ctx a oa.core) (right : CastTyping env 0 (SourceCasts env) ctx b ob.core)
    (leftForm : ValueForm setup ctx a oa.core) (rightForm : ValueForm setup ctx b ob.core)
    (iteDeclared : env.constants ``ite = some Branch.iteSignature)
    (fresh : ∀ r ∈ setup.rules, ``bne ≠ r.name)
    (freshLiteral : ∀ r ∈ setup.rules, ``OfNat.ofNat ≠ r.name)
    (freshEq : ∀ r ∈ setup.rules, ``Eq ≠ r.name)
    (freshDecision : ∀ r ∈ setup.rules, ``Decidable ≠ r.name)
    (freshIte : ∀ r ∈ setup.rules, ``ite ≠ r.name)
    (freshSome : ∀ r ∈ setup.rules, ``Option.some ≠ r.name) (fuel : Nat) :
    ∃ result, LeanStructuralConversion.prove env setup.basic setup.exposure 0 (fuel+21) ctx
      (equalValues (optionType wordType) lhs (someValue wordType (AnnotatedCondition.choice wordType .word v d a b)))
      (equalValues (optionType wordType) lhs
        (someValue wordType (AnnotatedCondition.choice resultAnnotation.core annotation v d a b))) = some result ∧
      result.type = .sort .zero := by
  have embed : ∀ scope a b, SourceCasts env scope a b → AnnotatedCondition.Casts setup scope a b :=
    fun _ _ _ h => .source h
  obtain ⟨valueEq,hv,tv⟩ := AnnotatedCondition.scalar_choice_proved setup decisions arithmetic closed
    resultAnnotation annotation operand oa ob value form decisionTyped decisionForm left right leftForm rightForm
    iteDeclared fresh freshLiteral freshEq freshDecision freshIte fuel
  have valueTyped := AnnotatedCondition.scalar_choice_typed setup decisions arithmetic annotation operand oa ob
    value form decisionTyped left right iteDeclared fresh freshLiteral freshEq freshDecision
  obtain ⟨fn,hfn,tfn⟩ := LeanStructuralConversion.prove_reflexive_complete library.some_typed
    (setup.basic_no_reduction _ _ rfl rfl freshSome freshSome rfl) (fuel+18) setup.exposure
  obtain ⟨wrapped,hw,tw⟩ := LeanStructuralConversion.prove_application_or_same_complete
    (leftName := ``Option.some) (rightName := ``Option.some) rfl rfl
    (setup.basic_no_reduction _ _ rfl rfl freshSome freshSome rfl)
    (CastTyping.application (library.some_typed.withCasts (AnnotatedCondition.Casts setup)) valueTyped)
    (AnnotatedCondition.Casts.covered setup arithmetic closed (fuel+5)) fn hfn tfn valueEq hv (.inl tv)
  obtain ⟨eqFn,heqFn,teqFn⟩ := LeanStructuralConversion.prove_reflexive_cast_complete
    (prefix_typed library lhsTyped)
    (setup.basic_no_reduction _ _ rfl rfl freshEq freshEq rfl)
    (setup.covers_source_recursive arithmetic closed (fuel+15))
  obtain ⟨result,done,kind⟩ := LeanStructuralConversion.prove_application_or_same_complete
    (leftName := ``Eq) (rightName := ``Eq) rfl rfl
    (setup.basic_no_reduction _ _ rfl rfl freshEq freshEq rfl)
    (expected_typed library (lhsTyped.mono embed) (.exact valueTyped))
    (AnnotatedCondition.Casts.covered setup arithmetic closed (fuel+6)) eqFn heqFn teqFn wrapped hw (.inl tw)
  exact ⟨result,done,kind⟩

/-- Only the explicit lexical transport adds a proof-side conversion. The
source-expression typing remains the ordinary arithmetic typing relation. -/
inductive Casts (setup : AliasSetup env) : TypeCasts where
  | condition (cast : AnnotatedCondition.Casts setup ctx a b) : Casts setup ctx a b
  | selectAnnotation (resultAnnotation : WordBinder.Annotation)
      (premises : AnnotatedCondition.ScalarConditions setup ctx v d a b annotation)
      (lhsTyped : CastTyping env 0 (SourceCasts env) ctx lhs (optionType wordType)) :
      Casts setup ctx
        (equalValues (optionType wordType) lhs (someValue wordType (AnnotatedCondition.choice wordType .word v d a b)))
        (equalValues (optionType wordType) lhs (someValue wordType (AnnotatedCondition.choice resultAnnotation.core annotation v d a b)))
  | source : SourceCasts env ctx a b → Casts setup ctx a b
  | beta {body arg lhs : VExpr} (annotation resultAnnotation : WordBinder.Annotation)
      (left : CastTyping env 0 (SourceCasts env) ctx lhs (optionType wordType))
      (bodyTyped : CastTyping env 0 (SourceCasts env) (annotation.core::ctx) body resultAnnotation.core)
      (argTyped : CheckedTyping env 0 (SourceCasts env) ctx arg annotation.core)
      (form : ∃ actual : WordBinder.Annotation, ValueForm setup ctx (body.inst arg) actual.core) :
      Casts setup ctx (equalValues (optionType wordType) lhs (someValue wordType (body.inst arg)))
        (equalValues (optionType wordType) lhs (someValue wordType (.app (.lam annotation.core body) arg)))
  | binaryAnnotation (op : Binary) (a b c d oa ob : WordBinder.Annotation)
      (leftValue : CastTyping env 0 (SourceCasts env) ctx lhs (optionType wordType))
      (left : CastTyping env 0 (SourceCasts env) ctx u oa.core)
      (right : CastTyping env 0 (SourceCasts env) ctx v ob.core)
      (leftForm : ValueForm setup ctx u oa.core) (rightForm : ValueForm setup ctx v ob.core)
      (fresh : ∀ r ∈ setup.rules, op.method ≠ r.name) :
      Casts setup ctx
        (equalValues (optionType wordType) lhs (someValue wordType (.app (.app op.header u) v)))
        (equalValues (optionType wordType) lhs
          (someValue wordType (.app (.app (AnnotatedBinary.header op a b c d) u) v)))
  | negAnnotation (annotation operand : WordBinder.Annotation)
      (lhsValue : CastTyping env 0 (SourceCasts env) ctx lhs (optionType wordType))
      (value : CastTyping env 0 (SourceCasts env) ctx v operand.core)
      (form : ValueForm setup ctx v operand.core)
      (fresh : ∀ r ∈ setup.rules, ``Neg.neg ≠ r.name) :
      Casts setup ctx (equalValues (optionType wordType) lhs (someValue wordType (.app negHeader v)))
        (equalValues (optionType wordType) lhs (someValue wordType (.app (AnnotatedNeg.header annotation) v)))

instance : Arithmetic.Includes (Casts setup) := ⟨fun _ _ _ h => .source (.arithmetic h)⟩

theorem Casts.covered (setup : AliasSetup env) (arithmetic : Arithmetic.Signatures env)
    (library : Signatures env) (closed : ClosedConstantTypes env)
    (freshEq : ∀ r ∈ setup.rules, ``Eq ≠ r.name)
    (freshSome : ∀ r ∈ setup.rules, ``Option.some ≠ r.name) :
    Conversion.Covers setup.conversion 0 (Casts setup) := by
  intro ctx actual expected cast
  cases cast with
  | condition h => exact AnnotatedCondition.Casts.covered_top setup arithmetic closed ctx actual expected h
  | selectAnnotation resultAnnotation h lhs =>
    obtain ⟨eq,he,te⟩ := select_expected_proved setup arithmetic library h.library closed
      resultAnnotation _ h.operand h.leftAnnotation h.rightAnnotation lhs h.value h.form h.decisionTyped h.decisionForm
      h.left h.right h.leftForm h.rightForm h.iteDeclared h.fresh h.freshLiteral freshEq h.freshDecision h.freshIte freshSome 43
    exact LeanStructuralConversion.conversion_of_prove eq he te
  | source h => exact setup.covers_source arithmetic closed ctx actual expected h
  | beta annotation resultAnnotation left bodyTyped argTyped form =>
    obtain ⟨result,success,kind⟩ := beta_expected_proved setup arithmetic library closed
      annotation resultAnnotation left bodyTyped argTyped form freshEq freshSome 57
    exact LeanStructuralConversion.conversion_of_prove result success kind
  | binaryAnnotation op a b c d oa ob lhs left right leftForm rightForm fresh =>
    obtain ⟨result,success,kind⟩ := binary_expected_proved setup arithmetic library closed
      op a b c d oa ob lhs left right leftForm rightForm fresh freshEq freshSome 49
    exact LeanStructuralConversion.conversion_of_prove result success kind
  | negAnnotation annotation operand lhs value form fresh =>
    obtain ⟨result,success,kind⟩ := neg_expected_proved setup arithmetic library closed
      annotation operand lhs value form fresh freshEq freshSome 49
    exact LeanStructuralConversion.conversion_of_prove result success kind

theorem annotated_binary_finish (setup : AliasSetup env) (inputs : InputsTyped env ctx p)
    (arithmetic : Arithmetic.Signatures env) (library : Signatures env)
    {leftPiece : Piece env ctx p u scalarExpected} {rightPiece : Piece env ctx p v scalarExpected}
    (left : ScalarCasts inputs leftPiece (SourceCasts env) (Casts setup))
    (right : ScalarCasts inputs rightPiece (SourceCasts env) (Casts setup))
    (op : Binary) (a b c d oa ob : WordBinder.Annotation)
    (leftTyped : CastTyping env 0 (SourceCasts env) ctx left.sourceCore.val oa.core)
    (rightTyped : CastTyping env 0 (SourceCasts env) ctx right.sourceCore.val ob.core)
    (leftForm : ValueForm setup ctx left.sourceCore.val oa.core)
    (rightForm : ValueForm setup ctx right.sourceCore.val ob.core)
    (fresh : ∀ r ∈ setup.rules, op.method ≠ r.name)
    (registered : env.constants op.fact = some ⟨0,op.signature⟩)
    (constructor : env.constants op.target = some ⟨0,.forallE exprType (.forallE exprType exprType)⟩)
    (coverage : Conversion.Covers conv 0 (Casts setup)) (exposure : Exposure env) :
    ∃ result, finish env conv exposure ctx
      (scalarExpected p (app op.target [leftPiece.code,rightPiece.code])
        (Lean.mkApp2 (AnnotatedBinary.nativeHeader op a b c d) u v))
      (app op.target [leftPiece.code,rightPiece.code])
      (app op.fact ([leftPiece.code,rightPiece.code] ++ p.args ++
        [u,v,leftPiece.checked.proof,rightPiece.checked.proof]))
      (leftPiece.checked.known.orElse rightPiece.checked.known) = some result ∧
      CastTyping env 0 (Casts setup) ctx result.proofCore.val result.core.val ∧
      result.code = app op.target [leftPiece.code,rightPiece.code] := by
  have embeds : ∀ scope x y, SourceCasts env scope x y → Casts setup scope x y := fun _ _ _ h => .source h
  have targetRep := app_represents (f := Lean.Expr.const op.target []) (.constant rfl)
    (.cons leftPiece.represented.property (.cons rightPiece.represented.property .nil))
  have sourceRep := Represents.app (Represents.app (AnnotatedBinary.represented op a b c d)
    left.sourceCore.property) right.sourceCore.property
  have proofRep := app_represents (f := Lean.Expr.const op.fact []) (.constant rfl)
    (.cons leftPiece.represented.property (.cons rightPiece.represented.property
      (.cons inputs.i.property (.cons inputs.x.property (.cons inputs.y.property
        (.cons inputs.s.property (.cons inputs.ls.property (.cons left.sourceCore.property
          (.cons right.sourceCore.property (.cons leftPiece.checked.proofCore.property
            (.cons rightPiece.checked.proofCore.property .nil)))))))))))
  have target : CastTyping env 0 (SourceCasts env) ctx
      (applications (.const op.target []) [leftPiece.represented.val,rightPiece.represented.val]) exprType := by
    -- The code type is not required separately: its evaluation is typed from
    -- the two source-independent quotation typings and the constructor below.
    have fact : CastTyping env 0 (SourceCasts env) ctx (.const op.target [])
        (.forallE exprType (.forallE exprType exprType)) :=
      .constant constructor (by simp) rfl
    exact .application (.application fact left.target) right.target
  have lhs := eval_typed library inputs target
  have value := AnnotatedBinary.value_typed arithmetic op a b c d left.value right.value
  exact finish_checked_complete (scalarExpected_represents inputs targetRep sourceRep) proofRep
    (.converted (binary_typed inputs (left.inProofCasts embeds) (right.inProofCasts embeds) op registered)
      (.binaryAnnotation op a b c d oa ob lhs leftTyped rightTyped leftForm rightForm fresh))
    ((expected_typed library lhs value).mono embeds)
    ((known_casts leftPiece.checked left.proof).orElse (known_casts rightPiece.checked right.proof)) coverage exposure _

theorem annotated_neg_finish (setup : AliasSetup env) (inputs : InputsTyped env ctx p)
    (arithmetic : Arithmetic.Signatures env) (library : Signatures env)
    {a : Piece env ctx p v scalarExpected} (value : ScalarCasts inputs a (SourceCasts env) (Casts setup))
    (annotation operand : WordBinder.Annotation)
    (valueTyped : CastTyping env 0 (SourceCasts env) ctx value.sourceCore.val operand.core)
    (form : ValueForm setup ctx value.sourceCore.val operand.core)
    (fresh : ∀ r ∈ setup.rules, ``Neg.neg ≠ r.name)
    (registered : env.constants ``WordFrontendFacts.neg = some ⟨0,negSignature⟩)
    (constructor : env.constants ``HybridWord.Expr.neg = some ⟨0,.forallE exprType exprType⟩)
    (coverage : Conversion.Covers conv 0 (Casts setup)) (exposure : Exposure env) :
    ∃ result, finish env conv exposure ctx
      (scalarExpected p (app ``HybridWord.Expr.neg [a.code]) (.app (AnnotatedNeg.nativeHeader annotation) v))
      (app ``HybridWord.Expr.neg [a.code])
      (app ``WordFrontendFacts.neg ([a.code] ++ p.args ++ [v,a.checked.proof])) a.checked.known = some result ∧
      CastTyping env 0 (Casts setup) ctx result.proofCore.val result.core.val ∧
      result.code = app ``HybridWord.Expr.neg [a.code] := by
  have embeds : ∀ scope x y, SourceCasts env scope x y → Casts setup scope x y := fun _ _ _ h => .source h
  have targetRep := app_represents (f := Lean.Expr.const ``HybridWord.Expr.neg []) (.constant rfl)
    (.cons a.represented.property .nil)
  have sourceRep := Represents.app (AnnotatedNeg.represented annotation) value.sourceCore.property
  have proofRep := app_represents (f := Lean.Expr.const ``WordFrontendFacts.neg []) (.constant rfl)
    (.cons a.represented.property (.cons inputs.i.property (.cons inputs.x.property (.cons inputs.y.property
      (.cons inputs.s.property (.cons inputs.ls.property (.cons value.sourceCore.property
        (.cons a.checked.proofCore.property .nil))))))))
  have fact : CastTyping env 0 (SourceCasts env) ctx (.const ``HybridWord.Expr.neg []) (.forallE exprType exprType) :=
    .constant constructor (by simp) rfl
  have target := CastTyping.application fact value.target
  have lhs := eval_typed library inputs target
  exact finish_checked_complete (scalarExpected_represents inputs targetRep sourceRep) proofRep
    (.converted (neg_typed inputs (value.inProofCasts embeds) registered)
      (.negAnnotation annotation operand lhs valueTyped form fresh))
    ((expected_typed library lhs (AnnotatedNeg.value_typed arithmetic annotation value.value)).mono embeds)
    (known_casts a.checked value.proof) coverage exposure _

/-- Compose the already parsed body with its original lexical let. This
returns an exact-type proof term, so later cached uses keep the same invariant. -/
theorem lexical_finish_complete {body arg : VExpr}
    (annotation resultAnnotation : WordBinder.Annotation) (setup : AliasSetup env) (arithmetic : Arithmetic.Signatures env) (library : Signatures env) (inputs : InputsTyped env ctx p)
    {piece : Piece env ctx p reduced scalarExpected}
    (child : ScalarCasts inputs piece (SourceCasts env) (Casts setup))
    (bodyTyped : CastTyping env 0 (SourceCasts env) (annotation.core::ctx) body resultAnnotation.core)
    (argTyped : CheckedTyping env 0 (SourceCasts env) ctx arg annotation.core)
    (reducedRep : Represents reduced (body.inst arg))
    (form : ∃ actual : WordBinder.Annotation, ValueForm setup ctx (body.inst arg) actual.core)
    (sourceRep : Represents source (.app (.lam annotation.core body) arg))
    (coverage : Conversion.Covers conv 0 (Casts setup)) :
    ∃ result, piece.checked.retarget conv
        (scalarExpected p piece.code source) = some result ∧
      Nonempty (ScalarCasts inputs
        (⟨piece.code,result,piece.closed,piece.represented⟩ :
          Piece env ctx p source scalarExpected) (SourceCasts env) (Casts setup)) := by
  have lhsTyped := eval_typed (casts := SourceCasts env) library inputs child.target
  have sourceTyped : CheckedTyping env 0 (SourceCasts env) ctx (.app (.lam annotation.core body) arg) wordType := by
    apply resultAnnotation.result
    have applied := CastTyping.checkedApplication (.lambda ((annotation.type_typed arithmetic).withCasts _) bodyTyped) argTyped
    simpa only [resultAnnotation.closed.instN_eq (Nat.zero_le _)] using applied
  have newRep := sourceRep
  have expectedRep := scalarExpected_represents inputs piece.represented.property newRep
  have actualRep := scalarExpected_represents inputs piece.represented.property reducedRep
  have actualSame := piece.checked.core.property.unique actualRep
  have rule : Casts setup ctx piece.checked.core.val
      (equalValues (optionType wordType)
        (scalarValue inputs.i.val inputs.x.val inputs.y.val inputs.s.val inputs.ls.val piece.represented.val)
        (someValue wordType (.app (.lam annotation.core body) arg))) := by
    rw [actualSame]
    exact .beta annotation resultAnnotation lhsTyped bodyTyped argTyped form
  have newTyped := expected_typed (casts := SourceCasts env) library lhsTyped
    sourceTyped
  obtain ⟨result,success,proofTyped⟩ := ScalarEnvironment.retarget_cast_complete piece.checked expectedRep
    child.proof (newTyped.mono (fun _ _ _ h => Casts.source h)) rule coverage
  exact ⟨result,success,⟨⟨⟨_,newRep⟩,sourceTyped,child.target,proofTyped⟩⟩⟩

/-- Lexical-let recursion composes the two immediate syntax children. No
traversal of the substituted body is requested by this theorem or by `visit`. -/
theorem let_visit_complete_code {body : VExpr} (annotation resultAnnotation : WordBinder.Annotation) (setup : AliasSetup env) (arithmetic : Arithmetic.Signatures env) (library : Signatures env)
    (inputs : InputsTyped env ctx p) (bindings : ScalarEnvironment.Bindings env ctx p)
    {valuePiece : Piece env ctx p (ScalarEnvironment.materialize bindings value) scalarExpected}
    (valueTyped : ScalarCasts inputs valuePiece (SourceCasts env) (Casts setup))
    {nextPiece : Piece env ctx p
      (ScalarEnvironment.materialize (⟨ScalarEnvironment.materialize bindings value,valuePiece⟩ :: bindings) next)
      scalarExpected}
    (nextTyped : ScalarCasts inputs nextPiece (SourceCasts env) (Casts setup))
    (bodyRep : Represents (LeanBindings.substitute (LeanBindings.underSubst (ScalarEnvironment.reference bindings)) next) body)
    (bodyTyped : CastTyping env 0 (SourceCasts env) (annotation.core::ctx) body resultAnnotation.core)
    (form : ∃ actual : WordBinder.Annotation, ValueForm setup ctx (body.inst valueTyped.sourceCore.val) actual.core)
    (coverage : Conversion.Covers conv 0 (Casts setup)) (exposure : Exposure env)
    (valueParsed : ScalarEnvironment.visit env conv exposure ctx p value bindings = some valuePiece)
    (nextParsed : ScalarEnvironment.visit env conv exposure ctx p next
      (⟨ScalarEnvironment.materialize bindings value,valuePiece⟩ :: bindings) = some nextPiece)
    (binder : Lean.Name) (flag : Bool) :
    ∃ piece, ScalarEnvironment.visit env conv exposure ctx p (.letE binder annotation.native value next flag) bindings = some piece ∧
      Nonempty (ScalarCasts inputs piece (SourceCasts env) (Casts setup)) ∧ piece.code = nextPiece.code := by
  have reducedRep : Represents
      (ScalarEnvironment.materialize (⟨ScalarEnvironment.materialize bindings value,valuePiece⟩ :: bindings) next)
      (body.inst valueTyped.sourceCore.val) := by
    rw [ScalarEnvironment.materialize_cons]
    exact bodyRep.instantiate valueTyped.sourceCore.property
  have materialized : ScalarEnvironment.materialize bindings (.letE binder annotation.native value next flag) =
      .letE binder annotation.native (ScalarEnvironment.materialize bindings value)
        (LeanBindings.substitute (LeanBindings.underSubst (ScalarEnvironment.reference bindings)) next) flag := by
    simp only [ScalarEnvironment.materialize_eq_substitute,LeanBindings.substitute]
    rw [annotation.substitute_native]
  have sourceRep : Represents
      (ScalarEnvironment.materialize bindings (.letE binder annotation.native value next flag))
      (.app (.lam annotation.core body) valueTyped.sourceCore.val) := by
    rw [materialized]
    exact .letE annotation.represented valueTyped.sourceCore.property bodyRep
  obtain ⟨result,checked,typed⟩ := lexical_finish_complete annotation resultAnnotation setup arithmetic library inputs nextTyped
    bodyTyped (annotation.argument valueTyped.value) reducedRep form sourceRep coverage
  refine ⟨⟨nextPiece.code,result,nextPiece.closed,nextPiece.represented⟩,?_,typed,rfl⟩
  rw [ScalarEnvironment.visit]
  simp only [valueParsed,nextParsed,checked,bind,Option.bind,pure,Option.pure_def]

theorem let_visit_complete {body : VExpr} (annotation resultAnnotation : WordBinder.Annotation) (setup : AliasSetup env) (arithmetic : Arithmetic.Signatures env) (library : Signatures env)
    (inputs : InputsTyped env ctx p) (bindings : ScalarEnvironment.Bindings env ctx p)
    {valuePiece : Piece env ctx p (ScalarEnvironment.materialize bindings value) scalarExpected}
    (valueTyped : ScalarCasts inputs valuePiece (SourceCasts env) (Casts setup))
    {nextPiece : Piece env ctx p
      (ScalarEnvironment.materialize (⟨ScalarEnvironment.materialize bindings value,valuePiece⟩ :: bindings) next)
      scalarExpected}
    (nextTyped : ScalarCasts inputs nextPiece (SourceCasts env) (Casts setup))
    (bodyRep : Represents (LeanBindings.substitute (LeanBindings.underSubst (ScalarEnvironment.reference bindings)) next) body)
    (bodyTyped : CastTyping env 0 (SourceCasts env) (annotation.core::ctx) body resultAnnotation.core)
    (form : ∃ actual : WordBinder.Annotation, ValueForm setup ctx (body.inst valueTyped.sourceCore.val) actual.core)
    (coverage : Conversion.Covers conv 0 (Casts setup)) (exposure : Exposure env)
    (valueParsed : ScalarEnvironment.visit env conv exposure ctx p value bindings = some valuePiece)
    (nextParsed : ScalarEnvironment.visit env conv exposure ctx p next
      (⟨ScalarEnvironment.materialize bindings value,valuePiece⟩ :: bindings) = some nextPiece)
    (binder : Lean.Name) (flag : Bool) :
    ∃ piece, ScalarEnvironment.visit env conv exposure ctx p (.letE binder annotation.native value next flag) bindings = some piece ∧
      Nonempty (ScalarCasts inputs piece (SourceCasts env) (Casts setup)) := by
  obtain ⟨piece,parsed,typed,_⟩ := let_visit_complete_code annotation resultAnnotation setup arithmetic library
    inputs bindings valueTyped nextTyped bodyRep bodyTyped form coverage exposure valueParsed nextParsed binder flag
  exact ⟨piece,parsed,typed⟩

/-- The corresponding administrative beta node also descends only into its two syntax children. -/
theorem beta_visit_complete_code {body : VExpr} (annotation resultAnnotation : WordBinder.Annotation) (setup : AliasSetup env) (arithmetic : Arithmetic.Signatures env) (library : Signatures env)
    (inputs : InputsTyped env ctx p) (bindings : ScalarEnvironment.Bindings env ctx p)
    {valuePiece : Piece env ctx p (ScalarEnvironment.materialize bindings value) scalarExpected}
    (valueTyped : ScalarCasts inputs valuePiece (SourceCasts env) (Casts setup))
    {nextPiece : Piece env ctx p
      (ScalarEnvironment.materialize (⟨ScalarEnvironment.materialize bindings value,valuePiece⟩ :: bindings) next)
      scalarExpected}
    (nextTyped : ScalarCasts inputs nextPiece (SourceCasts env) (Casts setup))
    (bodyRep : Represents (LeanBindings.substitute (LeanBindings.underSubst (ScalarEnvironment.reference bindings)) next) body)
    (bodyTyped : CastTyping env 0 (SourceCasts env) (annotation.core::ctx) body resultAnnotation.core)
    (form : ∃ actual : WordBinder.Annotation, ValueForm setup ctx (body.inst valueTyped.sourceCore.val) actual.core)
    (coverage : Conversion.Covers conv 0 (Casts setup)) (exposure : Exposure env)
    (valueParsed : ScalarEnvironment.visit env conv exposure ctx p value bindings = some valuePiece)
    (nextParsed : ScalarEnvironment.visit env conv exposure ctx p next
      (⟨ScalarEnvironment.materialize bindings value,valuePiece⟩ :: bindings) = some nextPiece)
    (binder : Lean.Name) (info : Lean.BinderInfo) :
    ∃ piece, ScalarEnvironment.visit env conv exposure ctx p (.app (.lam binder annotation.native next info) value) bindings = some piece ∧
      Nonempty (ScalarCasts inputs piece (SourceCasts env) (Casts setup)) ∧ piece.code = nextPiece.code := by
  have reducedRep : Represents
      (ScalarEnvironment.materialize (⟨ScalarEnvironment.materialize bindings value,valuePiece⟩ :: bindings) next)
      (body.inst valueTyped.sourceCore.val) := by
    rw [ScalarEnvironment.materialize_cons]
    exact bodyRep.instantiate valueTyped.sourceCore.property
  have materialized : ScalarEnvironment.materialize bindings (.app (.lam binder annotation.native next info) value) =
      .app (.lam binder annotation.native
        (LeanBindings.substitute (LeanBindings.underSubst (ScalarEnvironment.reference bindings)) next) info)
        (ScalarEnvironment.materialize bindings value) := by
    simp only [ScalarEnvironment.materialize_eq_substitute,LeanBindings.substitute]
    rw [annotation.substitute_native]
  have sourceRep : Represents
      (ScalarEnvironment.materialize bindings (.app (.lam binder annotation.native next info) value))
      (.app (.lam annotation.core body) valueTyped.sourceCore.val) := by
    rw [materialized]
    exact .app (.lam annotation.represented bodyRep) valueTyped.sourceCore.property
  obtain ⟨result,checked,typed⟩ := lexical_finish_complete annotation resultAnnotation setup arithmetic library inputs nextTyped
    bodyTyped (annotation.argument valueTyped.value) reducedRep form sourceRep coverage
  refine ⟨⟨nextPiece.code,result,nextPiece.closed,nextPiece.represented⟩,?_,typed,rfl⟩
  rw [ScalarEnvironment.visit]
  simp only [valueParsed,nextParsed,checked,bind,Option.bind,pure,Option.pure_def]

theorem beta_visit_complete {body : VExpr} (annotation resultAnnotation : WordBinder.Annotation) (setup : AliasSetup env) (arithmetic : Arithmetic.Signatures env) (library : Signatures env)
    (inputs : InputsTyped env ctx p) (bindings : ScalarEnvironment.Bindings env ctx p)
    {valuePiece : Piece env ctx p (ScalarEnvironment.materialize bindings value) scalarExpected}
    (valueTyped : ScalarCasts inputs valuePiece (SourceCasts env) (Casts setup))
    {nextPiece : Piece env ctx p
      (ScalarEnvironment.materialize (⟨ScalarEnvironment.materialize bindings value,valuePiece⟩ :: bindings) next)
      scalarExpected}
    (nextTyped : ScalarCasts inputs nextPiece (SourceCasts env) (Casts setup))
    (bodyRep : Represents (LeanBindings.substitute (LeanBindings.underSubst (ScalarEnvironment.reference bindings)) next) body)
    (bodyTyped : CastTyping env 0 (SourceCasts env) (annotation.core::ctx) body resultAnnotation.core)
    (form : ∃ actual : WordBinder.Annotation, ValueForm setup ctx (body.inst valueTyped.sourceCore.val) actual.core)
    (coverage : Conversion.Covers conv 0 (Casts setup)) (exposure : Exposure env)
    (valueParsed : ScalarEnvironment.visit env conv exposure ctx p value bindings = some valuePiece)
    (nextParsed : ScalarEnvironment.visit env conv exposure ctx p next
      (⟨ScalarEnvironment.materialize bindings value,valuePiece⟩ :: bindings) = some nextPiece)
    (binder : Lean.Name) (info : Lean.BinderInfo) :
    ∃ piece, ScalarEnvironment.visit env conv exposure ctx p (.app (.lam binder annotation.native next info) value) bindings = some piece ∧
      Nonempty (ScalarCasts inputs piece (SourceCasts env) (Casts setup)) := by
  obtain ⟨piece,parsed,typed,_⟩ := beta_visit_complete_code annotation resultAnnotation setup arithmetic library
    inputs bindings valueTyped nextTyped bodyRep bodyTyped form coverage exposure valueParsed nextParsed binder info
  exact ⟨piece,parsed,typed⟩

end IRComparison.WordFrontend.ScalarConversion
