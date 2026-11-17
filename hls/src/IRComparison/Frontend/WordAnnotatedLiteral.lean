import IRComparison.Frontend.WordBinder

/-! Numeral annotations emitted by Lean: Word and BitVec 32. The numeral's
spelling is retained in the generated code/certificate; only its fixed type
alias is converted. There is no evaluation/normalization of arbitrary terms. -/
namespace IRComparison.WordFrontend.AnnotatedLiteral
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic ScalarEnvironment ScalarSyntax
set_option maxHeartbeats 1800000

def native (annotation : WordBinder.Annotation) (n : Nat) : Lean.Expr :=
  Lean.mkApp3 (.const ``OfNat.ofNat [.zero]) annotation.native (.lit (.natVal n))
    (app ``BitVec.instOfNat [nativeWidth,.lit (.natVal n)])
def core (annotation : WordBinder.Annotation) (n : Nat) : VExpr :=
  applications (.const ``OfNat.ofNat [.zero])
    [annotation.core,numeral n,applications (.const ``BitVec.instOfNat []) [width,numeral n]]

theorem represented (annotation : WordBinder.Annotation) (n : Nat) :
    Represents (native annotation n) (core annotation n) :=
  .app (.app (.app (.constant rfl) annotation.represented) .natural)
    (.app (.app (.constant rfl) width_represents) .natural)

theorem closed (annotation : WordBinder.Annotation) (n : Nat) :
    isClosed (native annotation n) = true := by cases annotation <;> rfl

theorem annotation_typed (library : Signatures env) (annotation : WordBinder.Annotation) (n : Nat) :
    CastTyping env 0 (SourceCasts env) ctx (core annotation n) annotation.core := by
  cases annotation with
  | word => exact (library.literal_typed n).mono (fun _ _ _ h => .arithmetic h)
  | bitvec =>
    have bc : bitvecType.ClosedN 0 := WordBinder.Annotation.closed .bitvec
    have nt := library.literals.numeral_typed (ctx := ctx) (U := 0) n
    have dictionary : DirectTyping env 0 ctx (.const ``BitVec.instOfNat []) bitvecOfNatSignature :=
      .constant library.bitvecOfNat (by simp) rfl
    have d1 := DirectTyping.application dictionary library.width_typed
    simp only [bitvecOfNatSignature,natType,applications,VExpr.inst,Nat.reduceAdd,
      VExpr.instVar_succ,VExpr.instVar_zero,VExpr.instVar_lower] at d1
    have d2 := DirectTyping.application d1 nt
    simp only [VExpr.inst,VExpr.inst_lift,VExpr.instVar_zero] at d2
    have method : CastTyping env 0 (SourceCasts env) ctx (.const ``OfNat.ofNat [.zero])
        (.forallE (.sort (.succ .zero)) (.forallE natType
          (.forallE (applications (.const ``OfNat [.zero]) [.bvar 1,.bvar 0]) (.bvar 2)))) :=
      .constant library.ofNat (by simp [VLevel.WF]) rfl
    have a1 := CastTyping.application method (library.bitvec_typed.withCasts (SourceCasts env))
    simp only [natType,applications,VExpr.inst,Nat.reduceAdd,VExpr.instVar_lower,
      VExpr.instVar_zero,VExpr.instVar_succ,
      bc.lift_eq] at a1
    have a2 := CastTyping.application a1 (nt.withCasts (SourceCasts env))
    simp only [VExpr.inst,VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ,
      bc.lift_eq,bc.instN_eq (Nat.zero_le _)] at a2
    simpa only [bc.instN_eq (Nat.zero_le _)] using CastTyping.application a2 (d2.withCasts (SourceCasts env))

theorem typed (library : Signatures env) (annotation : WordBinder.Annotation) (n : Nat) :
    CheckedTyping env 0 (SourceCasts env) ctx (core annotation n) wordType :=
  annotation.result (annotation_typed library annotation n)

/-- The ordinary literal fact accepts the actual source numeral, including
its annotation. No canonical replacement expression is used as the input. -/
theorem fact_typed (inputs : InputsTyped env ctx p)
    (value : CheckedTyping env 0 (SourceCasts env) ctx raw wordType)
    (registered : env.constants ``WordFrontendFacts.literal = some ⟨0,literalSignature⟩) :
    CastTyping env 0 (SourceCasts env) ctx
      (applications (.const ``WordFrontendFacts.literal []) (raw :: inputs.args))
      (equalValues (optionType wordType)
        (scalarValue inputs.i.val inputs.x.val inputs.y.val inputs.s.val inputs.ls.val
          (.app (.const ``HybridWord.Expr.lit []) raw))
        (someValue wordType raw)) := by
  have fact : CastTyping env 0 (SourceCasts env) ctx (.const ``WordFrontendFacts.literal []) literalSignature :=
    .constant registered (by simp) rfl
  have first := CastTyping.checkedApplication fact value
  simp only [literalSignature,inputsType,wordType,stateType,wordsType,VExpr.inst] at first
  simpa only [InputsTyped.instantiate,scalarValue,equalValues,optionType,wordType,someValue,applications,
    Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst_lift,VExpr.inst,VExpr.instVar_lower,
    VExpr.instVar_zero,VExpr.instVar_succ] using inputs.apply_casts first

theorem visit_complete (inputs : InputsTyped env ctx p) (library : ScalarSyntax.Library env)
    (annotation : WordBinder.Annotation) (n : Nat)
    (embeds : ∀ scope a b, SourceCasts env scope a b → proofCasts scope a b)
    (coverage : Conversion.Covers conv 0 proofCasts) (exposure : Exposure env)
    (scope : Separated p (native annotation n)) :
    ∃ piece, visit env conv exposure ctx p (native annotation n) bindings = some piece ∧
      Nonempty (ScalarCasts inputs piece (SourceCasts env) proofCasts) ∧
      piece.code = app ``HybridWord.Expr.lit [native annotation n] := by
  have mat : materialize bindings (native annotation n) = native annotation n :=
    materialize_closed bindings (closed annotation n)
  have rep := represented annotation n
  have value := typed (ctx := ctx) library.toSignatures annotation n
  obtain ⟨translated,translation,same⟩ := rep.translate_complete
  let literal : ClosedTerm := ⟨native annotation n,closed annotation n,translated⟩
  let code := ClosedTerm.app ``HybridWord.Expr.lit [literal]
  have targetRep : Represents code.val (.app (.const ``HybridWord.Expr.lit []) (core annotation n)) :=
    .app (.constant rfl) rep
  have proofRep := app_represents (f := Lean.Expr.const ``WordFrontendFacts.literal []) (.constant rfl)
    (.cons rep inputs.arguments)
  obtain ⟨artifact,checked,proofTyped,_,_⟩ := finish_cast_complete
    (scalarExpected_represents inputs targetRep rep) proofRep
    ((fact_typed inputs value library.literalFact).mono embeds)
    (known := noKnownTypes env 0) (by intro _ _ _ h; cases h) coverage exposure code.val
  let art : Artifact env ctx (scalarExpected p code.val (materialize bindings (native annotation n))) :=
    mat.symm ▸ artifact
  let piece : Piece env ctx p (materialize bindings (native annotation n)) scalarExpected :=
    ⟨code.val,art,code.closed,code.represented⟩
  have literalClosed : closedTerm (native annotation n) = some literal := by
    simp only [closedTerm,closed,translation,literal,bind,Option.bind,dite_true,pure]
  refine ⟨piece,?_,⟨⟨⟨_,mat.symm ▸ rep⟩,value,?_,?_⟩⟩,rfl⟩
  · rw [visit] <;> try (solve | intro name ty value next flag h; cases h)
    have miss : lookup conv (native annotation n) bindings = none := rfl
    simp only [miss,node,finishScalar,mat]
    have head : (native annotation n).getAppFn.constName? = some ``OfNat.ofNat := rfl
    simp only [head]
    simp [List.forIn_cons,scope.index,scope.left,scope.right,scope.locals,
      literalClosed,ClosedTerm.app,app,literal,code,piece,art,mat] at checked ⊢
    simp only [forIn_constant_yield,Option.some.injEq,checked,Option.bind_some]
    cases bindings <;> cases annotation <;>
      simp [materialize,LeanBindings.substitute,native,WordBinder.Annotation.native,nativeWidth,word,
        Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB,app] at checked ⊢
    all_goals simp [checked]
  · have fact : CastTyping env 0 (SourceCasts env) ctx (.const ``HybridWord.Expr.lit []) (.forallE wordType exprType) :=
      .constant library.literalConstructor (by simp) rfl
    change CastTyping env 0 (SourceCasts env) ctx (.app (.const ``HybridWord.Expr.lit []) translated.val) exprType
    rw [same]
    exact .checkedApplication fact value
  · cases bindings <;> cases annotation <;>
      simpa [piece,art,materialize,LeanBindings.substitute,native,WordBinder.Annotation.native,nativeWidth,word,
        Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB,app] using proofTyped

end IRComparison.WordFrontend.AnnotatedLiteral
