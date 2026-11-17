import IRComparison.Frontend.WordAnnotatedLet
import IRComparison.Frontend.WordStructuralReadBind

namespace IRComparison.WordFrontend.WordBinder
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic StructuralBody
set_option maxHeartbeats 1200000

/-- This is a compositional rule; its recursive premise is discharged by
source-syntax induction, rather than supplied to the exported theorem. -/
theorem step_let_certificate (annotation : Annotation) (setup : AliasSetup env)
    (library : Signatures env) (inputs : InputsTyped env ctx p) (closed : ClosedConstantTypes env)
    (consDeclared : env.constants ``List.cons = some consSignature)
    (steps : Step.Signatures env)
    (eqDeclared : env.constants ``Eq = some eqSignature)
    (evalDeclared : env.constants ``HybridWord.Cmd.eval = some ⟨0,evalSignature⟩)
    (factDeclared : env.constants ``WordLoopFacts.letValue = some ⟨0,StructuralReadBind.letValueSignature⟩)
    (constructor : env.constants ``HybridWord.Cmd.letValue = some ⟨0,bindValueConstructor⟩)
    (optionFresh : ∀ r ∈ setup.rules, ``Option ≠ r.name)
    (coverage : Conversion.Covers setup.conversion 0 (For.Casts setup))
    (exposure : Exposure env)
    {a : Piece env ctx p first scalarExpected}
    (left : ScalarCasts inputs a (SourceCasts env) (For.Casts setup))
    {b : Piece env (annotation.core::ctx) {p.lift with locals := .bvar 0::p.lift.locals} nextBody Mode.step.expected}
    (right : StructuralLoop.StepCasts (annotation.nextInputs inputs closed library consDeclared) b (SourceCasts env) (For.Casts setup))
    (form : ValueForm setup (annotation.core::ctx) right.sourceCore.val (optionType Step.stepState))
    (binder : Lean.Name) (flag : Bool) :
    ∃ artifact, finish env setup.conversion exposure ctx
      (Mode.step.expected p (app ``HybridWord.Cmd.letValue [a.code,b.code]) (letSource annotation binder first nextBody flag))
      (app ``HybridWord.Cmd.letValue [a.code,b.code])
      (app ``WordLoopFacts.letValue ([a.code,b.code] ++ p.args ++
        [first,.lam binder annotation.native nextBody .default,a.checked.proof,
          .lam binder annotation.native b.checked.proof .default]))
      (a.checked.known.orElse b.checked.known) = some artifact ∧
      ∃ typed : StructuralLoop.StepCasts inputs
        (⟨_,artifact,(ClosedTerm.app ``HybridWord.Cmd.letValue [a.closedTerm,b.closedTerm]).closed,
          (ClosedTerm.app ``HybridWord.Cmd.letValue [a.closedTerm,b.closedTerm]).represented⟩ :
          Piece env ctx p (letSource annotation binder first nextBody flag) Mode.step.expected)
        (SourceCasts env) (For.Casts setup),
        ValueForm setup ctx typed.sourceCore.val (optionType Step.stepState) := by
  have embed : ∀ scope a b, SourceCasts env scope a b → For.Casts setup scope a b :=
    fun _ _ _ cast => .base (.base (.source cast))
  have targetClosed : b.represented.val.ClosedN 0 := b.represented.property.closed 0 b.closed
  have target := right.target.closed_context SourceCasts.closed targetClosed ctx
  have domainTyped := annotation.type_typed library (ctx := ctx)
  have nextTyped := CastTyping.lambda (domainTyped.withCasts (SourceCasts env)) right.value
  have optionTyped : DirectTyping env 0 (annotation.core::ctx) (optionType Step.stepState) (.sort (.succ .zero)) := by
    exact .application (.constant steps.option (by simp [VLevel.WF]) rfl) steps.step_typed
  have functionChecked : CheckedTyping env 0 (For.Casts setup) ctx
      (.lam annotation.core right.sourceCore.val) (.forallE wordType (optionType Step.stepState)) :=
    .converted (nextTyped.mono embed) (.annotatedFunction annotation optionTyped optionFresh)
  have liftedTarget : CastTyping env 0 (SourceCasts env) (annotation.core::ctx) b.represented.val.lift cmdType := by
    simpa only [cmdType,VExpr.lift,VExpr.liftN] using target.lift closed SourceCasts.closed annotation.core
  have evaluation := eval_cast_typed (annotation.nextInputs inputs closed library consDeclared) evalDeclared liftedTarget
  have prefixTyped := Step.equalityPrefix_typed steps eqDeclared evaluation

  have beta := For.Casts.annotatedContinuation (setup := setup) annotation
    (resultType := optionType Step.stepState) (by trivial) (by intro u; simp [optionType]) prefixTyped right.value form
  have nextProof := CastTyping.lambda (domainTyped.withCasts (For.Casts setup)) right.equality
  have certificate := StructuralReadBind.letValue_typed inputs (left.inProofCasts embed) (target.mono embed)
    functionChecked nextProof (by
      simpa only [StructuralReadBind.bindValueContinuationType,Step.expected,Step.equalityPrefix,Step.lifted,Annotation.nextInputs,InputsTyped.withLocal,InputsTyped.lift,
        continuationValue,targetClosed.lift_eq,VExpr.lift,VExpr.liftN,
        annotation.closed.liftN_eq (Nat.zero_le 0)] using beta) factDeclared
  obtain ⟨artifact,checked,typed,codeEq,proofEq⟩ := finish_cast_complete
    (expected := Mode.step.expected p (app ``HybridWord.Cmd.letValue [a.code,b.code])
      (letSource annotation binder first nextBody flag))
    (proof := app ``WordLoopFacts.letValue ([a.code,b.code] ++ p.args ++
      [first,.lam binder annotation.native nextBody .default,a.checked.proof,
       .lam binder annotation.native b.checked.proof .default]))
    (Step.expected_represents (evalCmd_represents inputs
      (app_represents (.constant rfl) (.cons a.represented.property (.cons b.represented.property .nil))))
      (.letE annotation.represented left.sourceCore.property right.sourceCore.property))
    (app_represents (.constant rfl) (.cons a.represented.property (.cons b.represented.property
      (.cons inputs.i.property (.cons inputs.x.property (.cons inputs.y.property
        (.cons inputs.s.property (.cons inputs.ls.property (.cons left.sourceCore.property
          (.cons (.lam annotation.represented right.sourceCore.property)
            (.cons a.checked.proofCore.property (.cons (.lam annotation.represented b.checked.proofCore.property) .nil))))))))))))
    certificate ((known_casts a.checked left.proof).orElse (known_casts b.checked right.proof)) coverage exposure
    (app ``HybridWord.Cmd.letValue [a.code,b.code])
  let code := ClosedTerm.app ``HybridWord.Cmd.letValue [a.closedTerm,b.closedTerm]
  let piece : Piece env ctx p (letSource annotation binder first nextBody flag) Mode.step.expected :=
    ⟨code.val,artifact,code.closed,code.represented⟩
  have sourceTyped := CastTyping.checkedApplication nextTyped (annotation.argument left.value)
  simp only [(show (optionType Step.stepState).ClosedN 0 from by trivial).instN_eq (Nat.zero_le _)] at sourceTyped
  have cmdHead : CastTyping env 0 (SourceCasts env) ctx (.const ``HybridWord.Cmd.letValue []) bindValueConstructor :=
    .constant constructor (by simp) rfl
  have firstCmd := CastTyping.application cmdHead left.target
  simp only [bindValueConstructor,cmdType,VExpr.inst] at firstCmd
  let invariant : StructuralLoop.StepCasts inputs piece (SourceCasts env) (For.Casts setup) :=
    ⟨⟨_,.letE annotation.represented left.sourceCore.property right.sourceCore.property⟩,
      sourceTyped,.application firstCmd target,typed⟩
  exact ⟨artifact,checked,invariant,.beta right.value⟩

theorem step_let_complete_code (annotation : Annotation) (setup : AliasSetup env)
    (library : Signatures env) (inputs : InputsTyped env ctx p) (closed : ClosedConstantTypes env)
    (consDeclared : env.constants ``List.cons = some consSignature)
    (steps : Step.Signatures env)
    (eqDeclared : env.constants ``Eq = some eqSignature)
    (evalDeclared : env.constants ``HybridWord.Cmd.eval = some ⟨0,evalSignature⟩)
    (factDeclared : env.constants ``WordLoopFacts.letValue = some ⟨0,StructuralReadBind.letValueSignature⟩)
    (constructor : env.constants ``HybridWord.Cmd.letValue = some ⟨0,bindValueConstructor⟩)
    (optionFresh : ∀ r ∈ setup.rules, ``Option ≠ r.name)
    (coverage : Conversion.Covers setup.conversion 0 (For.Casts setup))
    (exposure : Exposure env)
    {a : Piece env ctx p first scalarExpected}
    (left : ScalarCasts inputs a (SourceCasts env) (For.Casts setup))
    {b : Piece env (annotation.core::ctx) {p.lift with locals := .bvar 0::p.lift.locals} nextBody Mode.step.expected}
    (right : StructuralLoop.StepCasts (annotation.nextInputs inputs closed library consDeclared) b (SourceCasts env) (For.Casts setup))
    (form : ValueForm setup (annotation.core::ctx) right.sourceCore.val (optionType Step.stepState))
    (firstParsed : ScalarEnvironment.parse env setup.conversion exposure ctx p first = some a)
    (nextParsed : visit env setup.conversion exposure nextBody (annotation.core::ctx)
      {p.lift with locals := .bvar 0::p.lift.locals} .step .identity (fun _ => none) = some b)
    (binder : Lean.Name) (flag : Bool) :
    ∃ piece, visit env setup.conversion exposure (letSource annotation binder first nextBody flag) ctx p
      .step .identity (fun _ => none) = some piece ∧
      ∃ typed : StructuralLoop.StepCasts inputs piece (SourceCasts env) (For.Casts setup),
        ValueForm setup ctx typed.sourceCore.val (optionType Step.stepState) ∧
      piece.code = app ``HybridWord.Cmd.letValue [a.code,b.code] := by
  obtain ⟨artifact,checked,typed,form⟩ := step_let_certificate annotation setup library inputs closed consDeclared
    steps eqDeclared evalDeclared factDeclared constructor optionFresh coverage exposure left right form binder flag
  let code := ClosedTerm.app ``HybridWord.Cmd.letValue [a.closedTerm,b.closedTerm]
  let piece : Piece env ctx p (letSource annotation binder first nextBody flag) Mode.step.expected :=
    ⟨code.val,artifact,code.closed,code.represented⟩
  refine ⟨piece,?_,typed,form,rfl⟩
  have compatible := annotation.compatible setup library (ctx := ctx)
  have notState : sameTerm annotation.native state = false := by cases annotation <;> rfl
  obtain ⟨tc,translated,same⟩ := annotation.represented.translate_complete
  have translatedExact : translate annotation.native = some ⟨annotation.core,annotation.represented⟩ := by
    cases tc with | mk val prop => dsimp only at same; subst val; exact translated
  have emptyFunctions : underFunctions (fun _ => (none : Option (Continuation env))) = (fun _ => none) := by
    funext n; cases n <;> rfl
  have modeValue : (Mode.step == Mode.value) = false := rfl
  have modeStep : (Mode.step == Mode.step) = true := rfl
  rw [visit]
  simp only [node,letSource,letParts,Substitution.apply,under,emptyFunctions,notState,compatible,
    modeValue,modeStep,Bool.false_eq_true,ite_false,Bool.false_and,Bool.not_false,Bool.true_and,ite_true]
  simp only [translatedExact,bind,Option.bind,pure,Option.pure_def]
  rw [firstParsed]
  dsimp only
  rw [nextParsed]
  dsimp only
  simp only [finishBody,Mode.expected,ClosedTerm.app,Piece.closedTerm,letSource,app,List.map_cons,List.map_nil] at checked ⊢
  rw [checked]
  rfl


theorem step_let_complete (annotation : Annotation) (setup : AliasSetup env)
    (library : Signatures env) (inputs : InputsTyped env ctx p) (closed : ClosedConstantTypes env)
    (consDeclared : env.constants ``List.cons = some consSignature)
    (steps : Step.Signatures env)
    (eqDeclared : env.constants ``Eq = some eqSignature)
    (evalDeclared : env.constants ``HybridWord.Cmd.eval = some ⟨0,evalSignature⟩)
    (factDeclared : env.constants ``WordLoopFacts.letValue = some ⟨0,StructuralReadBind.letValueSignature⟩)
    (constructor : env.constants ``HybridWord.Cmd.letValue = some ⟨0,bindValueConstructor⟩)
    (optionFresh : ∀ r ∈ setup.rules, ``Option ≠ r.name)
    (coverage : Conversion.Covers setup.conversion 0 (For.Casts setup))
    (exposure : Exposure env)
    {a : Piece env ctx p first scalarExpected}
    (left : ScalarCasts inputs a (SourceCasts env) (For.Casts setup))
    {b : Piece env (annotation.core::ctx) {p.lift with locals := .bvar 0::p.lift.locals} nextBody Mode.step.expected}
    (right : StructuralLoop.StepCasts (annotation.nextInputs inputs closed library consDeclared) b (SourceCasts env) (For.Casts setup))
    (form : ValueForm setup (annotation.core::ctx) right.sourceCore.val (optionType Step.stepState))
    (firstParsed : ScalarEnvironment.parse env setup.conversion exposure ctx p first = some a)
    (nextParsed : visit env setup.conversion exposure nextBody (annotation.core::ctx)
      {p.lift with locals := .bvar 0::p.lift.locals} .step .identity (fun _ => none) = some b)
    (binder : Lean.Name) (flag : Bool) :
    ∃ piece, visit env setup.conversion exposure (letSource annotation binder first nextBody flag) ctx p
      .step .identity (fun _ => none) = some piece ∧
      ∃ typed : StructuralLoop.StepCasts inputs piece (SourceCasts env) (For.Casts setup),
        ValueForm setup ctx typed.sourceCore.val (optionType Step.stepState) := by
  obtain ⟨piece,success,typed,form⟩ := step_let_complete_code annotation setup library inputs closed consDeclared steps eqDeclared evalDeclared factDeclared constructor optionFresh coverage exposure left right form firstParsed nextParsed binder flag
  exact ⟨piece,success,typed,form.1⟩

end IRComparison.WordFrontend.WordBinder
