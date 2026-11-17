import IRComparison.Frontend.WordAnnotatedRead
import IRComparison.Frontend.WordStructuralReadBind

namespace IRComparison.WordFrontend.WordBinder
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic StructuralBody
set_option maxHeartbeats 1800000

def stepReadSource (annotation : Annotation) (first next : Lean.Expr) : Lean.Expr :=
  Lean.mkApp2 (bindHead annotation.native stepType) first next

theorem substitute_stepReadSource (σ : Substitution) (annotation : Annotation) :
    σ.apply (stepReadSource annotation first (.lam binder annotation.native nextBody info)) =
      stepReadSource annotation (σ.apply first) (.lam binder annotation.native ((under σ).apply nextBody) info) := by
  cases annotation <;> cases σ <;> rfl

theorem mapped_step_bind_bits_complete_code (setup : AliasSetup env) (library : Signatures env)
    (bindLibrary : BindSignatures env) (inputs : InputsTyped env ctx p) (closed : ClosedConstantTypes env)
    (consDeclared : env.constants ``List.cons = some consSignature)
    (steps : Step.Signatures env)
    (eqDeclared : env.constants ``Eq = some eqSignature)
    (evalDeclared : env.constants ``HybridWord.Cmd.eval = some ⟨0,evalSignature⟩)
    (factDeclared : env.constants ``WordLoopFacts.bindValue = some ⟨0,StructuralReadBind.bindValueSignature⟩)
    (constructor : env.constants ``HybridWord.Cmd.letValue = some ⟨0,bindValueConstructor⟩)
    (stepFresh : ∀ r ∈ setup.rules, ``ForInStep ≠ r.name)
    (bindFresh : ∀ r ∈ setup.rules, ``Bind.bind ≠ r.name)
    (coverage : Conversion.Covers setup.conversion 0 (For.Casts setup)) (exposure : Exposure env)
    {a : Piece env ctx p (σ.apply first) readExpected}
    (left : Read.ReadCasts inputs a (SourceCasts env) (For.Casts setup))
    (firstForm : ValueForm setup ctx left.sourceCore.val (optionType wordType))
    {b : Piece env (bitvecType::ctx) {p.lift with locals := .bvar 0::p.lift.locals} ((under σ).apply nextBody) Mode.step.expected}
    (right : StructuralLoop.StepCasts (Annotation.bitvec.nextInputs inputs closed library consDeclared) b
      (SourceCasts env) (For.Casts setup))
    (form : ValueForm setup (bitvecType::ctx) right.sourceCore.val (optionType Step.stepState))
    (firstParsed : readStep env setup.conversion exposure ctx p
      (ScalarEnvironment.parse env setup.conversion exposure ctx p) (σ.apply first) = some a)
    (nextParsed : visit env setup.conversion exposure nextBody (bitvecType::ctx)
      {p.lift with locals := .bvar 0::p.lift.locals} .step (under σ) (underFunctions fs) = some b)
    (binder : Lean.Name) (info : Lean.BinderInfo) :
    ∃ piece, visit env setup.conversion exposure
      (stepReadSource .bitvec first (.lam binder Annotation.bitvec.native nextBody info)) ctx p
      .step σ fs = some piece ∧
      ∃ typed : StructuralLoop.StepCasts inputs piece (SourceCasts env) (For.Casts setup),
        ValueForm setup ctx typed.sourceCore.val (optionType Step.stepState) ∧
      piece.code = app ``HybridWord.Cmd.letValue [a.code,b.code] := by
  have embed : ∀ scope a b, SourceCasts env scope a b → For.Casts setup scope a b :=
    fun _ _ _ h => .base (.base (.source h))
  have targetClosed : b.represented.val.ClosedN 0 := b.represented.property.closed 0 b.closed
  have target := right.target.closed_context SourceCasts.closed targetClosed ctx
  have nextTyped := CastTyping.lambda (Annotation.bitvec.type_typed library |>.withCasts (SourceCasts env)) right.value
  have resultTyped {ctx : List VExpr} : DirectTyping env 0 ctx (optionType Step.stepState) (.sort (.succ .zero)) :=
    .application (.constant bindLibrary.option (by simp [VLevel.WF]) rfl)
      steps.step_typed
  have nextChecked : CheckedTyping env 0 (SourceCasts env) ctx
      (.lam bitvecType right.sourceCore.val) (.forallE wordType (optionType Step.stepState)) :=
    .converted nextTyped (.wordFunction resultTyped)
  have liftedTarget : CastTyping env 0 (SourceCasts env) (bitvecType::ctx) b.represented.val.lift cmdType := by
    simpa only [cmdType,VExpr.lift,VExpr.liftN] using target.lift closed SourceCasts.closed bitvecType
  have evaluation := eval_cast_typed (Annotation.bitvec.nextInputs inputs closed library consDeclared) evalDeclared liftedTarget
  have prefixTyped := Step.equalityPrefix_typed steps eqDeclared evaluation
  have beta := For.Casts.annotatedContinuation (setup := setup) Annotation.bitvec
    (resultType := optionType Step.stepState) (by trivial) (by intro u; simp [optionType]) prefixTyped right.value form
  have nextProof := CastTyping.lambda (library.bitvec_typed.withCasts (For.Casts setup)) right.equality
  have bvLift : bitvecType.liftN 1 = bitvecType := (Annotation.closed .bitvec).liftN_eq (Nat.zero_le 0)
  have certificate := StructuralReadBind.bindValue_typed inputs
    (⟨left.sourceCore,left.value.mono embed,left.target.mono embed,left.proof⟩ : Read.ReadCasts inputs a (For.Casts setup))
    (target.mono embed) (nextChecked.mono embed) nextProof (by
      simpa only [StructuralReadBind.bindValueContinuationType,Step.expected,Step.equalityPrefix,Step.lifted,Annotation.nextInputs,InputsTyped.withLocal,InputsTyped.lift,
        continuationValue,targetClosed.lift_eq,VExpr.lift,VExpr.liftN,
        Annotation.core,bvLift] using beta) factDeclared
  obtain ⟨artifact,checked,proofTyped,_,_⟩ := finish_cast_complete
    (expected := Mode.step.expected p (app ``HybridWord.Cmd.letValue [a.code,b.code])
      (StructuralReadBind.bindValueSource (σ.apply first) (.lam binder Annotation.bitvec.native ((under σ).apply nextBody) info)))
    (proof := app ``WordLoopFacts.bindValue ([a.code,b.code] ++ p.args ++
      [σ.apply first,.lam binder Annotation.bitvec.native ((under σ).apply nextBody) info,a.checked.proof,
        .lam binder Annotation.bitvec.native b.checked.proof info]))
    (Step.expected_represents (evalCmd_represents inputs
      (app_represents (.constant rfl) (.cons a.represented.property (.cons b.represented.property .nil))))
      (.app (.app StructuralReadBind.valueBind_represents left.sourceCore.property) (.lam Annotation.bitvec.represented right.sourceCore.property)))
    (app_represents (.constant rfl) (.cons a.represented.property (.cons b.represented.property
      (.cons inputs.i.property (.cons inputs.x.property (.cons inputs.y.property
        (.cons inputs.s.property (.cons inputs.ls.property (.cons left.sourceCore.property
          (.cons (.lam Annotation.bitvec.represented right.sourceCore.property)
            (.cons a.checked.proofCore.property (.cons (.lam Annotation.bitvec.represented b.checked.proofCore.property) .nil))))))))))))
    certificate ((known_casts a.checked left.proof).orElse (known_casts b.checked right.proof)) coverage exposure
    (app ``HybridWord.Cmd.letValue [a.code,b.code])
  let code := ClosedTerm.app ``HybridWord.Cmd.letValue [a.closedTerm,b.closedTerm]
  have head : CastTyping env 0 (SourceCasts env) ctx (.const ``HybridWord.Cmd.letValue []) bindValueConstructor :=
    .constant constructor (by simp) rfl
  have codeTyped := CastTyping.application (CastTyping.application head left.target) target
  have evaluation := eval_cast_typed inputs evalDeclared codeTyped
  have prefixTyped := Step.equalityPrefix_typed steps eqDeclared evaluation
  have sourceRep : Represents (stepReadSource .bitvec (σ.apply first) (.lam binder Annotation.bitvec.native ((under σ).apply nextBody) info))
      (bindValueAnnotated bitvecType left.sourceCore.val (.lam bitvecType right.sourceCore.val) Step.stepState) :=
    .app (.app (.app (.app (.app (.app (.constant rfl) (.constant rfl))
      (.app (.app (.constant rfl) (.constant rfl)) (.constant rfl))) Annotation.bitvec.represented) (.app (.constant rfl) (.constant rfl)))
      left.sourceCore.property) (.lam Annotation.bitvec.represented right.sourceCore.property)
  have stateTyped : DirectTyping env 0 ctx Step.stepState (.sort (.succ .zero)) := steps.step_typed
  have headerTyped := bindLibrary.header_typed (Annotation.bitvec.type_typed library)
    stateTyped Annotation.bitvec.closed (by trivial)
  have firstChecked := checked_option_bitvec bindLibrary.option left.value
  have readApplied := CastTyping.checkedApplication (headerTyped.withCasts (SourceCasts env)) firstChecked
  simp only [Annotation.core, (Annotation.closed .bitvec).instN_eq (Nat.zero_le _),
    optionType,Step.stepState,stateType,VExpr.inst] at readApplied
  have bvInst : bitvecType.inst left.sourceCore.val = bitvecType :=
    (Annotation.closed .bitvec).instN_eq (Nat.zero_le 0)
  rw [bvInst] at readApplied
  have sourceTyped := CastTyping.application readApplied nextTyped
  have sourceSame := substitute_stepReadSource (binder := binder) (first := first) (nextBody := nextBody) (info := info) σ .bitvec
  rw [← sourceSame] at sourceRep
  have actualRep := Step.expected_represents (evalCmd_represents inputs code.represented.property) sourceRep
  have cast : For.Casts setup ctx artifact.core.val
      (equalValues (optionType Step.stepState)
        (Step.lifted (bodyValue inputs.i.val inputs.x.val inputs.y.val code.represented.val inputs.s.val inputs.ls.val))
        (bindValueAnnotated bitvecType left.sourceCore.val (.lam bitvecType right.sourceCore.val) Step.stepState)) := by
    rw [artifact.core.property.unique (Step.expected_represents (evalCmd_represents inputs code.represented.property)
      (Represents.app (.app StructuralReadBind.valueBind_represents left.sourceCore.property) (.lam Annotation.bitvec.represented right.sourceCore.property)))]
    exact .annotatedReadEquality bindLibrary (fun _ => steps.step_typed)
      (by trivial) rfl stepFresh rfl bindFresh prefixTyped left.value firstForm right.value
  obtain ⟨transported,retargeted,transportTyped⟩ := ScalarEnvironment.retarget_cast_complete artifact actualRep
    proofTyped ((CastTyping.application prefixTyped sourceTyped).mono embed) cast coverage
  let piece : Piece env ctx p (σ.apply (stepReadSource .bitvec first (.lam binder Annotation.bitvec.native nextBody info))) Mode.step.expected :=
    ⟨code.val,transported,code.closed,code.represented⟩
  let typed : StructuralLoop.StepCasts inputs piece (SourceCasts env) (For.Casts setup) :=
    ⟨⟨_,sourceRep⟩,sourceTyped,codeTyped,transportTyped⟩
  refine ⟨piece,?_,typed,?_,rfl⟩
  · have sc := Annotation.bitvec.compatible setup library (ctx := ctx)
    have notState : sameTerm Annotation.bitvec.native state = false := rfl
    have notWord : sameTerm Annotation.bitvec.native word = false := rfl
    have notUnit : sameTerm Annotation.bitvec.native (.const ``PUnit [.succ .zero]) = false := rfl
    have translated : translate Annotation.bitvec.native = some ⟨bitvecType,Annotation.bitvec.represented⟩ := rfl
    have empty : underFunctions (fun _ => (none : Option (Continuation env))) = (fun _ => none) := by funext n; cases n <;> rfl
    have modeValue : (Mode.step == Mode.value) = false := rfl
    have modeStep : (Mode.step == Mode.step) = true := rfl
    have modeBody : (Mode.step == Mode.body) = false := rfl
    have annotationApply : σ.apply Annotation.bitvec.native = Annotation.bitvec.native := by
      rw [Substitution.apply_eq,Annotation.substitute_native]
    have translatedMapped : (translate (σ.apply Annotation.bitvec.native)).unattach = some bitvecType := by
      rw [annotationApply]; rfl
    have lambdaSame : σ.apply (.lam binder Annotation.bitvec.native nextBody info) =
        .lam binder Annotation.bitvec.native ((under σ).apply nextBody) info := by
      cases σ <;> rfl
    rw [visit]
    simp [node,modeValue,modeStep,modeBody,letParts,applicationHead,makeContinuation,continuationParts,lambdaChain,
      ScalarEnvironment.arguments,ScalarEnvironment.below,lambdaParts,annotationApply,
      stepReadSource,bindHead,Lean.mkAppN,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB,
      Lean.Expr.getAppFn,Lean.Expr.constName?,notState,notWord,notUnit,sc,translated]
    simp [firstParsed,nextParsed,finishBody,retargetPiece,Mode.expected,ClosedTerm.app,Piece.closedTerm,
      translatedMapped,lambdaSame,code,piece,StructuralReadBind.bindValueSource,stepReadSource,bindHead,Lean.mkApp2,Lean.mkAppB,Lean.mkApp,app] at checked retargeted ⊢
    refine ⟨first,rfl,a,firstParsed,?_⟩
    have notValue : (Mode.step != Mode.value) = true := rfl
    simp only [notValue,ite_true,lambdaSame]
    cases σ
    all_goals
      simp only [Substitution.apply,LeanBindings.substitute,under,Annotation.native,Arithmetic.nativeWidth,
        app,List.foldl_cons,List.foldl_nil,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB] at checked retargeted ⊢
      rw [checked]
      simp only [Option.bind]
      rw [retargeted]
  · exact .constant rfl bindFresh (by decide)

theorem step_bind_bits_complete_code (setup : AliasSetup env) (library : Signatures env)
    (bindLibrary : BindSignatures env) (inputs : InputsTyped env ctx p) (closed : ClosedConstantTypes env)
    (consDeclared : env.constants ``List.cons = some consSignature)
    (steps : Step.Signatures env)
    (eqDeclared : env.constants ``Eq = some eqSignature)
    (evalDeclared : env.constants ``HybridWord.Cmd.eval = some ⟨0,evalSignature⟩)
    (factDeclared : env.constants ``WordLoopFacts.bindValue = some ⟨0,StructuralReadBind.bindValueSignature⟩)
    (constructor : env.constants ``HybridWord.Cmd.letValue = some ⟨0,bindValueConstructor⟩)
    (stepFresh : ∀ r ∈ setup.rules, ``ForInStep ≠ r.name)
    (bindFresh : ∀ r ∈ setup.rules, ``Bind.bind ≠ r.name)
    (coverage : Conversion.Covers setup.conversion 0 (For.Casts setup)) (exposure : Exposure env)
    {a : Piece env ctx p first readExpected}
    (left : Read.ReadCasts inputs a (SourceCasts env) (For.Casts setup))
    (firstForm : ValueForm setup ctx left.sourceCore.val (optionType wordType))
    {b : Piece env (bitvecType::ctx) {p.lift with locals := .bvar 0::p.lift.locals} nextBody Mode.step.expected}
    (right : StructuralLoop.StepCasts (Annotation.bitvec.nextInputs inputs closed library consDeclared) b
      (SourceCasts env) (For.Casts setup))
    (form : ValueForm setup (bitvecType::ctx) right.sourceCore.val (optionType Step.stepState))
    (firstParsed : readStep env setup.conversion exposure ctx p
      (ScalarEnvironment.parse env setup.conversion exposure ctx p) first = some a)
    (nextParsed : visit env setup.conversion exposure nextBody (bitvecType::ctx)
      {p.lift with locals := .bvar 0::p.lift.locals} .step .identity (fun _ => none) = some b)
    (binder : Lean.Name) (info : Lean.BinderInfo) :
    ∃ piece, visit env setup.conversion exposure
      (stepReadSource .bitvec first (.lam binder Annotation.bitvec.native nextBody info)) ctx p
      .step .identity (fun _ => none) = some piece ∧
      ∃ typed : StructuralLoop.StepCasts inputs piece (SourceCasts env) (For.Casts setup),
        ValueForm setup ctx typed.sourceCore.val (optionType Step.stepState) ∧
      piece.code = app ``HybridWord.Cmd.letValue [a.code,b.code] := by
  have empty : underFunctions (fun _ => (none : Option (Continuation env))) = (fun _ => none) := by
    funext n; cases n <;> rfl
  exact mapped_step_bind_bits_complete_code (σ := .identity) (fs := fun _ => none)
    (first := first) (nextBody := nextBody) setup library bindLibrary inputs closed consDeclared steps
    eqDeclared evalDeclared factDeclared constructor stepFresh bindFresh coverage exposure
    left firstForm right form firstParsed (by simpa only [under,empty] using nextParsed) binder info


theorem step_bind_bits_complete (setup : AliasSetup env) (library : Signatures env)
    (bindLibrary : BindSignatures env) (inputs : InputsTyped env ctx p) (closed : ClosedConstantTypes env)
    (consDeclared : env.constants ``List.cons = some consSignature)
    (steps : Step.Signatures env)
    (eqDeclared : env.constants ``Eq = some eqSignature)
    (evalDeclared : env.constants ``HybridWord.Cmd.eval = some ⟨0,evalSignature⟩)
    (factDeclared : env.constants ``WordLoopFacts.bindValue = some ⟨0,StructuralReadBind.bindValueSignature⟩)
    (constructor : env.constants ``HybridWord.Cmd.letValue = some ⟨0,bindValueConstructor⟩)
    (stepFresh : ∀ r ∈ setup.rules, ``ForInStep ≠ r.name)
    (bindFresh : ∀ r ∈ setup.rules, ``Bind.bind ≠ r.name)
    (coverage : Conversion.Covers setup.conversion 0 (For.Casts setup)) (exposure : Exposure env)
    {a : Piece env ctx p first readExpected}
    (left : Read.ReadCasts inputs a (SourceCasts env) (For.Casts setup))
    (firstForm : ValueForm setup ctx left.sourceCore.val (optionType wordType))
    {b : Piece env (bitvecType::ctx) {p.lift with locals := .bvar 0::p.lift.locals} nextBody Mode.step.expected}
    (right : StructuralLoop.StepCasts (Annotation.bitvec.nextInputs inputs closed library consDeclared) b
      (SourceCasts env) (For.Casts setup))
    (form : ValueForm setup (bitvecType::ctx) right.sourceCore.val (optionType Step.stepState))
    (firstParsed : readStep env setup.conversion exposure ctx p
      (ScalarEnvironment.parse env setup.conversion exposure ctx p) first = some a)
    (nextParsed : visit env setup.conversion exposure nextBody (bitvecType::ctx)
      {p.lift with locals := .bvar 0::p.lift.locals} .step .identity (fun _ => none) = some b)
    (binder : Lean.Name) (info : Lean.BinderInfo) :
    ∃ piece, visit env setup.conversion exposure
      (stepReadSource .bitvec first (.lam binder Annotation.bitvec.native nextBody info)) ctx p
      .step .identity (fun _ => none) = some piece ∧
      ∃ typed : StructuralLoop.StepCasts inputs piece (SourceCasts env) (For.Casts setup),
        ValueForm setup ctx typed.sourceCore.val (optionType Step.stepState) := by
  obtain ⟨piece,success,typed,form⟩ := step_bind_bits_complete_code setup library bindLibrary inputs closed consDeclared steps eqDeclared evalDeclared factDeclared constructor stepFresh bindFresh coverage exposure left firstForm right form firstParsed nextParsed binder info
  exact ⟨piece,success,typed,form.1⟩

end IRComparison.WordFrontend.WordBinder
