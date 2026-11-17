import IRComparison.Frontend.WordFunctionBindings
import IRComparison.Frontend.WordStructuralStep
import IRComparison.Frontend.WordAnnotatedStepLet

/-! Loop certificates with captured lexical bindings. The runtime traverses
original syntax; substitutions are used only in certificate types. -/
namespace IRComparison.WordFrontend.FunctionSyntax
open Lean4Lean LeanTyped LeanTypeInference Certificate StructuralBody StructuralSyntax
set_option maxHeartbeats 1800000

theorem substitute_stepSequence (σ : Substitution) :
    σ.apply (StructuralStep.sequenceSource first (.lam binder state next info)) =
      StructuralStep.sequenceSource (σ.apply first) (.lam binder state ((under σ).apply next) info) := by
  cases σ <;> rfl

theorem stepSequence_complete_code (setup : Arithmetic.AliasSetup env) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (fresh : ScopedSyntax.Fresh setup) (exposure : Exposure env)
    (inputs : InputsTyped env ctx p)
    {a : Piece env ctx p (σ.apply first) bodyExpected}
    (left : BodyCasts inputs a (Arithmetic.SourceCasts env) (For.Casts setup))
    {b : Piece env (stateType::ctx) {p.lift with s := .bvar 0} ((under σ).apply next) Mode.step.expected}
    (right : StructuralLoop.StepCasts (inputs.nextState closed) b (Arithmetic.SourceCasts env) (For.Casts setup))
    (rightForm : Arithmetic.ValueForm setup (stateType::ctx) right.sourceCore.val (optionType Step.stepState))
    (ha : visit env setup.conversion exposure first ctx p .body σ fs = some a)
    (hb : visit env setup.conversion exposure next (stateType::ctx) {p.lift with s := .bvar 0}
      .step (under σ) (underFunctions fs) = some b)
    (binder : Lean.Name) (info : Lean.BinderInfo) :
    ∃ result, visit env setup.conversion exposure (StructuralStep.sequenceSource first (.lam binder state next info))
        ctx p .step σ fs = some result ∧
      ∃ typed : StructuralLoop.StepCasts inputs result (Arithmetic.SourceCasts env) (For.Casts setup),
        Arithmetic.ValueForm setup ctx typed.sourceCore.val (optionType Step.stepState) ∧ result.code = app ``HybridWord.Cmd.seq [a.code,b.code] := by
  have coverage := For.Casts.covered setup library.scalars.toSignatures library.steps closed
    library.cons library.eq library.eval fresh.state fresh.eq fresh.lift
  have embed : ∀ scope a b, Arithmetic.SourceCasts env scope a b → For.Casts setup scope a b :=
    fun _ _ _ h => .base (.base (.source h))
  obtain ⟨target,nextTyped,_⟩ := StructuralStep.sequence_next_typed inputs closed Arithmetic.SourceCasts.closed library.steps.state right
  have eval := eval_cast_typed (inputs.nextState closed) library.eval right.target
  have direct := For.Casts.directContinuation (setup := setup) .state eval right.value rightForm
  have codeClosed := b.represented.property.closed 0 b.closed
  have beta : For.Casts setup ctx (StructuralStep.sequenceNextActual inputs b.represented.val right.sourceCore.val)
      (StructuralStep.sequenceContinuationType inputs b.represented.val (.lam stateType right.sourceCore.val)) := by
    simpa only [StructuralStep.sequenceNextActual,StructuralStep.sequenceContinuationType,
      InputsTyped.nextState,InputsTyped.lift,Step.Binder.core,Arithmetic.continuationValue,
      VExpr.lift,VExpr.liftN,stateType,codeClosed.liftN_eq (Nat.zero_le _)] using direct
  have assembled := StructuralStep.sequence_finish inputs closed Arithmetic.SourceCasts.closed embed library.steps.state
    left right beta library.stepSequence coverage exposure binder info
  have sourceSame := substitute_stepSequence (first := first) (next := next) (binder := binder) (info := info) σ
  rw [← sourceSame] at assembled
  obtain ⟨artifact,checked,proofTyped,_,_⟩ := assembled
  let code := ClosedTerm.app ``HybridWord.Cmd.seq [a.closedTerm,b.closedTerm]
  let result : Piece env ctx p (σ.apply (StructuralStep.sequenceSource first (.lam binder state next info))) Mode.step.expected :=
    ⟨code.val,artifact,code.closed,code.represented⟩
  have src : Represents (σ.apply (StructuralStep.sequenceSource first (.lam binder state next info)))
      (.app (.app StructuralStep.header left.sourceCore.val) (.lam stateType right.sourceCore.val)) := by
    rw [sourceSame]
    exact .app (.app StructuralStep.header_represents left.sourceCore.property) (.lam (.constant rfl) right.sourceCore.property)
  have applied := CastTyping.application ((library.bind.header_typed (domain := stateType) (result := Step.stepState)
    (.constant library.steps.state (by simp) rfl) library.steps.step_typed (by trivial) (by trivial)).withCasts (Arithmetic.SourceCasts env)) left.value
  simp only [optionType,stateType,Step.stepState,VExpr.inst] at applied
  have sourceTyped := CastTyping.application applied nextTyped
  have constructor : CastTyping env 0 (Arithmetic.SourceCasts env) ctx
      (.const ``HybridWord.Cmd.seq []) sequenceConstructor := .constant library.sequenceConstructor (by simp) rfl
  have targetTyped := CastTyping.application (CastTyping.application constructor left.target) target
  let typed : StructuralLoop.StepCasts inputs result (Arithmetic.SourceCasts env) (For.Casts setup) :=
    ⟨⟨_,src⟩,sourceTyped,targetTyped,proofTyped⟩
  refine ⟨result,?_,typed,?_,rfl⟩
  · have bodyValue : (Mode.step == Mode.value) = false := rfl
    have bodyStep : (Mode.step == Mode.step) = true := rfl
    have stateApply : σ.apply state = state := by cases σ <;> rfl
    have ss : sameTerm state state = true := sameTerm_complete (Represents.constant rfl) (Represents.constant rfl)
    have su : sameTerm state (.const ``PUnit [.succ .zero]) = false := rfl
    have st : translate state = some ⟨stateType,Represents.constant rfl⟩ := rfl
    have stMapped : (translate (σ.apply state)).unattach = some stateType := by rw [stateApply]; rfl
    have sc : compatible env setup.conversion ctx state state = true :=
      compatible_same (Represents.constant rfl) (Represents.constant rfl) env setup.conversion ctx
    rw [visit]
    simp [node,bodyValue,bodyStep,letParts,applicationHead,makeContinuation,continuationParts,lambdaChain,
      ScalarEnvironment.arguments,ScalarEnvironment.below,lambdaParts,stateApply,
      StructuralStep.sequenceSource,StructuralStep.nativeHeader,bindHead,Lean.mkAppN,Lean.mkApp2,Lean.mkApp,Lean.mkAppB,
      Lean.Expr.getAppFn,Lean.Expr.constName?,ss,su,st]
    simp only [List.map_append,List.map_cons,List.map_nil,Function.comp_apply,
      List.cons_append,List.nil_append,List.length_cons,List.length_nil,Nat.reduceAdd,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.unattach_some,
      stMapped,sc,ite_true,Option.bind_some,ha,hb]
    dsimp only [List.map,List.append,List.length,Function.comp_apply,List.getElem?_cons_zero,
      List.getElem?_cons_succ,Option.unattach]
    try simp only [ha,hb,Option.bind_some]
    have lambdaSame : σ.apply (.lam binder state next info) = .lam binder state ((under σ).apply next) info := by cases σ <;> rfl
    simp only [lambdaSame,finishBody,bind,Option.bind,pure,Option.pure_def]
    refine ⟨first,rfl,stateType,rfl,trivial,a,ha,b,hb,?_⟩
    simp only [Mode.expected,ClosedTerm.app,Piece.closedTerm,List.map_cons,List.map_nil,
      List.cons_append,List.nil_append,StructuralStep.sequenceSource,StructuralStep.nativeHeader,bindHead,Lean.mkAppN,Lean.mkApp4,
      Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB] at checked ⊢
    rw [checked]
    rfl
  · exact .constant rfl (fresh.value _ (by simp)) (by decide)

/-- Transport a value certificate without changing its code or checker. -/
theorem value_outcome_transport (inputs : InputsTyped env ctx p)
    {source target : Lean.Expr} (same : source = target)
    {left : Option (Piece env ctx p source Mode.value.expected)}
    {right : Option (Piece env ctx p target Mode.value.expected)} (equal : HEq left right)
    (result : ∃ piece, right = some piece ∧
      Nonempty (StructuralLoop.ValueCasts inputs piece casts proofCasts) ∧ piece.code = quotation) :
    ∃ piece, left = some piece ∧
      Nonempty (StructuralLoop.ValueCasts inputs piece casts proofCasts) ∧ piece.code = quotation := by
  subst target
  rw [eq_of_heq equal]
  exact result

/-- A current-state expression keeps its meaning under captured bindings. -/
theorem valueCurrent_congr (same : σ.apply raw = p.s) (inputs : InputsTyped env ctx p) :
    HEq (visit env conv exposure raw ctx p .value σ fs)
      (visit env conv exposure p.s ctx p .value .identity (fun _ => none)) := by
  have eq := sameTerm_complete inputs.s.property inputs.s.property
  rw [visit,visit]
  have mode : (Mode.value == Mode.value) = true := rfl
  have identity : Substitution.identity.apply p.s = p.s := rfl
  simp only [node,mode,identity,same,eq,ite_true]
  generalize σ.apply raw = q at same ⊢
  subst q
  rfl


theorem substitute_yield (σ : Substitution) :
    σ.apply (Step.yieldSource raw) = Step.yieldSource (σ.apply raw) := by
  cases σ <;> rfl

theorem yield_complete_code (setup : Arithmetic.AliasSetup env) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (fresh : ScopedSyntax.Fresh setup) (exposure : Exposure env)
    (inputs : InputsTyped env ctx p)
    {a : Piece env ctx p (σ.apply raw) Mode.value.expected}
    (typed : StructuralLoop.ValueCasts inputs a (Arithmetic.SourceCasts env) (For.Casts setup))
    (parsed : visit env setup.conversion exposure raw ctx p .value σ fs = some a) :
    ∃ result, visit env setup.conversion exposure (Step.yieldSource raw) ctx p .step σ fs = some result ∧
      ∃ resultTyped : StructuralLoop.StepCasts inputs result (Arithmetic.SourceCasts env) (For.Casts setup),
        Arithmetic.ValueForm setup ctx resultTyped.sourceCore.val (optionType Step.stepState) ∧ result.code = a.code := by
  have coverage := For.Casts.covered setup library.scalars.toSignatures library.steps closed
    library.cons library.eq library.eval fresh.state fresh.eq fresh.lift
  have embed : ∀ scope a b, Arithmetic.SourceCasts env scope a b → For.Casts setup scope a b :=
    fun _ _ _ h => .base (.base (.source h))
  have assembled := StructuralLoop.yield_certificate inputs library.steps library.eval library.compose
    embed typed coverage exposure
  rw [← substitute_yield σ] at assembled
  obtain ⟨artifact,checked,proofTyped⟩ := assembled
  let result : Piece env ctx p (σ.apply (Step.yieldSource raw)) Mode.step.expected :=
    ⟨a.code,artifact,a.closed,a.represented⟩
  have represented : Represents (σ.apply (Step.yieldSource raw)) (Step.yieldValue typed.sourceCore.val) := by
    rw [substitute_yield]; exact Step.yield_represents typed.sourceCore.property
  let resultTyped : StructuralLoop.StepCasts inputs result (Arithmetic.SourceCasts env) (For.Casts setup) :=
    ⟨⟨_,represented⟩,Step.yield_typed library.steps typed.value,typed.target,proofTyped⟩
  refine ⟨result,?_,resultTyped,?_,rfl⟩
  · have modeValue : (Mode.step == Mode.value) = false := rfl
    have modeStep : (Mode.step == Mode.step) = true := rfl
    rw [visit]
    simp [node,modeValue,modeStep,letParts,applicationHead,makeContinuation,continuationParts,lambdaChain,
      ScalarEnvironment.arguments,ScalarEnvironment.below,
      Step.yieldSource,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,Lean.mkAppB,Lean.mkApp,
      Lean.Expr.getAppFn,Lean.Expr.constName?,List.map_cons,List.map_nil,
      finishBody,Mode.expected,parsed,result] at checked ⊢
    try simp only [List.map_append,List.map_cons,List.map_nil,List.nil_append,List.cons_append,
      List.getLast?_cons_cons,List.getLast?_singleton,Option.unattach_some,Option.bind_some]
    simp [arguments,ScalarEnvironment.arguments,ScalarEnvironment.below,parsed,finishBody,
      Mode.expected,Piece.closedTerm,result,app,Step.yieldSource,Lean.mkApp4,Lean.mkApp3,
      Lean.mkApp2,Lean.mkAppB,Lean.mkApp] at checked ⊢
    refine ⟨raw,⟨?_,rfl⟩,a,parsed,artifact,checked,rfl,HEq.rfl,HEq.rfl⟩
    simp [syntaxSize]; omega
  · exact ScopedSyntax.head_form fresh represented (by rw [substitute_yield]; rfl) (by simp)


theorem substitute_stepBranch (σ : Substitution) :
    σ.apply (StructuralStep.Conditional.source v d yes no) =
      StructuralStep.Conditional.source (σ.apply v) (σ.apply d) (σ.apply yes) (σ.apply no) := by
  cases σ <;> rfl

theorem stepBranch_complete_code (setup : Arithmetic.AliasSetup env) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (fresh : ScopedSyntax.Fresh setup) (exposure : Exposure env)
    (inputs : InputsTyped env ctx p)
    {e : Piece env ctx p (σ.apply v) scalarExpected}
    (value : ScalarCasts inputs e (Arithmetic.SourceCasts env) (For.Casts setup))
    {a : Piece env ctx p (σ.apply yes) Mode.step.expected}
    (left : StructuralLoop.StepCasts inputs a (Arithmetic.SourceCasts env) (For.Casts setup))
    {b : Piece env ctx p (σ.apply no) Mode.step.expected}
    (right : StructuralLoop.StepCasts inputs b (Arithmetic.SourceCasts env) (For.Casts setup))
    (decisionRep : Represents (σ.apply d) dc)
    (predicateTyped : CastTyping env 0 (Arithmetic.SourceCasts env) ctx
      (Branch.condition value.sourceCore.val) (.sort .zero))
    (decisionTyped : CastTyping env 0 (Arithmetic.SourceCasts env) ctx dc
      (.app (.const ``Decidable []) (Branch.condition value.sourceCore.val)))
    (he : ScalarEnvironment.parse env setup.conversion exposure ctx p (σ.apply v) = some e)
    (ha : visit env setup.conversion exposure yes ctx p .step σ fs = some a)
    (hb : visit env setup.conversion exposure no ctx p .step σ fs = some b) :
    ∃ result, visit env setup.conversion exposure (StructuralStep.Conditional.source v d yes no) ctx p .step σ fs = some result ∧
      ∃ typed : StructuralLoop.StepCasts inputs result (Arithmetic.SourceCasts env) (For.Casts setup),
        Arithmetic.ValueForm setup ctx typed.sourceCore.val (optionType Step.stepState) ∧ result.code = app ``HybridWord.Cmd.branch [e.code,a.code,b.code] := by
  have coverage := For.Casts.covered setup library.scalars.toSignatures library.steps closed
    library.cons library.eq library.eval fresh.state fresh.eq fresh.lift
  have embed : ∀ scope a b, Arithmetic.SourceCasts env scope a b → For.Casts setup scope a b :=
    fun _ _ _ h => .base (.base (.source h))
  have assembled := StructuralStep.Conditional.finish_complete inputs
    (value.inProofCasts embed) (left.inProofCasts embed) (right.inProofCasts embed) decisionRep
    (decisionTyped.mono embed) library.stepBranch coverage exposure
  let code := ClosedTerm.app ``HybridWord.Cmd.branch [e.closedTerm,a.closedTerm,b.closedTerm]
  have represented := StructuralStep.Conditional.source_represents value.sourceCore.property decisionRep left.sourceCore.property right.sourceCore.property
  have sourceSame := substitute_stepBranch (v := v) (d := d) (yes := yes) (no := no) σ
  rw [← sourceSame] at represented assembled
  obtain ⟨artifact,checked,proofTyped,_,_⟩ := assembled
  let result : Piece env ctx p (σ.apply (StructuralStep.Conditional.source v d yes no)) Mode.step.expected :=
    ⟨code.val,artifact,code.closed,code.represented⟩
  have target : CastTyping env 0 (Arithmetic.SourceCasts env) ctx
      (applications (.const ``HybridWord.Cmd.branch []) [e.represented.val,a.represented.val,b.represented.val]) cmdType := by
    have h : CastTyping env 0 (Arithmetic.SourceCasts env) ctx (.const ``HybridWord.Cmd.branch []) Branch.constructorSignature :=
      .constant library.branchConstructor (by simp) rfl
    exact .application (.application (.application h value.target) left.target) right.target
  let typed : StructuralLoop.StepCasts inputs result (Arithmetic.SourceCasts env) (For.Casts setup) :=
    ⟨⟨_,represented⟩,Branch.ite_typed library.stepOption_typed (by trivial) predicateTyped decisionTyped
      left.value right.value library.ite,target,proofTyped⟩
  refine ⟨result,?_,typed,?_,rfl⟩
  · rw [visit]
    have bodyValue : (Mode.step == Mode.value) = false := rfl
    have bodyStep : (Mode.step == Mode.step) = true := rfl
    simp only [node,bodyValue,bodyStep]
    simp [letParts,applicationHead,makeContinuation,continuationParts,lambdaChain,
      ScalarEnvironment.arguments,ScalarEnvironment.below,StructuralStep.Conditional.source,Step.nativeChoice,Branch.nativeCondition,
      Lean.mkApp5,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB,
      Lean.Expr.getAppFn,Lean.Expr.constName?]
    have test : nonzeroValue (Branch.nativeCondition v) = some v := rfl
    simp only [Branch.nativeCondition,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB] at test
    simp only [test,Option.bind_some,he,ha,hb]
    refine ⟨v,rfl,e,he,a,rfl,b,rfl,?_⟩
    simp only [finishBody,bind,Option.bind,pure,Option.pure_def]
    simp only [Mode.expected,ClosedTerm.app,ClosedTerm.const,Piece.closedTerm,List.map_cons,List.map_nil,
      List.cons_append,List.nil_append,StructuralStep.Conditional.source,Step.nativeChoice,Branch.nativeCondition,Lean.mkApp5,Lean.mkApp4,
      Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB] at checked ⊢
    rw [checked]
    rfl
  · change Arithmetic.ValueForm setup ctx _ _
    exact .constant rfl (fresh.value _ (by simp)) (by decide)

theorem stepLetValue_complete_code (annotation : WordBinder.Annotation)
    (setup : Arithmetic.AliasSetup env) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (fresh : ScopedSyntax.Fresh setup) (exposure : Exposure env)
    (inputs : InputsTyped env ctx p)
    {a : Piece env ctx p (σ.apply first) scalarExpected}
    (left : ScalarCasts inputs a (Arithmetic.SourceCasts env) (For.Casts setup))
    {b : Piece env (annotation.core::ctx) {p.lift with locals := .bvar 0::p.lift.locals}
      ((under σ).apply next) Mode.step.expected}
    (right : StructuralLoop.StepCasts (annotation.nextInputs inputs closed library.scalars.toSignatures library.cons) b
      (Arithmetic.SourceCasts env) (For.Casts setup))
    (rightForm : Arithmetic.ValueForm setup (annotation.core::ctx) right.sourceCore.val (optionType Step.stepState))
    (ha : ScalarEnvironment.parse env setup.conversion exposure ctx p (σ.apply first) = some a)
    (hb : visit env setup.conversion exposure next (annotation.core::ctx)
      {p.lift with locals := .bvar 0::p.lift.locals} .step (under σ) (underFunctions fs) = some b)
    (binder : Lean.Name) (flag : Bool) :
    ∃ result, visit env setup.conversion exposure (WordBinder.letSource annotation binder first next flag)
        ctx p .step σ fs = some result ∧
      ∃ typed : StructuralLoop.StepCasts inputs result (Arithmetic.SourceCasts env) (For.Casts setup),
        Arithmetic.ValueForm setup ctx typed.sourceCore.val (optionType Step.stepState) ∧
        result.code = app ``HybridWord.Cmd.letValue [a.code,b.code] := by
  have coverage := For.Casts.covered setup library.scalars.toSignatures library.steps closed
    library.cons library.eq library.eval fresh.state fresh.eq fresh.lift
  have assembled := WordBinder.step_let_certificate annotation setup library.scalars.toSignatures inputs closed
    library.cons library.steps library.eq library.eval library.stepLetValue
    library.letValueConstructor fresh.option coverage exposure left right rightForm binder flag
  have sourceSame := substitute_annotated_let (binder := binder) (value := first) (next := next) (flag := flag) σ annotation
  rw [← sourceSame] at assembled
  obtain ⟨artifact,checked,typed,form⟩ := assembled
  let code := ClosedTerm.app ``HybridWord.Cmd.letValue [a.closedTerm,b.closedTerm]
  let result : Piece env ctx p (σ.apply (WordBinder.letSource annotation binder first next flag)) Mode.step.expected :=
    ⟨code.val,artifact,code.closed,code.represented⟩
  refine ⟨result,?_,typed,form,rfl⟩
  have annotationApply : σ.apply annotation.native = annotation.native := by
    rw [Substitution.apply_eq,annotation.substitute_native]
  have compatible := annotation.compatible setup library.scalars.toSignatures (ctx := ctx)
  have notState : sameTerm annotation.native state = false := by cases annotation <;> rfl
  obtain ⟨tc,translated,same⟩ := annotation.represented.translate_complete
  have translatedExact : translate annotation.native = some ⟨annotation.core,annotation.represented⟩ := by
    cases tc with | mk val prop => dsimp only at same; subst val; exact translated
  have modeValue : (Mode.step == Mode.value) = false := rfl
  have modeStep : (Mode.step == Mode.step) = true := rfl
  cases annotation <;> cases σ
  all_goals
    rw [visit]
    simp only [node,WordBinder.letSource,letParts,Substitution.apply,LeanBindings.substitute,
      WordBinder.Annotation.native,WordBinder.Annotation.core,WordFrontend.word,Arithmetic.nativeWidth,app,List.foldl_cons,List.foldl_nil,
      Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB,under] at compatible notState translatedExact ha hb checked ⊢
    simp only [notState,compatible,modeValue,modeStep,Bool.false_eq_true,ite_false,
      Bool.false_and,Bool.not_false,Bool.true_and,ite_true,translatedExact,bind,Option.bind,pure,Option.pure_def]
    rw [ha]
    dsimp only
    rw [hb]
    dsimp only
    simp only [finishBody,Mode.expected,ClosedTerm.app,Piece.closedTerm,WordBinder.letSource,
      Substitution.apply,LeanBindings.substitute,WordBinder.Annotation.native,WordBinder.Annotation.core,WordFrontend.word,
      Arithmetic.nativeWidth,app,List.foldl_cons,List.foldl_nil,List.map_cons,List.map_nil,
      Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB] at checked ⊢
    rw [checked]
    rfl

private theorem step_helper_retarget_complete_transport {sourceCore : VExpr}
    (setup : Arithmetic.AliasSetup env)
    (steps : Step.Signatures env)
    (eqDeclared : env.constants ``Eq = some eqSignature)
    (evalDeclared : env.constants ``HybridWord.Cmd.eval = some ⟨0,evalSignature⟩)
    (coverage : Conversion.Covers setup.conversion 0 (For.Casts setup))
    (inputs : InputsTyped env ctx p)
    {piece : Piece env ctx p reduced Mode.step.expected}
    (child : StructuralLoop.StepCasts inputs piece (Arithmetic.SourceCasts env) (For.Casts setup))
    (sourceRep : Represents source sourceCore)
    (sourceTyped : CastTyping env 0 (Arithmetic.SourceCasts env) ctx sourceCore (optionType Step.stepState))
    (transport : ∀ lhs,
      CastTyping env 0 (Arithmetic.SourceCasts env) ctx
        (.app (.app (.const ``Eq [.succ .zero]) (optionType Step.stepState)) lhs)
        (.forallE (optionType Step.stepState) (.sort .zero)) →
      For.Casts setup ctx (equalValues (optionType Step.stepState) lhs child.sourceCore.val)
        (equalValues (optionType Step.stepState) lhs sourceCore)) :
    ∃ result, retargetPiece setup.conversion .step source piece = some result ∧
      result.code = piece.code ∧
      Nonempty (StructuralLoop.StepCasts inputs result (Arithmetic.SourceCasts env) (For.Casts setup)) := by
  have evaluation := eval_cast_typed inputs evalDeclared child.target
  have prefixTyped := Step.equalityPrefix_typed steps eqDeclared evaluation
  have expectedRep := Step.expected_represents (evalCmd_represents inputs piece.represented.property) sourceRep
  have actualRep := Step.expected_represents (evalCmd_represents inputs piece.represented.property) child.sourceCore.property
  have actualSame := piece.checked.core.property.unique actualRep
  have cast : For.Casts setup ctx piece.checked.core.val
      (equalValues (optionType Step.stepState)
        (Step.lifted (bodyValue inputs.i.val inputs.x.val inputs.y.val piece.represented.val inputs.s.val inputs.ls.val))
        sourceCore) := by
    rw [actualSame]
    exact transport _ prefixTyped

  have typeTyped := CastTyping.application prefixTyped sourceTyped
  obtain ⟨checked,success,proofTyped⟩ := ScalarEnvironment.retarget_cast_complete piece.checked expectedRep
    child.proof (typeTyped.mono (fun _ _ _ h => .base (.base (.source h)))) cast
    coverage
  refine ⟨⟨piece.code,checked,piece.closed,piece.represented⟩,?_,rfl,?_⟩
  · exact congrArg (fun (o : Option (Artifact env ctx (stepExpected (evalCmd p piece.code) source))) =>
      o.bind (fun checked => some (⟨piece.code,checked,piece.closed,piece.represented⟩ :
        Piece env ctx p source Mode.step.expected))) success
  · exact ⟨⟨⟨_,sourceRep⟩,sourceTyped,child.target,proofTyped⟩⟩

theorem step_helper_retarget_complete {body : VExpr}
    (setup : Arithmetic.AliasSetup env)
    (steps : Step.Signatures env)
    (eqDeclared : env.constants ``Eq = some eqSignature)
    (evalDeclared : env.constants ``HybridWord.Cmd.eval = some ⟨0,evalSignature⟩)
    (coverage : Conversion.Covers setup.conversion 0 (For.Casts setup))
    (inputs : InputsTyped env ctx p)
    {piece : Piece env ctx p reduced Mode.step.expected}
    (child : StructuralLoop.StepCasts inputs piece (Arithmetic.SourceCasts env) (For.Casts setup))
    (domainTyped : CastTyping env 0 (Arithmetic.SourceCasts env) ctx domain (.sort u))
    (bodyTyped : CastTyping env 0 (Arithmetic.SourceCasts env) (domain::ctx) body bodyType)
    (argument : CastTyping env 0 (Arithmetic.SourceCasts env) ctx arg domain)
    (arguments : LeanTypeReduction.ArgumentsCasts env 0 (Arithmetic.SourceCasts env) ctx
      (bodyType.inst arg) args (optionType Step.stepState))
    (reducedRep : Represents reduced (args.foldl LeanTypeReduction.applyReduced (body.inst arg)))
    (sourceRep : Represents source (applications (.app (.lam domain body) arg) args))
    (form : Arithmetic.ValueForm setup ctx
      (args.foldl LeanTypeReduction.applyReduced (body.inst arg)) (optionType Step.stepState)) :
    ∃ result, retargetPiece setup.conversion .step source piece = some result ∧
      result.code = piece.code ∧
      Nonempty (StructuralLoop.StepCasts inputs result (Arithmetic.SourceCasts env) (For.Casts setup)) := by
  have sourceTyped : CastTyping env 0 (Arithmetic.SourceCasts env) ctx
      (applications (.app (.lam domain body) arg) args) (optionType Step.stepState) :=
    arguments.application_typed (.application (.lambda domainTyped bodyTyped) argument)
  have reducedSame := child.sourceCore.property.unique reducedRep
  exact step_helper_retarget_complete_transport setup steps eqDeclared evalDeclared coverage inputs child sourceRep sourceTyped (fun lhs prefixTyped => by
    rw [reducedSame]
    exact .helperEquality prefixTyped bodyTyped argument arguments (reducedSame ▸ child.value) form
      (by intro u; simp [optionType]))

/-- Retained scalar arguments use the shared administrative conversion rule.
The returned certificate keeps the invariant needed by enclosing constructs. -/
theorem step_helper_retained_retarget_complete {body : VExpr}
    (setup : Arithmetic.AliasSetup env)
    (steps : Step.Signatures env)
    (eqDeclared : env.constants ``Eq = some eqSignature)
    (evalDeclared : env.constants ``HybridWord.Cmd.eval = some ⟨0,evalSignature⟩)
    (coverage : Conversion.Covers setup.conversion 0 (For.Casts setup))
    (inputs : InputsTyped env ctx p)
    {piece : Piece env ctx p reduced Mode.step.expected}
    (child : StructuralLoop.StepCasts inputs piece (Arithmetic.SourceCasts env) (For.Casts setup))
    (domainTyped : CastTyping env 0 (Arithmetic.SourceCasts env) ctx domain (.sort u))
    (bodyTyped : CastTyping env 0 (Arithmetic.SourceCasts env) (domain::ctx) body (domains.foldr VExpr.forallE (optionType Step.stepState)))
    (argument : CheckedTyping env 0 (Arithmetic.SourceCasts env) ctx arg domain)
    (arguments : List.Forall₂ (fun domain arg =>
      CheckedTyping env 0 (Arithmetic.SourceCasts env) ctx arg domain) domains args)
    (typesClosed : ∀ n, ((domains.drop n).foldr VExpr.forallE (optionType Step.stepState)).ClosedN 0)
    (prefixTypes : ∀ before after, args = before ++ after → after ≠ [] →
      CastTyping env 0 (Arithmetic.SourceCasts env) ctx
        (before.foldl LeanTypeReduction.applyReduced (body.inst arg))
        ((domains.drop before.length).foldr VExpr.forallE (optionType Step.stepState)))
    (sourceRep : Represents source (applications (.app (.lam domain body) arg) args))
    (chain : RetainedConversion.Prefix env 0 (Arithmetic.SourceCasts env) (optionType Step.stepState)
      ctx child.sourceCore.val (args.foldl LeanTypeReduction.applyReduced (body.inst arg)) count) :
    ∃ result, retargetPiece setup.conversion .step source piece = some result ∧
      result.code = piece.code ∧
      Nonempty (StructuralLoop.StepCasts inputs result (Arithmetic.SourceCasts env) (For.Casts setup)) := by
  have initialClosed := typesClosed 0
  simp only [List.drop_zero] at initialClosed
  have sourceTyped : CastTyping env 0 (Arithmetic.SourceCasts env) ctx
      (applications (.app (.lam domain body) arg) args) (optionType Step.stepState) :=
    LeanTypeReduction.checked_spine_typed arguments typesClosed (by
      simpa only [initialClosed.instN_eq (Nat.zero_le _)] using
        CastTyping.checkedApplication (.lambda domainTyped bodyTyped) argument)
  exact step_helper_retarget_complete_transport setup steps eqDeclared evalDeclared coverage inputs child sourceRep sourceTyped (fun lhs prefixTyped => by
    exact .retainedEquality prefixTyped bodyTyped argument arguments typesClosed prefixTypes chain (by trivial))

theorem step_functionLet_complete {sourceBody functionValue : VExpr}
    (setup : Arithmetic.AliasSetup env)
    (steps : Step.Signatures env)
    (eqDeclared : env.constants ``Eq = some eqSignature)
    (evalDeclared : env.constants ``HybridWord.Cmd.eval = some ⟨0,evalSignature⟩)
    (stateFresh : ∀ r ∈ setup.rules, ``HybridWord.State ≠ r.name)
    (coverage : Conversion.Covers setup.conversion 0 (For.Casts setup))
    (exposure : Exposure env) (binder : Lean.Name) (ty value next : Lean.Expr) (flag : Bool)
    (inputs : InputsTyped env ctx p)
    (typeRep : Represents (σ.apply ty) (.forallE domain codomain))
    (typeTyped : CastTyping env 0 (Arithmetic.SourceCasts env) ctx (.forallE domain codomain) (.sort u))
    (bodyTyped : CastTyping env 0 (Arithmetic.SourceCasts env) ((.forallE domain codomain)::ctx)
      sourceBody (optionType Step.stepState))
    (valueTyped : CastTyping env 0 (Arithmetic.SourceCasts env) ctx functionValue (.forallE domain codomain))
    (reducedRep : Represents ((letSubstitution σ value).apply next) (sourceBody.inst functionValue))
    (sourceRep : Represents (σ.apply (.letE binder ty value next flag))
      (.app (.lam (.forallE domain codomain) sourceBody) functionValue))
    {piece : Piece env ctx p ((letSubstitution σ value).apply next) Mode.step.expected}
    (typed : StructuralLoop.StepCasts inputs piece (Arithmetic.SourceCasts env) (For.Casts setup))
    (form : Arithmetic.ValueForm setup ctx typed.sourceCore.val (optionType Step.stepState))
    (parsed :
      let raw := Lean.Expr.letE binder ty value next flag
      let recursor : Recursor env raw := fun nextCtx nextInputs nextMode bindings functions child =>
        visit env setup.conversion exposure child.val nextCtx nextInputs nextMode bindings functions
      let child : Child raw := ⟨value,by dsimp only [raw]; simp only [syntaxSize]; omega⟩
      visit env setup.conversion exposure next ctx p .step (letSubstitution σ value)
        (letContinuations fs (makeContinuation recursor ctx.length σ fs child)) = some piece) :
    ∃ result, visit env setup.conversion exposure (.letE binder ty value next flag) ctx p .step σ fs = some result ∧
      result.code = piece.code ∧
      ∃ typed : StructuralLoop.StepCasts inputs result (Arithmetic.SourceCasts env) (For.Casts setup),
        Arithmetic.ValueForm setup ctx typed.sourceCore.val (optionType Step.stepState) := by
  have notState : sameTerm (σ.apply ty) state = false := Bool.eq_false_iff.mpr (by
    intro same
    have impossible := sameTerm_sound typeRep (Represents.constant rfl : Represents state stateType) same
    cases impossible)
  have notWord : compatible env setup.conversion ctx (σ.apply ty) word = false := incompatible_of_conversion_none typeRep
    (Represents.constant rfl : Represents word wordType) (by intro h; cases h)
    (setup.function_word_none (ctx := ctx))
  have notStateCompatible : compatible env setup.conversion ctx (σ.apply ty) state = false := incompatible_of_conversion_none typeRep
    (Represents.constant rfl : Represents state stateType) (by intro h; cases h)
    (setup.function_state_none (ctx := ctx) stateFresh)
  have sameCore := typed.sourceCore.property.unique reducedRep
  obtain ⟨result,retargeted,codeSame,⟨resultTyped⟩⟩ := step_helper_retarget_complete setup
    steps eqDeclared evalDeclared coverage inputs typed typeTyped bodyTyped
    valueTyped (args := []) .nil reducedRep sourceRep (sameCore ▸ form)
  dsimp only at parsed
  refine ⟨result,?_,codeSame,resultTyped,?_⟩
  · rw [visit]
    have modeValue : (Mode.step == Mode.value) = false := rfl
    simp only [node,modeValue,Bool.false_eq_true,ite_false,letParts,notState,notWord,
      notStateCompatible,Bool.false_and,Bool.true_and,Bool.not_false,Bool.and_false,
      parsed,retargeted,bind,Option.bind,pure,Option.pure_def]
  · rw [resultTyped.sourceCore.property.unique sourceRep]
    exact .beta bodyTyped

end IRComparison.WordFrontend.FunctionSyntax
