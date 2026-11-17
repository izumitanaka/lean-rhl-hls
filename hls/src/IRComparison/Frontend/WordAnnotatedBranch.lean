import IRComparison.Frontend.WordFunctionLoops

/-! Nonzero conditions retain the type spelling produced by ordinary Lean
elaboration. Source computation and target commands are unchanged. -/
namespace IRComparison.WordFrontend.AnnotatedBranch
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic StructuralBody
set_option maxHeartbeats 2400000

def source (annotation : WordBinder.Annotation) (v d a b : Lean.Expr) : Lean.Expr :=
  Lean.mkApp5 (.const ``ite [.succ .zero]) (option state)
    (AnnotatedCondition.nativeCondition annotation v) d a b

theorem source_represents (annotation : WordBinder.Annotation)
    (vr : Represents v vc) (dr : Represents d dc) (ar : Represents a ac) (br : Represents b bc) :
    Represents (source annotation v d a b) (AnnotatedCondition.choice (optionType stateType) annotation vc dc ac bc) :=
  app_represents (.constant rfl) (.cons (.app (.constant rfl) (.constant rfl))
    (.cons (AnnotatedCondition.condition_represents annotation vr) (.cons dr (.cons ar (.cons br .nil)))))

theorem substitute_source (σ : Substitution) :
    σ.apply (source annotation v d a b) = source annotation (σ.apply v) (σ.apply d) (σ.apply a) (σ.apply b) := by
  cases σ <;> cases annotation <;> rfl

theorem finish_complete (setup : AliasSetup env) (library : ScopedSyntax.Library env)
    (fresh : ScopedSyntax.Fresh setup) (inputs : InputsTyped env ctx p)
    (annotation operand : WordBinder.Annotation)
    {e : Piece env ctx p v scalarExpected} (value : ScalarCasts inputs e (SourceCasts env) (For.Casts setup))
    {a : Piece env ctx p yes bodyExpected} (left : BodyCasts inputs a (SourceCasts env) (For.Casts setup))
    {b : Piece env ctx p no bodyExpected} (right : BodyCasts inputs b (SourceCasts env) (For.Casts setup))
    (valueTyped : CastTyping env 0 (SourceCasts env) ctx value.sourceCore.val operand.core)
    (valueForm : ValueForm setup ctx value.sourceCore.val operand.core)
    (leftForm : ValueForm setup ctx left.sourceCore.val (optionType stateType))
    (rightForm : ValueForm setup ctx right.sourceCore.val (optionType stateType))
    (decisionRep : Represents d dc)
    (decisionTyped : CastTyping env 0 (SourceCasts env) ctx dc
      (.app (.const ``Decidable []) (AnnotatedCondition.condition annotation value.sourceCore.val)))
    (decisionForm : ValueForm setup ctx dc
      (.app (.const ``Decidable []) (AnnotatedCondition.condition annotation value.sourceCore.val)))
    (coverage : Conversion.Covers conv 0 (For.Casts setup)) (exposure : Exposure env) :
    ∃ result, finish env conv exposure ctx
      (bodyExpected p (app ``HybridWord.Cmd.branch [e.code,a.code,b.code]) (source annotation v d yes no))
      (app ``HybridWord.Cmd.branch [e.code,a.code,b.code])
      (app ``WordFrontendFacts.branch ([e.code,a.code,b.code] ++ p.args ++
        [v,d,yes,no,e.checked.proof,a.checked.proof,b.checked.proof]))
      (e.checked.known.orElse (a.checked.known.orElse b.checked.known)) = some result ∧
      CastTyping env 0 (For.Casts setup) ctx result.proofCore.val result.core.val ∧
      result.code = app ``HybridWord.Cmd.branch [e.code,a.code,b.code] := by
  have embed : ∀ scope a b, SourceCasts env scope a b → For.Casts setup scope a b :=
    fun _ _ _ h => .base (.base (.source h))
  have targetRep := app_represents (f := Lean.Expr.const ``HybridWord.Cmd.branch []) (.constant rfl)
    (.cons e.represented.property (.cons a.represented.property (.cons b.represented.property .nil)))
  have srcRep := source_represents annotation value.sourceCore.property decisionRep left.sourceCore.property right.sourceCore.property
  have proofRep := app_represents (f := Lean.Expr.const ``WordFrontendFacts.branch []) (.constant rfl)
    (.cons e.represented.property (.cons a.represented.property (.cons b.represented.property
      (.cons inputs.i.property (.cons inputs.x.property (.cons inputs.y.property
        (.cons inputs.s.property (.cons inputs.ls.property
          (.cons value.sourceCore.property (.cons decisionRep (.cons left.sourceCore.property
            (.cons right.sourceCore.property (.cons e.checked.proofCore.property
              (.cons a.checked.proofCore.property (.cons b.checked.proofCore.property .nil)))))))))))))))
  have decCast : For.Casts setup ctx
      (.app (.const ``Decidable []) (AnnotatedCondition.condition annotation value.sourceCore.val))
      (.app (.const ``Decidable []) (Branch.condition value.sourceCore.val)) :=
    .condition (.decision library.decisions annotation .word operand valueTyped valueForm
      (fresh.condition _ (by simp)) (fresh.scalar _ (by simp [LexicalScalarSyntax.valueHeads])) fresh.eq (fresh.condition _ (by simp)))
  have fact := Branch.fact_typed inputs (value.inProofCasts embed) (left.inProofCasts embed)
    (right.inProofCasts embed) (.converted (decisionTyped.mono embed) decCast) library.branchFact
  have constructor : CastTyping env 0 (SourceCasts env) ctx (.const ``HybridWord.Cmd.branch []) Branch.constructorSignature :=
    .constant library.branchConstructor (by simp) rfl
  have target := CastTyping.application (CastTyping.application (CastTyping.application constructor value.target) left.target) right.target
  have lhs := eval_cast_typed inputs library.eval target
  have pref := CastTyping.application
    ((equality_head_typed library.returns.state library.returns.option library.eq).withCasts (SourceCasts env)) lhs
  simp only [optionState,stateType,VExpr.inst] at pref
  have rule : For.Casts setup ctx
      (equalValues (optionType stateType)
        (bodyValue inputs.i.val inputs.x.val inputs.y.val
          (applications (.const ``HybridWord.Cmd.branch []) [e.represented.val,a.represented.val,b.represented.val]) inputs.s.val inputs.ls.val)
        (Branch.choice value.sourceCore.val dc left.sourceCore.val right.sourceCore.val))
      (equalValues (optionType stateType)
        (bodyValue inputs.i.val inputs.x.val inputs.y.val
          (applications (.const ``HybridWord.Cmd.branch []) [e.represented.val,a.represented.val,b.represented.val]) inputs.s.val inputs.ls.val)
        (AnnotatedCondition.choice (optionType stateType) annotation value.sourceCore.val dc left.sourceCore.val right.sourceCore.val)) :=
    .annotatedChoice ⟨library.decisions,operand,valueTyped,valueForm,library.toLibrary.option_typed,by trivial,
      decisionTyped,decisionForm,left.value,right.value,leftForm,rightForm,(by intro u h; cases h),library.ite,
      fresh.condition _ (by simp),fresh.scalar _ (by simp [LexicalScalarSyntax.valueHeads]),fresh.eq,
      fresh.condition _ (by simp),fresh.value _ (by simp),pref⟩
  have srcTyped := Branch.ite_typed library.toLibrary.option_typed (by trivial)
    (AnnotatedCondition.condition_typed library.decisions library.scalars.toSignatures annotation value.value).1
    decisionTyped (.exact left.value) (.exact right.value) library.ite
  have expected := CastTyping.application pref srcTyped
  exact finish_checked_complete (bodyExpected_represents inputs targetRep srcRep) proofRep
    (.converted fact rule) (expected.mono embed)
    ((known_casts e.checked value.proof).orElse ((known_casts a.checked left.proof).orElse (known_casts b.checked right.proof)))
    coverage exposure _


theorem visit_complete_code (setup : Arithmetic.AliasSetup env) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (fresh : ScopedSyntax.Fresh setup) (exposure : Exposure env)
    (inputs : InputsTyped env ctx p) (annotation operand : WordBinder.Annotation)
    {e : Piece env ctx p (σ.apply v) scalarExpected}
    (value : ScalarCasts inputs e (Arithmetic.SourceCasts env) (For.Casts setup))
    {a : Piece env ctx p (σ.apply yes) bodyExpected}
    (left : BodyCasts inputs a (Arithmetic.SourceCasts env) (For.Casts setup))
    {b : Piece env ctx p (σ.apply no) bodyExpected}
    (right : BodyCasts inputs b (Arithmetic.SourceCasts env) (For.Casts setup))
    (decisionRep : Represents (σ.apply d) dc)
    (valueTyped : CastTyping env 0 (SourceCasts env) ctx value.sourceCore.val operand.core)
    (valueForm : ValueForm setup ctx value.sourceCore.val operand.core)
    (leftForm : ValueForm setup ctx left.sourceCore.val (optionType stateType))
    (rightForm : ValueForm setup ctx right.sourceCore.val (optionType stateType))
    (decisionTyped : CastTyping env 0 (SourceCasts env) ctx dc
      (.app (.const ``Decidable []) (AnnotatedCondition.condition annotation value.sourceCore.val)))
    (decisionForm : ValueForm setup ctx dc
      (.app (.const ``Decidable []) (AnnotatedCondition.condition annotation value.sourceCore.val)))
    (he : ScalarEnvironment.parse env setup.conversion exposure ctx p (σ.apply v) = some e)
    (ha : visit env setup.conversion exposure yes ctx p .body σ fs = some a)
    (hb : visit env setup.conversion exposure no ctx p .body σ fs = some b) :
    ∃ result, visit env setup.conversion exposure (source annotation v d yes no) ctx p .body σ fs = some result ∧
      ∃ typed : BodyCasts inputs result (Arithmetic.SourceCasts env) (For.Casts setup),
        Arithmetic.ValueForm setup ctx typed.sourceCore.val (optionType stateType) ∧ result.code = app ``HybridWord.Cmd.branch [e.code,a.code,b.code] := by
  have coverage := For.Casts.covered setup library.scalars.toSignatures library.steps closed
    library.cons library.eq library.eval fresh.state fresh.eq fresh.lift
  have embed : ∀ scope a b, Arithmetic.SourceCasts env scope a b → For.Casts setup scope a b :=
    fun _ _ _ h => .base (.base (.source h))
  have assembled := finish_complete setup library fresh inputs annotation operand value left right
    valueTyped valueForm leftForm rightForm decisionRep decisionTyped decisionForm coverage exposure
  let code := ClosedTerm.app ``HybridWord.Cmd.branch [e.closedTerm,a.closedTerm,b.closedTerm]
  have represented := source_represents annotation value.sourceCore.property decisionRep left.sourceCore.property right.sourceCore.property
  have sourceSame := substitute_source (annotation := annotation) (v := v) (d := d) (a := yes) (b := no) σ
  rw [← sourceSame] at represented assembled
  obtain ⟨artifact,checked,proofTyped,_⟩ := assembled
  let result : Piece env ctx p (σ.apply (source annotation v d yes no)) bodyExpected :=
    ⟨code.val,artifact,code.closed,code.represented⟩
  have target : CastTyping env 0 (Arithmetic.SourceCasts env) ctx
      (applications (.const ``HybridWord.Cmd.branch []) [e.represented.val,a.represented.val,b.represented.val]) cmdType := by
    have h : CastTyping env 0 (Arithmetic.SourceCasts env) ctx (.const ``HybridWord.Cmd.branch []) Branch.constructorSignature :=
      .constant library.branchConstructor (by simp) rfl
    exact .application (.application (.application h value.target) left.target) right.target
  let typed : BodyCasts inputs result (Arithmetic.SourceCasts env) (For.Casts setup) :=
    ⟨⟨_,represented⟩,Branch.ite_typed library.toLibrary.option_typed (by trivial)
      (AnnotatedCondition.condition_typed library.decisions library.scalars.toSignatures annotation value.value).1 decisionTyped
      (.exact left.value) (.exact right.value) library.ite,target,proofTyped⟩
  refine ⟨result,?_,typed,?_,rfl⟩
  · rw [visit]
    have bodyValue : (Mode.body == Mode.value) = false := rfl
    have bodyStep : (Mode.body == Mode.step) = false := rfl
    simp only [node,bodyValue,bodyStep]
    cases annotation <;>
      simp [letParts,applicationHead,makeContinuation,continuationParts,lambdaChain,
      ScalarEnvironment.arguments,ScalarEnvironment.below,source,AnnotatedCondition.nativeCondition,AnnotatedCondition.nativeTest,AnnotatedCondition.nativeHeader,AnnotatedLiteral.native,WordBinder.Annotation.native,
      Lean.mkApp5,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB,
      Lean.Expr.getAppFn,Lean.Expr.constName?]
    all_goals
      simp only [Option.bind_some,he,ha,hb]
      refine ⟨v,rfl,e,he,a,rfl,b,rfl,?_⟩
      simp only [finishBody,bind,Option.bind,pure,Option.pure_def]
      simp only [Mode.expected,ClosedTerm.app,ClosedTerm.const,Piece.closedTerm,List.map_cons,List.map_nil,
        List.cons_append,List.nil_append,source,AnnotatedCondition.nativeCondition,AnnotatedCondition.nativeTest,
        AnnotatedCondition.nativeHeader,AnnotatedLiteral.native,WordBinder.Annotation.native,
        Lean.mkApp5,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB] at checked ⊢
      rw [checked]
      rfl
  · change Arithmetic.ValueForm setup ctx _ _
    exact .constant rfl (fresh.value _ (by simp)) (by decide)

namespace Loop

def source (annotation : WordBinder.Annotation) (v d a b : Lean.Expr) : Lean.Expr :=
  Lean.mkApp5 (.const ``ite [.succ .zero]) (option stepType)
    (AnnotatedCondition.nativeCondition annotation v) d a b

theorem source_represents (annotation : WordBinder.Annotation)
    (vr : Represents v vc) (dr : Represents d dc) (ar : Represents a ac) (br : Represents b bc) :
    Represents (source annotation v d a b) (AnnotatedCondition.choice (optionType Step.stepState) annotation vc dc ac bc) :=
  app_represents (.constant rfl) (.cons (.app (.constant rfl) (.app (.constant rfl) (.constant rfl)))
    (.cons (AnnotatedCondition.condition_represents annotation vr) (.cons dr (.cons ar (.cons br .nil)))))

theorem substitute_source (σ : Substitution) :
    σ.apply (source annotation v d a b) = source annotation (σ.apply v) (σ.apply d) (σ.apply a) (σ.apply b) := by
  cases σ <;> cases annotation <;> rfl

theorem finish_complete (setup : AliasSetup env) (library : ScopedSyntax.Library env)
    (fresh : ScopedSyntax.Fresh setup) (inputs : InputsTyped env ctx p)
    (annotation operand : WordBinder.Annotation)
    {e : Piece env ctx p v scalarExpected} (value : ScalarCasts inputs e (SourceCasts env) (For.Casts setup))
    {a : Piece env ctx p yes Mode.step.expected} (left : StructuralLoop.StepCasts inputs a (SourceCasts env) (For.Casts setup))
    {b : Piece env ctx p no Mode.step.expected} (right : StructuralLoop.StepCasts inputs b (SourceCasts env) (For.Casts setup))
    (valueTyped : CastTyping env 0 (SourceCasts env) ctx value.sourceCore.val operand.core)
    (valueForm : ValueForm setup ctx value.sourceCore.val operand.core)
    (leftForm : ValueForm setup ctx left.sourceCore.val (optionType Step.stepState))
    (rightForm : ValueForm setup ctx right.sourceCore.val (optionType Step.stepState))
    (decisionRep : Represents d dc)
    (decisionTyped : CastTyping env 0 (SourceCasts env) ctx dc
      (.app (.const ``Decidable []) (AnnotatedCondition.condition annotation value.sourceCore.val)))
    (decisionForm : ValueForm setup ctx dc
      (.app (.const ``Decidable []) (AnnotatedCondition.condition annotation value.sourceCore.val)))
    (coverage : Conversion.Covers conv 0 (For.Casts setup)) (exposure : Exposure env) :
    ∃ result, finish env conv exposure ctx
      (Mode.step.expected p (app ``HybridWord.Cmd.branch [e.code,a.code,b.code]) (source annotation v d yes no))
      (app ``HybridWord.Cmd.branch [e.code,a.code,b.code])
      (app ``WordLoopFacts.branchCmd ([e.code,a.code,b.code] ++ p.args ++
        [v,d,yes,no,e.checked.proof,a.checked.proof,b.checked.proof]))
      (e.checked.known.orElse (a.checked.known.orElse b.checked.known)) = some result ∧
      CastTyping env 0 (For.Casts setup) ctx result.proofCore.val result.core.val ∧
      result.code = app ``HybridWord.Cmd.branch [e.code,a.code,b.code] := by
  have embed : ∀ scope a b, SourceCasts env scope a b → For.Casts setup scope a b :=
    fun _ _ _ h => .base (.base (.source h))
  have targetRep := app_represents (f := Lean.Expr.const ``HybridWord.Cmd.branch []) (.constant rfl)
    (.cons e.represented.property (.cons a.represented.property (.cons b.represented.property .nil)))
  have srcRep := source_represents annotation value.sourceCore.property decisionRep left.sourceCore.property right.sourceCore.property
  have proofRep := app_represents (f := Lean.Expr.const ``WordLoopFacts.branchCmd []) (.constant rfl)
    (.cons e.represented.property (.cons a.represented.property (.cons b.represented.property
      (.cons inputs.i.property (.cons inputs.x.property (.cons inputs.y.property
        (.cons inputs.s.property (.cons inputs.ls.property
          (.cons value.sourceCore.property (.cons decisionRep (.cons left.sourceCore.property
            (.cons right.sourceCore.property (.cons e.checked.proofCore.property
              (.cons a.checked.proofCore.property (.cons b.checked.proofCore.property .nil)))))))))))))))
  have decCast : For.Casts setup ctx
      (.app (.const ``Decidable []) (AnnotatedCondition.condition annotation value.sourceCore.val))
      (.app (.const ``Decidable []) (Branch.condition value.sourceCore.val)) :=
    .condition (.decision library.decisions annotation .word operand valueTyped valueForm
      (fresh.condition _ (by simp)) (fresh.scalar _ (by simp [LexicalScalarSyntax.valueHeads])) fresh.eq (fresh.condition _ (by simp)))
  have fact := StructuralStep.Conditional.fact_typed inputs (value.inProofCasts embed) (left.inProofCasts embed)
    (right.inProofCasts embed) (.converted (decisionTyped.mono embed) decCast) library.stepBranch
  have constructor : CastTyping env 0 (SourceCasts env) ctx (.const ``HybridWord.Cmd.branch []) Branch.constructorSignature :=
    .constant library.branchConstructor (by simp) rfl
  have target := CastTyping.application (CastTyping.application (CastTyping.application constructor value.target) left.target) right.target
  have lhs := eval_cast_typed inputs library.eval target
  have pref := Step.equalityPrefix_typed library.steps library.eq lhs
  have rule : For.Casts setup ctx
      (equalValues (optionType Step.stepState)
        (Step.lifted (bodyValue inputs.i.val inputs.x.val inputs.y.val
          (applications (.const ``HybridWord.Cmd.branch []) [e.represented.val,a.represented.val,b.represented.val]) inputs.s.val inputs.ls.val))
        (StructuralStep.Conditional.choice value.sourceCore.val dc left.sourceCore.val right.sourceCore.val))
      (equalValues (optionType Step.stepState)
        (Step.lifted (bodyValue inputs.i.val inputs.x.val inputs.y.val
          (applications (.const ``HybridWord.Cmd.branch []) [e.represented.val,a.represented.val,b.represented.val]) inputs.s.val inputs.ls.val))
        (AnnotatedCondition.choice (optionType Step.stepState) annotation value.sourceCore.val dc left.sourceCore.val right.sourceCore.val)) :=
    .annotatedChoice ⟨library.decisions,operand,valueTyped,valueForm,library.stepOption_typed,by trivial,
      decisionTyped,decisionForm,left.value,right.value,leftForm,rightForm,(by intro u h; cases h),library.ite,
      fresh.condition _ (by simp),fresh.scalar _ (by simp [LexicalScalarSyntax.valueHeads]),fresh.eq,
      fresh.condition _ (by simp),fresh.value _ (by simp),pref⟩
  have srcTyped := Branch.ite_typed library.stepOption_typed (by trivial)
    (AnnotatedCondition.condition_typed library.decisions library.scalars.toSignatures annotation value.value).1
    decisionTyped (.exact left.value) (.exact right.value) library.ite
  have expected := CastTyping.application pref srcTyped
  exact finish_checked_complete (Step.expected_represents (evalCmd_represents inputs targetRep) srcRep) proofRep
    (.converted fact rule) (expected.mono embed)
    ((known_casts e.checked value.proof).orElse ((known_casts a.checked left.proof).orElse (known_casts b.checked right.proof)))
    coverage exposure _


theorem visit_complete_code (setup : Arithmetic.AliasSetup env) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (fresh : ScopedSyntax.Fresh setup) (exposure : Exposure env)
    (inputs : InputsTyped env ctx p) (annotation operand : WordBinder.Annotation)
    {e : Piece env ctx p (σ.apply v) scalarExpected}
    (value : ScalarCasts inputs e (Arithmetic.SourceCasts env) (For.Casts setup))
    {a : Piece env ctx p (σ.apply yes) Mode.step.expected}
    (left : StructuralLoop.StepCasts inputs a (Arithmetic.SourceCasts env) (For.Casts setup))
    {b : Piece env ctx p (σ.apply no) Mode.step.expected}
    (right : StructuralLoop.StepCasts inputs b (Arithmetic.SourceCasts env) (For.Casts setup))
    (decisionRep : Represents (σ.apply d) dc)
    (valueTyped : CastTyping env 0 (SourceCasts env) ctx value.sourceCore.val operand.core)
    (valueForm : ValueForm setup ctx value.sourceCore.val operand.core)
    (leftForm : ValueForm setup ctx left.sourceCore.val (optionType Step.stepState))
    (rightForm : ValueForm setup ctx right.sourceCore.val (optionType Step.stepState))
    (decisionTyped : CastTyping env 0 (SourceCasts env) ctx dc
      (.app (.const ``Decidable []) (AnnotatedCondition.condition annotation value.sourceCore.val)))
    (decisionForm : ValueForm setup ctx dc
      (.app (.const ``Decidable []) (AnnotatedCondition.condition annotation value.sourceCore.val)))
    (he : ScalarEnvironment.parse env setup.conversion exposure ctx p (σ.apply v) = some e)
    (ha : visit env setup.conversion exposure yes ctx p .step σ fs = some a)
    (hb : visit env setup.conversion exposure no ctx p .step σ fs = some b) :
    ∃ result, visit env setup.conversion exposure (source annotation v d yes no) ctx p .step σ fs = some result ∧
      ∃ typed : StructuralLoop.StepCasts inputs result (Arithmetic.SourceCasts env) (For.Casts setup),
        Arithmetic.ValueForm setup ctx typed.sourceCore.val (optionType Step.stepState) ∧ result.code = app ``HybridWord.Cmd.branch [e.code,a.code,b.code] := by
  have coverage := For.Casts.covered setup library.scalars.toSignatures library.steps closed
    library.cons library.eq library.eval fresh.state fresh.eq fresh.lift
  have embed : ∀ scope a b, Arithmetic.SourceCasts env scope a b → For.Casts setup scope a b :=
    fun _ _ _ h => .base (.base (.source h))
  have assembled := finish_complete setup library fresh inputs annotation operand value left right
    valueTyped valueForm leftForm rightForm decisionRep decisionTyped decisionForm coverage exposure
  let code := ClosedTerm.app ``HybridWord.Cmd.branch [e.closedTerm,a.closedTerm,b.closedTerm]
  have represented := source_represents annotation value.sourceCore.property decisionRep left.sourceCore.property right.sourceCore.property
  have sourceSame := substitute_source (annotation := annotation) (v := v) (d := d) (a := yes) (b := no) σ
  rw [← sourceSame] at represented assembled
  obtain ⟨artifact,checked,proofTyped,_⟩ := assembled
  let result : Piece env ctx p (σ.apply (source annotation v d yes no)) Mode.step.expected :=
    ⟨code.val,artifact,code.closed,code.represented⟩
  have target : CastTyping env 0 (Arithmetic.SourceCasts env) ctx
      (applications (.const ``HybridWord.Cmd.branch []) [e.represented.val,a.represented.val,b.represented.val]) cmdType := by
    have h : CastTyping env 0 (Arithmetic.SourceCasts env) ctx (.const ``HybridWord.Cmd.branch []) Branch.constructorSignature :=
      .constant library.branchConstructor (by simp) rfl
    exact .application (.application (.application h value.target) left.target) right.target
  let typed : StructuralLoop.StepCasts inputs result (Arithmetic.SourceCasts env) (For.Casts setup) :=
    ⟨⟨_,represented⟩,Branch.ite_typed library.stepOption_typed (by trivial)
      (AnnotatedCondition.condition_typed library.decisions library.scalars.toSignatures annotation value.value).1 decisionTyped
      (.exact left.value) (.exact right.value) library.ite,target,proofTyped⟩
  refine ⟨result,?_,typed,?_,rfl⟩
  · rw [visit]
    have bodyValue : (Mode.step == Mode.value) = false := rfl
    have bodyStep : (Mode.step == Mode.step) = true := rfl
    simp only [node,bodyValue,bodyStep]
    cases annotation <;>
      simp [letParts,applicationHead,makeContinuation,continuationParts,lambdaChain,
      ScalarEnvironment.arguments,ScalarEnvironment.below,source,AnnotatedCondition.nativeCondition,AnnotatedCondition.nativeTest,AnnotatedCondition.nativeHeader,AnnotatedLiteral.native,WordBinder.Annotation.native,
      Lean.mkApp5,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB,
      Lean.Expr.getAppFn,Lean.Expr.constName?]
    all_goals
      simp only [Option.bind_some,he,ha,hb]
      refine ⟨v,rfl,e,he,a,rfl,b,rfl,?_⟩
      simp only [finishBody,bind,Option.bind,pure,Option.pure_def]
      simp only [Mode.expected,ClosedTerm.app,ClosedTerm.const,Piece.closedTerm,List.map_cons,List.map_nil,
        List.cons_append,List.nil_append,source,AnnotatedCondition.nativeCondition,AnnotatedCondition.nativeTest,
        AnnotatedCondition.nativeHeader,AnnotatedLiteral.native,WordBinder.Annotation.native,
        Lean.mkApp5,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB] at checked ⊢
      rw [checked]
      rfl
  · change Arithmetic.ValueForm setup ctx _ _
    exact .constant rfl (fresh.value _ (by simp)) (by decide)

end Loop

end IRComparison.WordFrontend.AnnotatedBranch
