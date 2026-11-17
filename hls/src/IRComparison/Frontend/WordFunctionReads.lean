import IRComparison.Frontend.WordFunctionLoops

namespace IRComparison.WordFrontend.FunctionSyntax
open Lean4Lean LeanTyped LeanTypeInference Certificate StructuralBody StructuralSyntax
set_option maxHeartbeats 1800000

theorem substitute_bindValue (σ : Substitution) :
    σ.apply (bindValueSource first (.lam binder word next info)) =
      bindValueSource (σ.apply first) (.lam binder word ((under σ).apply next) info) := by
  cases σ <;> rfl

theorem readWord_complete_code (setup : Arithmetic.AliasSetup env) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (fresh : ScopedSyntax.Fresh setup) (exposure : Exposure env)
    (inputs : InputsTyped env ctx p)
    {a : Piece env ctx p (σ.apply first) readExpected}
    (left : Read.ReadCasts inputs a (Arithmetic.SourceCasts env) (For.Casts setup))
    {b : Piece env (wordType::ctx) {p.lift with locals := .bvar 0::p.lift.locals} ((under σ).apply next) bodyExpected}
    (right : BodyCasts (inputs.nextWord closed library.scalars.word library.cons) b (Arithmetic.SourceCasts env) (For.Casts setup))
    (rightForm : Arithmetic.ValueForm setup (wordType::ctx) right.sourceCore.val (optionType stateType))
    (ha : readStep env setup.conversion exposure ctx p
      (ScalarEnvironment.parse env setup.conversion exposure ctx p) (σ.apply first) = some a)
    (hb : visit env setup.conversion exposure next (wordType::ctx) {p.lift with locals := .bvar 0::p.lift.locals}
      .body (under σ) (underFunctions fs) = some b)
    (binder : Lean.Name) (info : Lean.BinderInfo) :
    ∃ result, visit env setup.conversion exposure (bindValueSource first (.lam binder word next info))
        ctx p .body σ fs = some result ∧
      ∃ typed : BodyCasts inputs result (Arithmetic.SourceCasts env) (For.Casts setup),
        Arithmetic.ValueForm setup ctx typed.sourceCore.val (optionType stateType) ∧ result.code = app ``HybridWord.Cmd.letValue [a.code,b.code] := by
  have coverage := For.Casts.covered setup library.scalars.toSignatures library.steps closed
    library.cons library.eq library.eval fresh.state fresh.eq fresh.lift
  have embed : ∀ scope a b, Arithmetic.SourceCasts env scope a b → For.Casts setup scope a b :=
    fun _ _ _ h => .base (.base (.source h))
  obtain ⟨target,nextTyped,_⟩ := bindValue_next_typed inputs closed Arithmetic.SourceCasts.closed library.scalars.word library.cons right
  have beta : For.Casts setup ctx (bindValueNextActual inputs b.represented.val right.sourceCore.val)
      (bindValueContinuationType inputs b.represented.val (.lam wordType right.sourceCore.val)) :=
    .base (.base (.valueContinuation inputs target right.value rightForm))
  have assembled := bindValue_finish inputs closed Arithmetic.SourceCasts.closed embed library.scalars.word library.cons
    left right beta library.bindValueFact coverage exposure binder info
  have sourceSame := substitute_bindValue (first := first) (next := next) (binder := binder) (info := info) σ
  rw [← sourceSame] at assembled
  obtain ⟨artifact,checked,proofTyped,_,_⟩ := assembled
  let code := ClosedTerm.app ``HybridWord.Cmd.letValue [a.closedTerm,b.closedTerm]
  let result : Piece env ctx p (σ.apply (bindValueSource first (.lam binder word next info))) bodyExpected :=
    ⟨code.val,artifact,code.closed,code.represented⟩
  have src : Represents (σ.apply (bindValueSource first (.lam binder word next info)))
      (.app (.app valueBindHeader left.sourceCore.val) (.lam wordType right.sourceCore.val)) := by
    rw [sourceSame]
    exact .app (.app valueBind_represents left.sourceCore.property) (.lam (.constant rfl) right.sourceCore.property)
  have applied := CastTyping.checkedApplication ((library.bind.header_typed
    (domain := wordType) (result := stateType)
    (.constant library.scalars.word (by simp) rfl) (.constant library.steps.state (by simp) rfl)
    (by trivial) (by trivial)).withCasts (Arithmetic.SourceCasts env)) left.value
  simp only [optionType,wordType,stateType,VExpr.inst] at applied
  have sourceTyped := CastTyping.application applied nextTyped
  have constructor : CastTyping env 0 (Arithmetic.SourceCasts env) ctx
      (.const ``HybridWord.Cmd.letValue []) bindValueConstructor := .constant library.letValueConstructor (by simp) rfl
  have targetTyped := CastTyping.application (CastTyping.application constructor left.target) target
  let typed : BodyCasts inputs result (Arithmetic.SourceCasts env) (For.Casts setup) :=
    ⟨⟨_,src⟩,sourceTyped,targetTyped,proofTyped⟩
  refine ⟨result,?_,typed,?_,rfl⟩
  · have bodyValue : (Mode.body == Mode.value) = false := rfl
    have bodyStep : (Mode.body == Mode.step) = false := rfl
    have stateApply : σ.apply word = word := by cases σ <;> rfl
    have ss : sameTerm word word = true := sameTerm_complete (Represents.constant rfl) (Represents.constant rfl)
    have notState : sameTerm word state = false := rfl
    have su : sameTerm word (.const ``PUnit [.succ .zero]) = false := rfl
    have st : translate word = some ⟨wordType,Represents.constant rfl⟩ := rfl
    have stMapped : (translate (σ.apply word)).unattach = some wordType := by rw [stateApply]; rfl
    have sc : compatible env setup.conversion ctx word word = true :=
      compatible_same (Represents.constant rfl) (Represents.constant rfl) env setup.conversion ctx
    rw [visit]
    simp [node,bodyValue,bodyStep,letParts,applicationHead,makeContinuation,continuationParts,lambdaChain,
      ScalarEnvironment.arguments,ScalarEnvironment.below,lambdaParts,stateApply,
      bindValueSource,bindHead,Lean.mkAppN,Lean.mkApp2,Lean.mkApp,Lean.mkAppB,
      Lean.Expr.getAppFn,Lean.Expr.constName?,ss,notState,su,st]
    simp only [List.map_append,List.map_cons,List.map_nil,Function.comp_apply,
      List.cons_append,List.nil_append,List.length_cons,List.length_nil,Nat.reduceAdd,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.unattach_some,
      stMapped,sc,notState,ite_true,Option.bind_some,ha,hb]
    dsimp only [List.map,List.append,List.length,Function.comp_apply,List.getElem?_cons_zero,
      List.getElem?_cons_succ,Option.unattach]
    try simp only [ha,hb,Option.bind_some]
    have lambdaSame : σ.apply (.lam binder word next info) = .lam binder word ((under σ).apply next) info := by cases σ <;> rfl
    simp only [lambdaSame,finishBody,bind,Option.bind,pure,Option.pure_def]
    refine ⟨first,rfl,wordType,rfl,?_⟩
    rw [ha]
    dsimp only
    rw [hb]
    dsimp only
    simp only [Mode.expected,ClosedTerm.app,Piece.closedTerm,List.map_cons,List.map_nil,
      List.cons_append,List.nil_append,bindValueSource,bindHead,Lean.mkAppN,Lean.mkApp4,
      Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB] at checked ⊢
    rw [checked]
    rfl
  · exact .constant rfl (fresh.value _ (by simp)) (by decide)

theorem substitute_stepBindValue (σ : Substitution) :
    σ.apply (StructuralReadBind.bindValueSource first (.lam binder word next info)) =
      StructuralReadBind.bindValueSource (σ.apply first) (.lam binder word ((under σ).apply next) info) := by
  cases σ <;> rfl

theorem stepReadWord_complete_code (setup : Arithmetic.AliasSetup env) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (fresh : ScopedSyntax.Fresh setup) (exposure : Exposure env)
    (inputs : InputsTyped env ctx p)
    {a : Piece env ctx p (σ.apply first) readExpected}
    (left : Read.ReadCasts inputs a (Arithmetic.SourceCasts env) (For.Casts setup))
    {b : Piece env (wordType::ctx) {p.lift with locals := .bvar 0::p.lift.locals} ((under σ).apply next) Mode.step.expected}
    (right : StructuralLoop.StepCasts (inputs.nextWord closed library.scalars.word library.cons) b (Arithmetic.SourceCasts env) (For.Casts setup))
    (rightForm : Arithmetic.ValueForm setup (wordType::ctx) right.sourceCore.val (optionType Step.stepState))
    (ha : readStep env setup.conversion exposure ctx p
      (ScalarEnvironment.parse env setup.conversion exposure ctx p) (σ.apply first) = some a)
    (hb : visit env setup.conversion exposure next (wordType::ctx) {p.lift with locals := .bvar 0::p.lift.locals}
      .step (under σ) (underFunctions fs) = some b)
    (binder : Lean.Name) (info : Lean.BinderInfo) :
    ∃ result, visit env setup.conversion exposure (StructuralReadBind.bindValueSource first (.lam binder word next info))
        ctx p .step σ fs = some result ∧
      ∃ typed : StructuralLoop.StepCasts inputs result (Arithmetic.SourceCasts env) (For.Casts setup),
        Arithmetic.ValueForm setup ctx typed.sourceCore.val (optionType Step.stepState) ∧ result.code = app ``HybridWord.Cmd.letValue [a.code,b.code] := by
  have coverage := For.Casts.covered setup library.scalars.toSignatures library.steps closed
    library.cons library.eq library.eval fresh.state fresh.eq fresh.lift
  have embed : ∀ scope a b, Arithmetic.SourceCasts env scope a b → For.Casts setup scope a b :=
    fun _ _ _ h => .base (.base (.source h))
  obtain ⟨target,nextTyped,_⟩ := StructuralReadBind.bindValue_next_typed inputs closed Arithmetic.SourceCasts.closed library.scalars.word library.cons right
  have eval := eval_cast_typed (inputs.nextWord closed library.scalars.word library.cons) library.eval right.target
  have direct := For.Casts.directContinuation (setup := setup) .word eval right.value rightForm
  have codeClosed := b.represented.property.closed 0 b.closed
  have beta : For.Casts setup ctx (StructuralReadBind.bindValueNextActual inputs b.represented.val right.sourceCore.val)
      (StructuralReadBind.bindValueContinuationType inputs b.represented.val (.lam wordType right.sourceCore.val)) := by
    simpa only [StructuralReadBind.bindValueNextActual,StructuralReadBind.bindValueContinuationType,
      InputsTyped.nextWord,InputsTyped.lift,Step.Binder.core,Arithmetic.continuationValue,
      VExpr.lift,VExpr.liftN,wordType,codeClosed.liftN_eq (Nat.zero_le _)] using direct
  have assembled := StructuralReadBind.bindValue_finish inputs closed Arithmetic.SourceCasts.closed embed library.scalars.word library.cons
    left right beta library.stepBindValue coverage exposure binder info
  have sourceSame := substitute_stepBindValue (first := first) (next := next) (binder := binder) (info := info) σ
  rw [← sourceSame] at assembled
  obtain ⟨artifact,checked,proofTyped,_,_⟩ := assembled
  let code := ClosedTerm.app ``HybridWord.Cmd.letValue [a.closedTerm,b.closedTerm]
  let result : Piece env ctx p (σ.apply (StructuralReadBind.bindValueSource first (.lam binder word next info))) Mode.step.expected :=
    ⟨code.val,artifact,code.closed,code.represented⟩
  have src : Represents (σ.apply (StructuralReadBind.bindValueSource first (.lam binder word next info)))
      (.app (.app StructuralReadBind.valueBindHeader left.sourceCore.val) (.lam wordType right.sourceCore.val)) := by
    rw [sourceSame]
    exact .app (.app StructuralReadBind.valueBind_represents left.sourceCore.property) (.lam (.constant rfl) right.sourceCore.property)
  have applied := CastTyping.checkedApplication ((library.bind.header_typed
    (domain := wordType) (result := Step.stepState)
    (.constant library.scalars.word (by simp) rfl) library.steps.step_typed
    (by trivial) (by trivial)).withCasts (Arithmetic.SourceCasts env)) left.value
  simp only [optionType,wordType,stateType,Step.stepState,VExpr.inst] at applied
  have sourceTyped := CastTyping.application applied nextTyped
  have constructor : CastTyping env 0 (Arithmetic.SourceCasts env) ctx
      (.const ``HybridWord.Cmd.letValue []) bindValueConstructor := .constant library.letValueConstructor (by simp) rfl
  have targetTyped := CastTyping.application (CastTyping.application constructor left.target) target
  let typed : StructuralLoop.StepCasts inputs result (Arithmetic.SourceCasts env) (For.Casts setup) :=
    ⟨⟨_,src⟩,sourceTyped,targetTyped,proofTyped⟩
  refine ⟨result,?_,typed,?_,rfl⟩
  · have bodyValue : (Mode.step == Mode.value) = false := rfl
    have bodyStep : (Mode.step == Mode.step) = true := rfl
    have stateApply : σ.apply word = word := by cases σ <;> rfl
    have ss : sameTerm word word = true := sameTerm_complete (Represents.constant rfl) (Represents.constant rfl)
    have notState : sameTerm word state = false := rfl
    have su : sameTerm word (.const ``PUnit [.succ .zero]) = false := rfl
    have st : translate word = some ⟨wordType,Represents.constant rfl⟩ := rfl
    have stMapped : (translate (σ.apply word)).unattach = some wordType := by rw [stateApply]; rfl
    have sc : compatible env setup.conversion ctx word word = true :=
      compatible_same (Represents.constant rfl) (Represents.constant rfl) env setup.conversion ctx
    rw [visit]
    simp [node,bodyValue,bodyStep,letParts,applicationHead,makeContinuation,continuationParts,lambdaChain,
      ScalarEnvironment.arguments,ScalarEnvironment.below,lambdaParts,stateApply,
      StructuralReadBind.bindValueSource,bindHead,Lean.mkAppN,Lean.mkApp2,Lean.mkApp,Lean.mkAppB,
      Lean.Expr.getAppFn,Lean.Expr.constName?,ss,notState,su,st]
    simp only [List.map_append,List.map_cons,List.map_nil,Function.comp_apply,
      List.cons_append,List.nil_append,List.length_cons,List.length_nil,Nat.reduceAdd,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.unattach_some,
      stMapped,sc,notState,ite_true,Option.bind_some,ha,hb]
    dsimp only [List.map,List.append,List.length,Function.comp_apply,List.getElem?_cons_zero,
      List.getElem?_cons_succ,Option.unattach]
    try simp only [ha,hb,Option.bind_some]
    have lambdaSame : σ.apply (.lam binder word next info) = .lam binder word ((under σ).apply next) info := by cases σ <;> rfl
    simp only [lambdaSame,finishBody,bind,Option.bind,pure,Option.pure_def]
    refine ⟨first,rfl,wordType,rfl,?_⟩
    rw [ha]
    dsimp only
    rw [hb]
    dsimp only
    simp only [Mode.expected,ClosedTerm.app,Piece.closedTerm,List.map_cons,List.map_nil,
      List.cons_append,List.nil_append,StructuralReadBind.bindValueSource,bindHead,Lean.mkAppN,Lean.mkApp4,
      Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB] at checked ⊢
    rw [checked]
    rfl
  · exact .constant rfl (fresh.value _ (by simp)) (by decide)

end IRComparison.WordFrontend.FunctionSyntax
