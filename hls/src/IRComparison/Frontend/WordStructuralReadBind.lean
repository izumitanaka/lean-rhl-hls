import IRComparison.Frontend.WordStructuralStep

/-! Successful composition of an Option-valued read and its value continuation.
The input is the ordinary elaborated Lean bind, not a new source language. -/
namespace IRComparison.WordFrontend.StructuralReadBind
open Lean4Lean LeanTyped LeanTypeInference Certificate StructuralBody StructuralLoop
variable {casts proofCasts : TypeCasts} [Arithmetic.Includes casts] [Arithmetic.Includes proofCasts]
set_option maxHeartbeats 800000

def valueBindHeader : VExpr := optionBindHeader wordType Step.stepState

theorem valueBind_represents : Represents (bindHead word stepType) valueBindHeader := by
  exact .app (.app (.app (.app (.constant rfl) (.constant rfl))
    (.app (.app (.constant rfl) (.constant rfl)) (.constant rfl))) (.constant rfl)) (.app (.constant rfl) (.constant rfl))

theorem valueBind_inst (v : VExpr) (k : Nat) : valueBindHeader.inst v k = valueBindHeader :=
  (valueBind_represents.closed 0 rfl).instN_eq (Nat.zero_le k)

def bindValueFirstPremise : VExpr := equalValues (optionType wordType)
  (scalarValue (.bvar 6) (.bvar 5) (.bvar 4) (.bvar 3) (.bvar 2) (.bvar 8)) (.bvar 1)
def bindValueNextPremise : VExpr := .forallE wordType
  (Step.expected
    (bodyValue (.bvar 8) (.bvar 7) (.bvar 6) (.bvar 9) (.bvar 5)
      (applications (.const ``List.cons [.zero]) [wordType,.bvar 0,.bvar 4]))
    (.app (.bvar 2) (.bvar 0)))
def bindValueResult : VExpr := Step.expected
  (bodyValue (.bvar 8) (.bvar 7) (.bvar 6)
    (applications (.const ``HybridWord.Cmd.letValue []) [.bvar 10,.bvar 9]) (.bvar 5) (.bvar 4))
  (applications valueBindHeader [.bvar 3,.bvar 2])
def bindValueSignature : VExpr := .forallE exprType (.forallE cmdType
  (inputsType (.forallE (optionType wordType)
    (.forallE (.forallE wordType (optionType Step.stepState))
      (.forallE bindValueFirstPremise (.forallE bindValueNextPremise bindValueResult))))))

def bindValueContinuationType (inputs : InputsTyped env ctx p) (b next : VExpr) : VExpr :=
  .forallE wordType (Step.expected
    (bodyValue inputs.i.val.lift inputs.x.val.lift inputs.y.val.lift b.lift
      inputs.s.val.lift (applications (.const ``List.cons [.zero]) [wordType,.bvar 0,inputs.ls.val.lift]))
    (.app next.lift (.bvar 0)))

theorem bindValue_typed (inputs : InputsTyped env ctx p)
    {a : Piece env ctx p first readExpected} (left : Read.ReadCasts inputs a casts)
    (rightTarget : CastTyping env 0 casts ctx b cmdType)
    (nextTyped : CheckedTyping env 0 casts ctx next (.forallE wordType (optionType Step.stepState)))
    (nextProof : CastTyping env 0 casts ctx proofNext actual)
    (beta : casts ctx actual (bindValueContinuationType inputs b next))
    (registered : env.constants ``WordLoopFacts.bindValue = some ⟨0,bindValueSignature⟩) :
    CastTyping env 0 casts ctx
      (applications (.const ``WordLoopFacts.bindValue [])
        ([a.represented.val,b] ++ inputs.args ++
          [left.sourceCore.val,next,a.checked.proofCore.val,proofNext]))
      (Step.expected
        (bodyValue inputs.i.val inputs.x.val inputs.y.val
          (applications (.const ``HybridWord.Cmd.letValue []) [a.represented.val,b]) inputs.s.val inputs.ls.val)
        (applications valueBindHeader [left.sourceCore.val,next])) := by
  have fact : CastTyping env 0 casts ctx (.const ``WordLoopFacts.bindValue []) bindValueSignature :=
    .constant (levels := []) registered (by simp) rfl
  have a1 := CastTyping.application fact left.target
  simp only [Step.expected,Step.lifted,Step.stepState,bindValueSignature,inputsType,exprType,cmdType,wordType,stateType,wordsType,optionType,VExpr.inst] at a1
  have a2 := CastTyping.application a1 rightTarget
  simp only [Step.expected,Step.lifted,Step.stepState,VExpr.inst] at a2
  have a3 := inputs.apply_casts a2
  simp only [Step.expected,Step.lifted,Step.stepState,InputsTyped.instantiate,bindValueFirstPremise,bindValueNextPremise,bindValueResult,
    bodyValue,scalarValue,equalValues,optionType,stateType,wordType,applications,Nat.reduceAdd,
    ← VExpr.lift_instN_lo,VExpr.inst_lift,valueBind_inst,VExpr.inst,
    VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] at a3
  have a4 := CastTyping.checkedApplication a3 left.value
  simp only [Step.expected,Step.lifted,Step.stepState,Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst_lift,valueBind_inst,VExpr.inst,
    VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] at a4
  have a5 := CastTyping.checkedApplication a4 nextTyped
  simp only [Step.expected,Step.lifted,Step.stepState,Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst_lift,valueBind_inst,VExpr.inst,
    VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] at a5
  have a6 := CastTyping.application a5 left.equality
  simp only [Step.expected,Step.lifted,Step.stepState,Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst_lift,valueBind_inst,VExpr.inst,
    VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] at a6
  have cast := beta
  simp only [Step.expected,Step.lifted,Step.stepState,bindValueContinuationType,bodyValue,scalarValue,equalValues,applications,optionType,wordType,stateType] at cast
  simpa only [InputsTyped.args,applications,List.cons_append,List.nil_append,bodyValue,
    equalValues,optionType,wordType,stateType,Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst_lift,
    valueBind_inst,VExpr.inst,VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] using
    CastTyping.convertedApplication a6 nextProof cast

def bindValueNextActual (inputs : InputsTyped env ctx p) (b source : VExpr) : VExpr :=
  .forallE wordType (Step.expected
    (bodyValue inputs.i.val.lift inputs.x.val.lift inputs.y.val.lift b.lift
      inputs.s.val.lift (applications (.const ``List.cons [.zero]) [wordType,.bvar 0,inputs.ls.val.lift])) source)

theorem bindValue_next_typed (inputs : InputsTyped env ctx p)
    (closed : ClosedConstantTypes env) (stable : ClosedCasts casts)
    (wordDeclared : env.constants ``HybridWord.Word = some ⟨0,.sort (.succ .zero)⟩)
    (consDeclared : env.constants ``List.cons = some consSignature)
    {b : Piece env (wordType::ctx) {p.lift with locals := .bvar 0 :: p.lift.locals} nextBody Mode.step.expected}
    (right : StepCasts (inputs.nextWord closed wordDeclared consDeclared) b casts proofCasts) :
    CastTyping env 0 casts ctx b.represented.val cmdType ∧
    CastTyping env 0 casts ctx (.lam wordType right.sourceCore.val)
      (.forallE wordType (optionType Step.stepState)) ∧
    CastTyping env 0 proofCasts ctx (.lam wordType b.checked.proofCore.val)
      (bindValueNextActual inputs b.represented.val right.sourceCore.val) := by
  have targetClosed : b.represented.val.ClosedN 0 := b.represented.property.closed 0 b.closed
  have wordTyped : DirectTyping env 0 ctx wordType (.sort (.succ .zero)) :=
    .constant wordDeclared (by simp) rfl
  refine ⟨right.target.closed_context stable targetClosed ctx,
    .lambda (wordTyped.withCasts casts) right.value,?_⟩
  have proof := CastTyping.lambda (wordTyped.withCasts proofCasts) right.equality
  simpa only [bindValueNextActual,InputsTyped.nextWord,InputsTyped.lift,
    targetClosed.lift_eq] using proof

def bindValueSource (first next : Lean.Expr) : Lean.Expr := Lean.mkApp2 (bindHead word stepType) first next

theorem bindValue_finish (inputs : InputsTyped env ctx p)
    (closed : ClosedConstantTypes env) (stable : ClosedCasts casts)
    (embeds : ∀ scope a b, casts scope a b → proofCasts scope a b)
    (wordDeclared : env.constants ``HybridWord.Word = some ⟨0,.sort (.succ .zero)⟩)
    (consDeclared : env.constants ``List.cons = some consSignature)
    {a : Piece env ctx p first readExpected} (left : Read.ReadCasts inputs a casts proofCasts)
    {b : Piece env (wordType::ctx) {p.lift with locals := .bvar 0 :: p.lift.locals} nextBody Mode.step.expected}
    (right : StepCasts (inputs.nextWord closed wordDeclared consDeclared) b casts proofCasts)
    (beta : proofCasts ctx (bindValueNextActual inputs b.represented.val right.sourceCore.val)
      (bindValueContinuationType inputs b.represented.val (.lam wordType right.sourceCore.val)))
    (registered : env.constants ``WordLoopFacts.bindValue = some ⟨0,bindValueSignature⟩)
    (coverage : Conversion.Covers conv 0 proofCasts) (exposure : Exposure env)
    (binder : Lean.Name) (info : Lean.BinderInfo) :
    ∃ result, finish env conv exposure ctx
      (Mode.step.expected p (app ``HybridWord.Cmd.letValue [a.code,b.code])
        (bindValueSource first (.lam binder word nextBody info)))
      (app ``HybridWord.Cmd.letValue [a.code,b.code])
      (app ``WordLoopFacts.bindValue ([a.code,b.code] ++ p.args ++
        [first,.lam binder word nextBody info,a.checked.proof,.lam binder word b.checked.proof info]))
      (a.checked.known.orElse b.checked.known) = some result ∧
      CastTyping env 0 proofCasts ctx result.proofCore.val result.core.val ∧
      result.code = app ``HybridWord.Cmd.letValue [a.code,b.code] ∧
      result.proof = app ``WordLoopFacts.bindValue ([a.code,b.code] ++ p.args ++
        [first,.lam binder word nextBody info,a.checked.proof,.lam binder word b.checked.proof info]) := by
  obtain ⟨target,nextTyped,nextProof⟩ := bindValue_next_typed inputs closed stable wordDeclared consDeclared right
  have typed := bindValue_typed inputs (⟨left.sourceCore,left.value.mono embeds,left.target.mono embeds,left.proof⟩ : Read.ReadCasts inputs a proofCasts) (target.mono embeds)
    (.exact (nextTyped.mono embeds)) nextProof beta registered
  exact finish_cast_complete
    (Step.expected_represents (evalCmd_represents inputs
      (app_represents (.constant rfl) (.cons a.represented.property (.cons b.represented.property .nil))))
      (.app (.app valueBind_represents left.sourceCore.property) (.lam (.constant rfl) right.sourceCore.property)))
    (app_represents (.constant rfl) (.cons a.represented.property (.cons b.represented.property
      (.cons inputs.i.property (.cons inputs.x.property (.cons inputs.y.property
        (.cons inputs.s.property (.cons inputs.ls.property (.cons left.sourceCore.property
          (.cons (.lam (.constant rfl) right.sourceCore.property)
            (.cons a.checked.proofCore.property (.cons (.lam (.constant rfl) b.checked.proofCore.property) .nil))))))))))))
    typed ((known_casts a.checked left.proof).orElse (known_casts b.checked right.proof))
    coverage exposure _

def bindValueConstructor : VExpr := .forallE exprType (.forallE cmdType cmdType)

theorem complete_code (inputs : InputsTyped env ctx p)
    (closed : ClosedConstantTypes env) (stable : ClosedCasts casts)
    (embeds : ∀ scope a b, casts scope a b → proofCasts scope a b)
    (wordDeclared : env.constants ``HybridWord.Word = some ⟨0,.sort (.succ .zero)⟩)
    (consDeclared : env.constants ``List.cons = some consSignature)
    {a : Piece env ctx p first readExpected} (left : Read.ReadCasts inputs a casts proofCasts)
    {b : Piece env (wordType::ctx) {p.lift with locals := .bvar 0 :: p.lift.locals} nextBody Mode.step.expected}
    (right : StepCasts (inputs.nextWord closed wordDeclared consDeclared) b casts proofCasts)
    (beta : proofCasts ctx (bindValueNextActual inputs b.represented.val right.sourceCore.val)
      (bindValueContinuationType inputs b.represented.val (.lam wordType right.sourceCore.val)))
    (registered : env.constants ``WordLoopFacts.bindValue = some ⟨0,bindValueSignature⟩)
    (constructor : env.constants ``HybridWord.Cmd.letValue = some ⟨0,bindValueConstructor⟩)
    (coverage : Conversion.Covers conv 0 proofCasts) (exposure : Exposure env)
    (bindLibrary : BindSignatures env)
    (steps : Step.Signatures env)
    (binder : Lean.Name) (info : Lean.BinderInfo)
    (firstParsed : readStep env conv exposure ctx p (ScalarEnvironment.parse env conv exposure ctx p) first = some a)
    (nextParsed : visit env conv exposure nextBody (wordType::ctx) {p.lift with locals := .bvar 0 :: p.lift.locals}
      .step .identity (fun _ => none) = some b) :
    ∃ piece, visit env conv exposure (bindValueSource first (.lam binder word nextBody info)) ctx p
      .step .identity (fun _ => none) = some piece ∧
      Nonempty (StepCasts inputs piece casts proofCasts) ∧
      piece.code = app ``HybridWord.Cmd.letValue [a.code,b.code] := by
  obtain ⟨artifact,checked,typed,_,_⟩ := bindValue_finish inputs closed stable embeds wordDeclared consDeclared
    left right beta registered coverage exposure binder info
  let code := ClosedTerm.app ``HybridWord.Cmd.letValue [a.closedTerm,b.closedTerm]
  let piece : Piece env ctx p (bindValueSource first (.lam binder word nextBody info)) Mode.step.expected :=
    ⟨code.val,artifact,code.closed,code.represented⟩
  obtain ⟨_,nextTyped,_⟩ := bindValue_next_typed inputs closed stable wordDeclared consDeclared right
  have applied := CastTyping.checkedApplication ((bindLibrary.header_typed (domain := wordType) (result := Step.stepState)
    (.constant wordDeclared (by simp) rfl) steps.step_typed (by trivial) (by trivial)).withCasts casts) left.value
  simp only [optionType,stateType,Step.stepState,VExpr.inst] at applied
  have sourceTyped := CastTyping.application applied nextTyped
  refine ⟨piece,?_,⟨⟨⟨_,.app (.app valueBind_represents left.sourceCore.property)
    (.lam (.constant rfl) right.sourceCore.property)⟩,sourceTyped,?_,typed⟩⟩,rfl⟩
  · have ss : sameTerm word state = false := rfl
    have sc : compatible env conv ctx word word = true :=
      compatible_same (Represents.constant rfl) (Represents.constant rfl) env conv ctx
    have st : translate word = some ⟨wordType,Represents.constant rfl⟩ := rfl
    have su : sameTerm word (.const ``PUnit [.succ .zero]) = false := rfl
    have modeValue : (Mode.step == Mode.value) = false := rfl
    have modeStep : (Mode.step == Mode.step) = true := rfl
    have args : (bindValueSource first (.lam binder word nextBody info)).getAppArgs =
      #[.const ``Option [.zero],Lean.mkAppN (.const ``Monad.toBind [.zero,.zero])
        #[.const ``Option [.zero],.const ``instMonadOption [.zero]],word,stepType,first,.lam binder word nextBody info] := rfl
    have empty : underFunctions (fun _ => (none : Option (Continuation env))) = (fun _ => none) := by
      funext n; cases n <;> rfl
    rw [visit]
    simp [node,modeValue,modeStep,letParts,applicationHead,makeContinuation,continuationParts,lambdaChain,
      Substitution.apply,ScalarEnvironment.arguments,ScalarEnvironment.below,lambdaParts,under,
      empty,ss,sc,st,bindValueSource,bindHead,Lean.mkApp,Lean.mkApp2,Lean.mkAppB,
      Lean.Expr.getAppFn,Lean.Expr.constName?,bindHead,Lean.mkAppN,List.map_cons,List.map_nil]
    simp only [bindValueSource,bindHead,Lean.mkApp,Lean.mkApp2,Lean.mkAppB,bindHead,Lean.mkAppN] at args
    simp only [List.map_append,List.map_cons,List.map_nil,List.nil_append,List.cons_append,
      Function.comp_apply,List.length_cons,List.length_nil,Nat.reduceAdd,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.unattach_some,
      args,Array.getElem?_eq_getElem,Array.back?,su,ss,sc,st,
      Option.bind_some,Bool.false_eq_true,Bool.true_eq_false,ite_false,ite_true]
    simp [firstParsed,nextParsed,finishBody,Mode.expected,ClosedTerm.app,Piece.closedTerm,
      code,piece,bindValueSource,bindHead,Lean.mkApp2,Lean.mkAppB,Lean.mkApp,app] at checked ⊢
    refine ⟨first,rfl,a,firstParsed,?_⟩
    simp only [checked]
    rfl
  · obtain ⟨target,_,_⟩ := bindValue_next_typed inputs closed stable wordDeclared consDeclared right
    have fact : CastTyping env 0 casts ctx (.const ``HybridWord.Cmd.letValue []) bindValueConstructor :=
      .constant constructor (by simp) rfl
    have first := CastTyping.application fact left.target
    simp only [bindValueConstructor,cmdType,exprType,VExpr.inst] at first
    exact .application first target

def letValueFirstPremise : VExpr := equalValues (optionType wordType)
  (scalarValue (.bvar 6) (.bvar 5) (.bvar 4) (.bvar 3) (.bvar 2) (.bvar 8))
  (someValue wordType (.bvar 1))
def letValueResult : VExpr := Step.expected
  (bodyValue (.bvar 8) (.bvar 7) (.bvar 6)
    (applications (.const ``HybridWord.Cmd.letValue []) [.bvar 10,.bvar 9]) (.bvar 5) (.bvar 4))
  (.app (.bvar 2) (.bvar 3))
def letValueSignature : VExpr := .forallE exprType (.forallE cmdType
  (inputsType (.forallE wordType
    (.forallE (.forallE wordType (optionType Step.stepState))
      (.forallE letValueFirstPremise (.forallE bindValueNextPremise letValueResult))))))

def letValueSource (binder : Lean.Name) (value next : Lean.Expr) (nondep : Bool) : Lean.Expr :=
  .letE binder word value next nondep

theorem complete (inputs : InputsTyped env ctx p)
    (closed : ClosedConstantTypes env) (stable : ClosedCasts casts)
    (embeds : ∀ scope a b, casts scope a b → proofCasts scope a b)
    (wordDeclared : env.constants ``HybridWord.Word = some ⟨0,.sort (.succ .zero)⟩)
    (consDeclared : env.constants ``List.cons = some consSignature)
    {a : Piece env ctx p first readExpected} (left : Read.ReadCasts inputs a casts proofCasts)
    {b : Piece env (wordType::ctx) {p.lift with locals := .bvar 0 :: p.lift.locals} nextBody Mode.step.expected}
    (right : StepCasts (inputs.nextWord closed wordDeclared consDeclared) b casts proofCasts)
    (beta : proofCasts ctx (bindValueNextActual inputs b.represented.val right.sourceCore.val)
      (bindValueContinuationType inputs b.represented.val (.lam wordType right.sourceCore.val)))
    (registered : env.constants ``WordLoopFacts.bindValue = some ⟨0,bindValueSignature⟩)
    (constructor : env.constants ``HybridWord.Cmd.letValue = some ⟨0,bindValueConstructor⟩)
    (coverage : Conversion.Covers conv 0 proofCasts) (exposure : Exposure env)
    (bindLibrary : BindSignatures env)
    (steps : Step.Signatures env)
    (binder : Lean.Name) (info : Lean.BinderInfo)
    (firstParsed : readStep env conv exposure ctx p (ScalarEnvironment.parse env conv exposure ctx p) first = some a)
    (nextParsed : visit env conv exposure nextBody (wordType::ctx) {p.lift with locals := .bvar 0 :: p.lift.locals}
      .step .identity (fun _ => none) = some b) :
    ∃ piece, visit env conv exposure (bindValueSource first (.lam binder word nextBody info)) ctx p
      .step .identity (fun _ => none) = some piece ∧
      Nonempty (StepCasts inputs piece casts proofCasts) := by
  obtain ⟨piece,success,typed,form⟩ := complete_code inputs closed stable embeds wordDeclared consDeclared left right beta registered constructor coverage exposure bindLibrary steps binder info firstParsed nextParsed
  exact ⟨piece,success,typed⟩

theorem letValue_typed (inputs : InputsTyped env ctx p)
    {a : Piece env ctx p first scalarExpected} (left : ScalarCasts inputs a casts)
    (rightTarget : CastTyping env 0 casts ctx b cmdType)
    (nextTyped : CheckedTyping env 0 casts ctx next (.forallE wordType (optionType Step.stepState)))
    (nextProof : CastTyping env 0 casts ctx proofNext actual)
    (beta : casts ctx actual (bindValueContinuationType inputs b next))
    (registered : env.constants ``WordLoopFacts.letValue = some ⟨0,letValueSignature⟩) :
    CastTyping env 0 casts ctx
      (applications (.const ``WordLoopFacts.letValue [])
        ([a.represented.val,b] ++ inputs.args ++
          [left.sourceCore.val,next,a.checked.proofCore.val,proofNext]))
      (Step.expected
        (bodyValue inputs.i.val inputs.x.val inputs.y.val
          (applications (.const ``HybridWord.Cmd.letValue []) [a.represented.val,b]) inputs.s.val inputs.ls.val)
        (.app next left.sourceCore.val)) := by
  have fact : CastTyping env 0 casts ctx (.const ``WordLoopFacts.letValue []) letValueSignature :=
    .constant (levels := []) registered (by simp) rfl
  have a1 := CastTyping.application fact left.target
  simp only [Step.expected,Step.lifted,Step.stepState,letValueSignature,inputsType,exprType,cmdType,wordType,stateType,wordsType,optionType,VExpr.inst] at a1
  have a2 := CastTyping.application a1 rightTarget
  simp only [Step.expected,Step.lifted,Step.stepState,VExpr.inst] at a2
  have a3 := inputs.apply_casts a2
  simp only [Step.expected,Step.lifted,Step.stepState,InputsTyped.instantiate,letValueFirstPremise,bindValueNextPremise,letValueResult,
    bodyValue,scalarValue,someValue,equalValues,optionType,stateType,wordType,applications,Nat.reduceAdd,
    ← VExpr.lift_instN_lo,VExpr.inst_lift,VExpr.inst,
    VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] at a3
  have a4 := CastTyping.checkedApplication a3 left.value
  simp only [Step.expected,Step.lifted,Step.stepState,Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst_lift,VExpr.inst,
    VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] at a4
  have a5 := CastTyping.checkedApplication a4 nextTyped
  simp only [Step.expected,Step.lifted,Step.stepState,Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst_lift,VExpr.inst,
    VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] at a5
  have a6 := CastTyping.application a5 left.equality
  simp only [Step.expected,Step.lifted,Step.stepState,Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst_lift,VExpr.inst,
    VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] at a6
  have cast := beta
  simp only [Step.expected,Step.lifted,Step.stepState,bindValueContinuationType,bodyValue,scalarValue,someValue,equalValues,applications,optionType,wordType,stateType] at cast
  simpa only [InputsTyped.args,applications,List.cons_append,List.nil_append,bodyValue,
    equalValues,optionType,wordType,stateType,Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst_lift,
    VExpr.inst,VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] using
    CastTyping.convertedApplication a6 nextProof cast

theorem letValue_finish (inputs : InputsTyped env ctx p)
    (closed : ClosedConstantTypes env) (stable : ClosedCasts casts)
    (embeds : ∀ scope a b, casts scope a b → proofCasts scope a b)
    (wordDeclared : env.constants ``HybridWord.Word = some ⟨0,.sort (.succ .zero)⟩)
    (consDeclared : env.constants ``List.cons = some consSignature)
    {a : Piece env ctx p first scalarExpected} (left : ScalarCasts inputs a casts proofCasts)
    {b : Piece env (wordType::ctx) {p.lift with locals := .bvar 0 :: p.lift.locals} nextBody Mode.step.expected}
    (right : StepCasts (inputs.nextWord closed wordDeclared consDeclared) b casts proofCasts)
    (beta : proofCasts ctx (bindValueNextActual inputs b.represented.val right.sourceCore.val)
      (bindValueContinuationType inputs b.represented.val (.lam wordType right.sourceCore.val)))
    (registered : env.constants ``WordLoopFacts.letValue = some ⟨0,letValueSignature⟩)
    (coverage : Conversion.Covers conv 0 proofCasts) (exposure : Exposure env)
    (binder : Lean.Name) (nondep : Bool) :
    ∃ result, finish env conv exposure ctx
      (Mode.step.expected p (app ``HybridWord.Cmd.letValue [a.code,b.code])
        (letValueSource binder first nextBody nondep))
      (app ``HybridWord.Cmd.letValue [a.code,b.code])
      (app ``WordLoopFacts.letValue ([a.code,b.code] ++ p.args ++
        [first,.lam binder word nextBody .default,a.checked.proof,.lam binder word b.checked.proof .default]))
      (a.checked.known.orElse b.checked.known) = some result ∧
      CastTyping env 0 proofCasts ctx result.proofCore.val result.core.val ∧
      result.code = app ``HybridWord.Cmd.letValue [a.code,b.code] ∧
      result.proof = app ``WordLoopFacts.letValue ([a.code,b.code] ++ p.args ++
        [first,.lam binder word nextBody .default,a.checked.proof,.lam binder word b.checked.proof .default]) := by
  obtain ⟨target,nextTyped,nextProof⟩ := bindValue_next_typed inputs closed stable wordDeclared consDeclared right
  have typed := letValue_typed inputs (left.inProofCasts embeds) (target.mono embeds)
    (.exact (nextTyped.mono embeds)) nextProof beta registered
  exact finish_cast_complete
    (Step.expected_represents (evalCmd_represents inputs
      (app_represents (.constant rfl) (.cons a.represented.property (.cons b.represented.property .nil))))
      (.letE (.constant rfl) left.sourceCore.property right.sourceCore.property))
    (app_represents (.constant rfl) (.cons a.represented.property (.cons b.represented.property
      (.cons inputs.i.property (.cons inputs.x.property (.cons inputs.y.property
        (.cons inputs.s.property (.cons inputs.ls.property (.cons left.sourceCore.property
          (.cons (.lam (.constant rfl) right.sourceCore.property)
            (.cons a.checked.proofCore.property (.cons (.lam (.constant rfl) b.checked.proofCore.property) .nil))))))))))))
    typed ((known_casts a.checked (left.proof)).orElse (known_casts b.checked right.proof))
    coverage exposure _

theorem letValue_step_split_complete (inputs : InputsTyped env ctx p)
    (closed : ClosedConstantTypes env) (stable : ClosedCasts casts)
    (embeds : ∀ scope a b, casts scope a b → proofCasts scope a b)
    (wordDeclared : env.constants ``HybridWord.Word = some ⟨0,.sort (.succ .zero)⟩)
    (consDeclared : env.constants ``List.cons = some consSignature)
    {a : Piece env ctx p first scalarExpected} (left : ScalarCasts inputs a casts proofCasts)
    {b : Piece env (wordType::ctx) {p.lift with locals := .bvar 0 :: p.lift.locals} nextBody Mode.step.expected}
    (right : StepCasts (inputs.nextWord closed wordDeclared consDeclared) b casts proofCasts)
    (beta : proofCasts ctx (bindValueNextActual inputs b.represented.val right.sourceCore.val)
      (bindValueContinuationType inputs b.represented.val (.lam wordType right.sourceCore.val)))
    (registered : env.constants ``WordLoopFacts.letValue = some ⟨0,letValueSignature⟩)
    (constructor : env.constants ``HybridWord.Cmd.letValue = some ⟨0,bindValueConstructor⟩)
    (coverage : Conversion.Covers conv 0 proofCasts) (exposure : Exposure env)
    (binder : Lean.Name) (nondep : Bool)
    (firstParsed : ScalarEnvironment.parse env conv exposure ctx p first = some a)
    (nextParsed : visit env conv exposure nextBody (wordType::ctx)
      {p.lift with locals := .bvar 0 :: p.lift.locals} .step .identity (fun _ => none) = some b) :
    ∃ piece, visit env conv exposure (letValueSource binder first nextBody nondep) ctx p
      .step .identity (fun _ => none) = some piece ∧
      Nonempty (StepCasts inputs piece casts proofCasts) := by
  obtain ⟨artifact,checked,typed,_,_⟩ := letValue_finish inputs closed stable embeds wordDeclared consDeclared
    left right beta registered coverage exposure binder nondep
  let code := ClosedTerm.app ``HybridWord.Cmd.letValue [a.closedTerm,b.closedTerm]
  let piece : Piece env ctx p (letValueSource binder first nextBody nondep) Mode.step.expected :=
    ⟨code.val,artifact,code.closed,code.represented⟩
  obtain ⟨_,nextTyped,_⟩ := bindValue_next_typed inputs closed stable wordDeclared consDeclared right
  have sourceTyped := CastTyping.checkedApplication nextTyped left.value
  simp only [Step.expected,Step.lifted,Step.stepState,optionType,stateType,VExpr.inst] at sourceTyped
  refine ⟨piece,?_,⟨⟨⟨_,.letE (.constant rfl) left.sourceCore.property
    right.sourceCore.property⟩,sourceTyped,?_,typed⟩⟩⟩
  · have wordSame := sameTerm_complete (a := word) (b := word)
      (Represents.constant rfl) (Represents.constant rfl)
    have wordNotState : sameTerm word state = false := rfl
    have wordCompatible : compatible env conv ctx word word = true := by
      simp only [Step.expected,Step.lifted,Step.stepState,compatible,wordSame]; rfl
    have translated : translate word = some ⟨wordType,Represents.constant rfl⟩ := rfl
    have empty : underFunctions (fun _ => (none : Option (Continuation env))) = (fun _ => none) := by
      funext n; cases n <;> rfl
    have modeValue : (Mode.step == Mode.value) = false := rfl
    have modeStep : (Mode.step == Mode.step) = true := rfl
    rw [visit]
    simp [node,letParts,letValueSource,modeValue,modeStep,Substitution.apply,under,empty,
      wordNotState,wordCompatible,translated,firstParsed,nextParsed,
      finishBody,Mode.expected,ClosedTerm.app,Piece.closedTerm,code,piece,app,letValueSource] at checked ⊢
    exact checked
  · obtain ⟨target,_,_⟩ := bindValue_next_typed inputs closed stable wordDeclared consDeclared right
    have fact : CastTyping env 0 casts ctx (.const ``HybridWord.Cmd.letValue []) bindValueConstructor :=
      .constant constructor (by simp) rfl
    have first := CastTyping.application fact left.target
    simp only [Step.expected,Step.lifted,Step.stepState,bindValueConstructor,cmdType,VExpr.inst] at first
    exact .application first target

theorem letValue_step_complete (inputs : InputsTyped env ctx p)
    (closed : ClosedConstantTypes env) (stable : ClosedCasts casts)
    (embeds : ∀ scope a b, casts scope a b → proofCasts scope a b)
    (wordDeclared : env.constants ``HybridWord.Word = some ⟨0,.sort (.succ .zero)⟩)
    (consDeclared : env.constants ``List.cons = some consSignature)
    {a : Piece env ctx p first scalarExpected} (left : ScalarCasts inputs a casts)
    {b : Piece env (wordType::ctx) {p.lift with locals := .bvar 0 :: p.lift.locals} nextBody Mode.step.expected}
    (right : StepCasts (inputs.nextWord closed wordDeclared consDeclared) b casts proofCasts)
    (beta : proofCasts ctx (bindValueNextActual inputs b.represented.val right.sourceCore.val)
      (bindValueContinuationType inputs b.represented.val (.lam wordType right.sourceCore.val)))
    (registered : env.constants ``WordLoopFacts.letValue = some ⟨0,letValueSignature⟩)
    (constructor : env.constants ``HybridWord.Cmd.letValue = some ⟨0,bindValueConstructor⟩)
    (coverage : Conversion.Covers conv 0 proofCasts) (exposure : Exposure env)
    (binder : Lean.Name) (nondep : Bool)
    (firstParsed : ScalarEnvironment.parse env conv exposure ctx p first = some a)
    (nextParsed : visit env conv exposure nextBody (wordType::ctx)
      {p.lift with locals := .bvar 0 :: p.lift.locals} .step .identity (fun _ => none) = some b) :
    ∃ piece, visit env conv exposure (letValueSource binder first nextBody nondep) ctx p
      .step .identity (fun _ => none) = some piece ∧
      Nonempty (StepCasts inputs piece casts proofCasts) := by
  exact letValue_step_split_complete inputs closed stable embeds wordDeclared consDeclared
    (left.mapProofs embeds) right beta registered constructor coverage exposure binder nondep firstParsed nextParsed

end IRComparison.WordFrontend.StructuralReadBind
