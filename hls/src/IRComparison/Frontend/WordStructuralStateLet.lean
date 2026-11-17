import IRComparison.Frontend.WordStructuralReadBind
import IRComparison.Frontend.WordStateLetCompleteness

/-! Structural traversal of pure State updates. The value is processed once;
its command certificate is composed with the latest-State continuation. -/
namespace IRComparison.WordFrontend.StructuralStateLet
open Lean4Lean LeanTyped LeanTypeInference Certificate StructuralBody StructuralLoop
variable {casts proofCasts : TypeCasts} [Arithmetic.Includes casts] [Arithmetic.Includes proofCasts]
open Certificate.StateLet
set_option maxHeartbeats 1200000

theorem mapped_complete_code (inputs : InputsTyped env ctx p)
    (closed : ClosedConstantTypes env) (stable : ClosedCasts casts)
    (embeds : ∀ scope a b, casts scope a b → proofCasts scope a b)
    (stateDeclared : env.constants ``HybridWord.State = some ⟨0,.sort (.succ .zero)⟩)
    {a : Piece env ctx p (σ.apply first) Mode.value.expected} (left : ValueCasts inputs a casts proofCasts)
    (returns : Return.Signatures env)
    {b : Piece env (stateType::ctx) {p.lift with s := .bvar 0} ((under σ).apply nextBody) bodyExpected}
    (right : BodyCasts (inputs.nextState closed) b casts proofCasts)
    (beta : proofCasts ctx (sequenceNextActual inputs b.represented.val right.sourceCore.val)
      (sequenceContinuationType inputs b.represented.val (.lam stateType right.sourceCore.val)))
    (registered : env.constants ``WordFrontendFacts.letState = some ⟨0,signature⟩)
    (constructor : env.constants ``HybridWord.Cmd.seq = some ⟨0,sequenceConstructor⟩)
    (coverage : Conversion.Covers conv 0 proofCasts) (exposure : Exposure env)
    (binder : Lean.Name) (nondep : Bool)
    (notAlias : sameTerm (σ.apply first) p.s = false)
    (firstParsed : visit env conv exposure first ctx p .value σ fs = some a)
    (nextParsed : visit env conv exposure nextBody (stateType::ctx) {p.lift with s := .bvar 0} .body (under σ) (underFunctions fs) = some b) :
    ∃ piece, visit env conv exposure (source binder first nextBody nondep) ctx p .body σ fs = some piece ∧
      Nonempty (BodyCasts inputs piece casts proofCasts) ∧
      piece.code = app ``HybridWord.Cmd.seq [a.code,b.code] := by
  have assembled := StateLet.finish_complete inputs closed stable embeds stateDeclared
    (left.asBody returns) left.sourceCore.property left.value right beta registered coverage exposure binder nondep
  have sourceSame : σ.apply (source binder first nextBody nondep) =
      source binder (σ.apply first) ((under σ).apply nextBody) nondep := by cases σ <;> rfl
  rw [← sourceSame] at assembled
  obtain ⟨artifact,checked,typed,_,_⟩ := assembled
  let code := ClosedTerm.app ``HybridWord.Cmd.seq [a.closedTerm,b.closedTerm]
  let piece : Piece env ctx p (σ.apply (source binder first nextBody nondep)) bodyExpected :=
    ⟨code.val,artifact,code.closed,code.represented⟩
  obtain ⟨_,nextTyped,_⟩ := sequence_next_typed inputs closed stable stateDeclared right
  have sourceTyped := CastTyping.application nextTyped left.value
  simp only [optionType,stateType,VExpr.inst] at sourceTyped
  have represented : Represents (σ.apply (source binder first nextBody nondep))
      (.app (.lam stateType right.sourceCore.val) left.sourceCore.val) := by
    rw [sourceSame]; exact .letE (.constant rfl) left.sourceCore.property right.sourceCore.property
  refine ⟨piece,?_,⟨⟨⟨_,represented⟩,sourceTyped,?_,typed⟩⟩,rfl⟩
  · have stateSame := sameTerm_complete (a := state) (b := state)
      (Represents.constant rfl) (Represents.constant rfl)
    have stateCompatible : compatible env conv ctx state state = true := by
      simp only [compatible,stateSame]; rfl
    have translated : translate state = some ⟨stateType,Represents.constant rfl⟩ := rfl
    have modeValue : (Mode.body == Mode.value) = false := rfl
    have modeStep : (Mode.body == Mode.step) = false := rfl
    cases σ
    all_goals
      rw [visit]
      simp only [node,modeValue,modeStep,source,letParts,Substitution.apply,LeanBindings.substitute,
        under,state,WordFrontend.state] at notAlias stateSame stateCompatible translated firstParsed nextParsed checked ⊢
      simp only [stateSame,notAlias,stateCompatible,translated,Bool.false_eq_true,Bool.true_eq_false,
        Bool.not_true,Bool.not_false,Bool.false_and,Bool.and_false,Bool.and_true,Bool.true_and,ite_true,ite_false,bind,Option.bind,pure,Option.pure_def]
      rw [firstParsed]
      dsimp only
      rw [nextParsed]
      dsimp only
      simp only [ValueCasts.asBody,finishBody,Mode.expected,ClosedTerm.app,Piece.closedTerm,code,piece,app,
        source,Substitution.apply,LeanBindings.substitute,under,state,WordFrontend.state,
        List.map_cons,List.map_nil,List.foldl_cons,List.foldl_nil,Inputs.args,List.cons_append,List.nil_append]
        at checked ⊢
      rw [checked]
      all_goals rfl
  · obtain ⟨target,_,_⟩ := sequence_next_typed inputs closed stable stateDeclared right
    have fact : CastTyping env 0 casts ctx (.const ``HybridWord.Cmd.seq []) sequenceConstructor :=
      .constant constructor (by simp) rfl
    have first := CastTyping.application fact left.target
    simp only [sequenceConstructor,cmdType,VExpr.inst] at first
    exact .application first target


theorem complete_code (inputs : InputsTyped env ctx p)
    (closed : ClosedConstantTypes env) (stable : ClosedCasts casts)
    (embeds : ∀ scope a b, casts scope a b → proofCasts scope a b)
    (stateDeclared : env.constants ``HybridWord.State = some ⟨0,.sort (.succ .zero)⟩)
    {a : Piece env ctx p first Mode.value.expected} (left : ValueCasts inputs a casts proofCasts)
    (returns : Return.Signatures env)
    {b : Piece env (stateType::ctx) {p.lift with s := .bvar 0} nextBody bodyExpected}
    (right : BodyCasts (inputs.nextState closed) b casts proofCasts)
    (beta : proofCasts ctx (sequenceNextActual inputs b.represented.val right.sourceCore.val)
      (sequenceContinuationType inputs b.represented.val (.lam stateType right.sourceCore.val)))
    (registered : env.constants ``WordFrontendFacts.letState = some ⟨0,signature⟩)
    (constructor : env.constants ``HybridWord.Cmd.seq = some ⟨0,sequenceConstructor⟩)
    (coverage : Conversion.Covers conv 0 proofCasts) (exposure : Exposure env)
    (binder : Lean.Name) (nondep : Bool)
    (notAlias : sameTerm first p.s = false)
    (firstParsed : visit env conv exposure first ctx p .value .identity (fun _ => none) = some a)
    (nextParsed : StructuralBody.bodyRetained env conv exposure (stateType::ctx) {p.lift with s := .bvar 0} nextBody = some b) :
    ∃ piece, StructuralBody.bodyRetained env conv exposure ctx p (source binder first nextBody nondep) = some piece ∧
      Nonempty (BodyCasts inputs piece casts proofCasts) ∧
      piece.code = app ``HybridWord.Cmd.seq [a.code,b.code] := by
  have empty : underFunctions (fun _ => (none : Option (Continuation env))) = (fun _ => none) := by
    funext n; cases n <;> rfl
  exact mapped_complete_code (σ := .identity) (fs := fun _ => none) inputs closed stable embeds stateDeclared left returns right beta registered
    constructor coverage exposure binder nondep notAlias firstParsed (by simpa only [under,empty] using nextParsed)

theorem complete (inputs : InputsTyped env ctx p)
    (closed : ClosedConstantTypes env) (stable : ClosedCasts casts)
    (embeds : ∀ scope a b, casts scope a b → proofCasts scope a b)
    (stateDeclared : env.constants ``HybridWord.State = some ⟨0,.sort (.succ .zero)⟩)
    {a : Piece env ctx p first Mode.value.expected} (left : ValueCasts inputs a casts proofCasts)
    (returns : Return.Signatures env)
    {b : Piece env (stateType::ctx) {p.lift with s := .bvar 0} nextBody bodyExpected}
    (right : BodyCasts (inputs.nextState closed) b casts proofCasts)
    (beta : proofCasts ctx (sequenceNextActual inputs b.represented.val right.sourceCore.val)
      (sequenceContinuationType inputs b.represented.val (.lam stateType right.sourceCore.val)))
    (registered : env.constants ``WordFrontendFacts.letState = some ⟨0,signature⟩)
    (constructor : env.constants ``HybridWord.Cmd.seq = some ⟨0,sequenceConstructor⟩)
    (coverage : Conversion.Covers conv 0 proofCasts) (exposure : Exposure env)
    (binder : Lean.Name) (nondep : Bool)
    (notAlias : sameTerm first p.s = false)
    (firstParsed : visit env conv exposure first ctx p .value .identity (fun _ => none) = some a)
    (nextParsed : StructuralBody.bodyRetained env conv exposure (stateType::ctx) {p.lift with s := .bvar 0} nextBody = some b) :
    ∃ piece, StructuralBody.bodyRetained env conv exposure ctx p (source binder first nextBody nondep) = some piece ∧
      Nonempty (BodyCasts inputs piece casts proofCasts) := by
  obtain ⟨piece,success,typed,_⟩ := complete_code inputs closed stable embeds stateDeclared left returns right beta registered constructor coverage exposure binder nondep notAlias firstParsed nextParsed
  exact ⟨piece,success,typed⟩

namespace Loop
def firstPremise : VExpr := equalValues (optionType stateType)
  (bodyValue (.bvar 6) (.bvar 5) (.bvar 4) (.bvar 8) (.bvar 3) (.bvar 2))
  (someValue stateType (.bvar 1))
def resultType : VExpr := Step.expected
  (bodyValue (.bvar 8) (.bvar 7) (.bvar 6)
    (applications (.const ``HybridWord.Cmd.seq []) [.bvar 10,.bvar 9]) (.bvar 5) (.bvar 4))
  (.app (.bvar 2) (.bvar 3))
def signature : VExpr := .forallE cmdType (.forallE cmdType
  (inputsType (.forallE stateType
    (.forallE (.forallE stateType (optionType Step.stepState))
      (.forallE firstPremise (.forallE StructuralStep.sequenceNextPremise resultType))))))

def source (binder : Lean.Name) (value next : Lean.Expr) (nondep : Bool) : Lean.Expr :=
  .letE binder state value next nondep

theorem fact_typed (inputs : InputsTyped env ctx p)
    {a : Piece env ctx p (someExpr state first) bodyExpected} (left : BodyCasts inputs a casts)
    (valueRep : Represents first valueCore) (valueTyped : CastTyping env 0 casts ctx valueCore stateType)
    (rightTarget : CastTyping env 0 casts ctx b cmdType)
    (nextTyped : CastTyping env 0 casts ctx next (.forallE stateType (optionType Step.stepState)))
    (nextProof : CastTyping env 0 casts ctx proofNext actual)
    (beta : casts ctx actual (StructuralStep.sequenceContinuationType inputs b next))
    (registered : env.constants ``WordLoopFacts.letState = some ⟨0,signature⟩) :
    CastTyping env 0 casts ctx
      (applications (.const ``WordLoopFacts.letState [])
        ([a.represented.val,b] ++ inputs.args ++
          [valueCore,next,a.checked.proofCore.val,proofNext]))
      (Step.expected
        (bodyValue inputs.i.val inputs.x.val inputs.y.val
          (applications (.const ``HybridWord.Cmd.seq []) [a.represented.val,b]) inputs.s.val inputs.ls.val)
        (.app next valueCore)) := by
  have fact : CastTyping env 0 casts ctx (.const ``WordLoopFacts.letState []) signature :=
    .constant (levels := []) registered (by simp) rfl
  have a1 := CastTyping.application fact left.target
  simp only [Step.expected,Step.lifted,Step.stepState,signature,inputsType,exprType,cmdType,wordType,stateType,wordsType,optionType,VExpr.inst] at a1
  have a2 := CastTyping.application a1 rightTarget
  simp only [Step.expected,Step.lifted,Step.stepState,VExpr.inst] at a2
  have a3 := inputs.apply_casts a2
  simp only [Step.expected,Step.lifted,Step.stepState,InputsTyped.instantiate,firstPremise,StructuralStep.sequenceNextPremise,resultType,
    bodyValue,scalarValue,someValue,equalValues,optionType,stateType,wordType,applications,Nat.reduceAdd,
    ← VExpr.lift_instN_lo,VExpr.inst_lift,VExpr.inst,
    VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] at a3
  have a4 := CastTyping.application a3 valueTyped
  simp only [Step.expected,Step.lifted,Step.stepState,Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst_lift,VExpr.inst,
    VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] at a4
  have a5 := CastTyping.application a4 nextTyped
  simp only [Step.expected,Step.lifted,Step.stepState,Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst_lift,VExpr.inst,
    VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] at a5
  have valueSource : left.sourceCore.val = someValue stateType valueCore :=
    left.sourceCore.property.unique (.app (.app (.constant rfl) (.constant rfl)) valueRep)
  have firstEquality := left.equality
  rw [valueSource] at firstEquality
  have a6 := CastTyping.application a5 firstEquality
  simp only [Step.expected,Step.lifted,Step.stepState,Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst_lift,VExpr.inst,
    VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] at a6
  have cast := beta
  simp only [Step.expected,Step.lifted,Step.stepState,StructuralStep.sequenceContinuationType,bodyValue,scalarValue,someValue,equalValues,applications,optionType,wordType,stateType] at cast
  simpa only [InputsTyped.args,applications,List.cons_append,List.nil_append,bodyValue,
    equalValues,optionType,wordType,stateType,Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst_lift,
    VExpr.inst,VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] using
    CastTyping.convertedApplication a6 nextProof cast

theorem finish_complete (inputs : InputsTyped env ctx p)
    (closed : ClosedConstantTypes env) (stable : ClosedCasts casts)
    (embeds : ∀ scope a b, casts scope a b → proofCasts scope a b)
    (stateDeclared : env.constants ``HybridWord.State = some ⟨0,.sort (.succ .zero)⟩)
    {a : Piece env ctx p (someExpr state first) bodyExpected} (left : BodyCasts inputs a casts proofCasts)
    (valueRep : Represents first valueCore) (valueTyped : CastTyping env 0 casts ctx valueCore stateType)
    {b : Piece env (stateType::ctx) {p.lift with s := .bvar 0} nextBody Mode.step.expected}
    (right : StepCasts (inputs.nextState closed) b casts proofCasts)
    (beta : proofCasts ctx (StructuralStep.sequenceNextActual inputs b.represented.val right.sourceCore.val)
      (StructuralStep.sequenceContinuationType inputs b.represented.val (.lam stateType right.sourceCore.val)))
    (registered : env.constants ``WordLoopFacts.letState = some ⟨0,signature⟩)
    (coverage : Conversion.Covers conv 0 proofCasts) (exposure : Exposure env)
    (binder : Lean.Name) (nondep : Bool) :
    ∃ result, finish env conv exposure ctx
      (Mode.step.expected p (app ``HybridWord.Cmd.seq [a.code,b.code])
        (source binder first nextBody nondep))
      (app ``HybridWord.Cmd.seq [a.code,b.code])
      (app ``WordLoopFacts.letState ([a.code,b.code] ++ p.args ++
        [first,.lam binder state nextBody .default,a.checked.proof,.lam binder state b.checked.proof .default]))
      (a.checked.known.orElse b.checked.known) = some result ∧
      CastTyping env 0 proofCasts ctx result.proofCore.val result.core.val ∧
      result.code = app ``HybridWord.Cmd.seq [a.code,b.code] ∧
      result.proof = app ``WordLoopFacts.letState ([a.code,b.code] ++ p.args ++
        [first,.lam binder state nextBody .default,a.checked.proof,.lam binder state b.checked.proof .default]) := by
  obtain ⟨target,nextTyped,nextProof⟩ := StructuralStep.sequence_next_typed inputs closed stable stateDeclared right
  have typed := fact_typed inputs (left.inProofCasts embeds) valueRep (valueTyped.mono embeds) (target.mono embeds)
    (nextTyped.mono embeds) nextProof beta registered
  exact finish_cast_complete
    (Step.expected_represents (evalCmd_represents inputs
      (app_represents (.constant rfl) (.cons a.represented.property (.cons b.represented.property .nil))))
      (.letE (.constant rfl) valueRep right.sourceCore.property))
    (app_represents (.constant rfl) (.cons a.represented.property (.cons b.represented.property
      (.cons inputs.i.property (.cons inputs.x.property (.cons inputs.y.property
        (.cons inputs.s.property (.cons inputs.ls.property (.cons valueRep
          (.cons (.lam (.constant rfl) right.sourceCore.property)
            (.cons a.checked.proofCore.property (.cons (.lam (.constant rfl) b.checked.proofCore.property) .nil))))))))))))
    typed ((known_casts a.checked left.proof).orElse (known_casts b.checked right.proof))
    coverage exposure _

theorem mapped_complete_code (inputs : InputsTyped env ctx p)
    (closed : ClosedConstantTypes env) (stable : ClosedCasts casts)
    (embeds : ∀ scope a b, casts scope a b → proofCasts scope a b)
    (stateDeclared : env.constants ``HybridWord.State = some ⟨0,.sort (.succ .zero)⟩)
    {a : Piece env ctx p (σ.apply first) Mode.value.expected} (left : ValueCasts inputs a casts proofCasts)
    (returns : Return.Signatures env)
    {b : Piece env (stateType::ctx) {p.lift with s := .bvar 0} ((under σ).apply nextBody) Mode.step.expected}
    (right : StepCasts (inputs.nextState closed) b casts proofCasts)
    (beta : proofCasts ctx (StructuralStep.sequenceNextActual inputs b.represented.val right.sourceCore.val)
      (StructuralStep.sequenceContinuationType inputs b.represented.val (.lam stateType right.sourceCore.val)))
    (registered : env.constants ``WordLoopFacts.letState = some ⟨0,signature⟩)
    (constructor : env.constants ``HybridWord.Cmd.seq = some ⟨0,sequenceConstructor⟩)
    (coverage : Conversion.Covers conv 0 proofCasts) (exposure : Exposure env)
    (binder : Lean.Name) (nondep : Bool)
    (notAlias : sameTerm (σ.apply first) p.s = false)
    (firstParsed : visit env conv exposure first ctx p .value σ fs = some a)
    (nextParsed : visit env conv exposure nextBody (stateType::ctx) {p.lift with s := .bvar 0} .step (under σ) (underFunctions fs) = some b) :
    ∃ piece, visit env conv exposure (source binder first nextBody nondep) ctx p .step σ fs = some piece ∧
      Nonempty (StepCasts inputs piece casts proofCasts) ∧
      piece.code = app ``HybridWord.Cmd.seq [a.code,b.code] := by
  have assembled := finish_complete inputs closed stable embeds stateDeclared
    (left.asBody returns) left.sourceCore.property left.value right beta registered coverage exposure binder nondep
  have sourceSame : σ.apply (source binder first nextBody nondep) =
      source binder (σ.apply first) ((under σ).apply nextBody) nondep := by cases σ <;> rfl
  rw [← sourceSame] at assembled
  obtain ⟨artifact,checked,typed,_,_⟩ := assembled
  let code := ClosedTerm.app ``HybridWord.Cmd.seq [a.closedTerm,b.closedTerm]
  let piece : Piece env ctx p (σ.apply (source binder first nextBody nondep)) Mode.step.expected :=
    ⟨code.val,artifact,code.closed,code.represented⟩
  obtain ⟨_,nextTyped,_⟩ := StructuralStep.sequence_next_typed inputs closed stable stateDeclared right
  have sourceTyped := CastTyping.application nextTyped left.value
  simp only [Step.expected,Step.lifted,Step.stepState,optionType,stateType,VExpr.inst] at sourceTyped
  have represented : Represents (σ.apply (source binder first nextBody nondep))
      (.app (.lam stateType right.sourceCore.val) left.sourceCore.val) := by
    rw [sourceSame]; exact .letE (.constant rfl) left.sourceCore.property right.sourceCore.property
  refine ⟨piece,?_,⟨⟨⟨_,represented⟩,sourceTyped,?_,typed⟩⟩,rfl⟩
  · have stateSame := sameTerm_complete (a := state) (b := state)
      (Represents.constant rfl) (Represents.constant rfl)
    have stateCompatible : compatible env conv ctx state state = true := by
      simp only [Step.expected,Step.lifted,Step.stepState,compatible,stateSame]; rfl
    have translated : translate state = some ⟨stateType,Represents.constant rfl⟩ := rfl
    have modeValue : (Mode.step == Mode.value) = false := rfl
    have modeStep : (Mode.step == Mode.step) = true := rfl
    cases σ
    all_goals
      rw [visit]
      simp only [node,modeValue,modeStep,source,letParts,Substitution.apply,LeanBindings.substitute,
        under,state,WordFrontend.state] at notAlias stateSame stateCompatible translated firstParsed nextParsed checked ⊢
      simp only [stateSame,notAlias,stateCompatible,translated,Bool.false_eq_true,Bool.true_eq_false,
        Bool.not_true,Bool.not_false,Bool.false_and,Bool.and_false,Bool.and_true,Bool.true_and,ite_true,ite_false,bind,Option.bind,pure,Option.pure_def]
      rw [firstParsed]
      dsimp only
      rw [nextParsed]
      dsimp only
      simp only [ValueCasts.asBody,finishBody,Mode.expected,ClosedTerm.app,Piece.closedTerm,code,piece,app,
        source,Substitution.apply,LeanBindings.substitute,under,state,WordFrontend.state,
        List.map_cons,List.map_nil,List.foldl_cons,List.foldl_nil,Inputs.args,List.cons_append,List.nil_append]
        at checked ⊢
      rw [checked]
      all_goals rfl
  · obtain ⟨target,_,_⟩ := StructuralStep.sequence_next_typed inputs closed stable stateDeclared right
    have fact : CastTyping env 0 casts ctx (.const ``HybridWord.Cmd.seq []) sequenceConstructor :=
      .constant constructor (by simp) rfl
    have first := CastTyping.application fact left.target
    simp only [Step.expected,Step.lifted,Step.stepState,sequenceConstructor,cmdType,VExpr.inst] at first
    exact .application first target

theorem complete_code (inputs : InputsTyped env ctx p)
    (closed : ClosedConstantTypes env) (stable : ClosedCasts casts)
    (embeds : ∀ scope a b, casts scope a b → proofCasts scope a b)
    (stateDeclared : env.constants ``HybridWord.State = some ⟨0,.sort (.succ .zero)⟩)
    {a : Piece env ctx p first Mode.value.expected} (left : ValueCasts inputs a casts proofCasts)
    (returns : Return.Signatures env)
    {b : Piece env (stateType::ctx) {p.lift with s := .bvar 0} nextBody Mode.step.expected}
    (right : StepCasts (inputs.nextState closed) b casts proofCasts)
    (beta : proofCasts ctx (StructuralStep.sequenceNextActual inputs b.represented.val right.sourceCore.val)
      (StructuralStep.sequenceContinuationType inputs b.represented.val (.lam stateType right.sourceCore.val)))
    (registered : env.constants ``WordLoopFacts.letState = some ⟨0,signature⟩)
    (constructor : env.constants ``HybridWord.Cmd.seq = some ⟨0,sequenceConstructor⟩)
    (coverage : Conversion.Covers conv 0 proofCasts) (exposure : Exposure env)
    (binder : Lean.Name) (nondep : Bool)
    (notAlias : sameTerm first p.s = false)
    (firstParsed : visit env conv exposure first ctx p .value .identity (fun _ => none) = some a)
    (nextParsed : visit env conv exposure nextBody (stateType::ctx) {p.lift with s := .bvar 0} .step .identity (fun _ => none) = some b) :
    ∃ piece, visit env conv exposure (source binder first nextBody nondep) ctx p .step .identity (fun _ => none) = some piece ∧
      Nonempty (StepCasts inputs piece casts proofCasts) ∧
      piece.code = app ``HybridWord.Cmd.seq [a.code,b.code] := by
  have empty : underFunctions (fun _ => (none : Option (Continuation env))) = (fun _ => none) := by
    funext n; cases n <;> rfl
  exact mapped_complete_code (σ := .identity) (fs := fun _ => none) inputs closed stable embeds stateDeclared left returns right beta registered
    constructor coverage exposure binder nondep notAlias firstParsed (by simpa only [under,empty] using nextParsed)

theorem complete (inputs : InputsTyped env ctx p)
    (closed : ClosedConstantTypes env) (stable : ClosedCasts casts)
    (embeds : ∀ scope a b, casts scope a b → proofCasts scope a b)
    (stateDeclared : env.constants ``HybridWord.State = some ⟨0,.sort (.succ .zero)⟩)
    {a : Piece env ctx p first Mode.value.expected} (left : ValueCasts inputs a casts proofCasts)
    (returns : Return.Signatures env)
    {b : Piece env (stateType::ctx) {p.lift with s := .bvar 0} nextBody Mode.step.expected}
    (right : StepCasts (inputs.nextState closed) b casts proofCasts)
    (beta : proofCasts ctx (StructuralStep.sequenceNextActual inputs b.represented.val right.sourceCore.val)
      (StructuralStep.sequenceContinuationType inputs b.represented.val (.lam stateType right.sourceCore.val)))
    (registered : env.constants ``WordLoopFacts.letState = some ⟨0,signature⟩)
    (constructor : env.constants ``HybridWord.Cmd.seq = some ⟨0,sequenceConstructor⟩)
    (coverage : Conversion.Covers conv 0 proofCasts) (exposure : Exposure env)
    (binder : Lean.Name) (nondep : Bool)
    (notAlias : sameTerm first p.s = false)
    (firstParsed : visit env conv exposure first ctx p .value .identity (fun _ => none) = some a)
    (nextParsed : visit env conv exposure nextBody (stateType::ctx) {p.lift with s := .bvar 0} .step .identity (fun _ => none) = some b) :
    ∃ piece, visit env conv exposure (source binder first nextBody nondep) ctx p .step .identity (fun _ => none) = some piece ∧
      Nonempty (StepCasts inputs piece casts proofCasts) := by
  obtain ⟨piece,success,typed,_⟩ := complete_code inputs closed stable embeds stateDeclared left returns right beta registered constructor coverage exposure binder nondep notAlias firstParsed nextParsed
  exact ⟨piece,success,typed⟩

end Loop

end IRComparison.WordFrontend.StructuralStateLet
