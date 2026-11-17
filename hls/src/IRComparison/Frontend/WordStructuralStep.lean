import IRComparison.Frontend.WordStructuralLoop

/-! Composition of direct ForInStep command certificates. Source binders and
commands are related directly, without a normalized intermediate program. -/
namespace IRComparison.WordFrontend.StructuralStep
open Lean4Lean LeanTyped LeanTypeInference Certificate StructuralBody StructuralLoop
variable {casts proofCasts : TypeCasts} [Arithmetic.Includes casts] [Arithmetic.Includes proofCasts]
set_option maxHeartbeats 1800000

def header : VExpr := optionBindHeader stateType Step.stepState
def nativeHeader : Lean.Expr := bindHead state stepType

theorem header_represents : Represents nativeHeader header := by
  exact .app (.app (.app (.app (.constant rfl) (.constant rfl))
    (.app (.app (.constant rfl) (.constant rfl)) (.constant rfl))) (.constant rfl))
    (.app (.constant rfl) (.constant rfl))

theorem header_inst (v : VExpr) (k : Nat) : header.inst v k = header :=
  (header_represents.closed 0 rfl).instN_eq (Nat.zero_le k)

def sequenceNextPremise : VExpr := .forallE stateType
  (Step.expected
    (bodyValue (.bvar 8) (.bvar 7) (.bvar 6) (.bvar 9) (.bvar 0) (.bvar 4))
    (.app (.bvar 2) (.bvar 0)))
def sequenceResult : VExpr := Step.expected
  (bodyValue (.bvar 8) (.bvar 7) (.bvar 6)
    (applications (.const ``HybridWord.Cmd.seq []) [.bvar 10,.bvar 9]) (.bvar 5) (.bvar 4))
  (applications header [.bvar 3,.bvar 2])
def sequenceSignature : VExpr := .forallE cmdType (.forallE cmdType
  (inputsType (.forallE (optionType stateType)
    (.forallE (.forallE stateType (optionType Step.stepState))
      (.forallE sequenceFirstPremise (.forallE sequenceNextPremise sequenceResult))))))

/-- The continuation fact expects a function application, while the recursively
constructed proof mentions its body. This explicitly isolates that beta
conversion from the compiler's semantic transformation. -/
def sequenceContinuationType (inputs : InputsTyped env ctx p) (b next : VExpr) : VExpr :=
  .forallE stateType (Step.expected
    (bodyValue inputs.i.val.lift inputs.x.val.lift inputs.y.val.lift b.lift
      (.bvar 0) inputs.ls.val.lift)
    (.app next.lift (.bvar 0)))

theorem sequence_typed (inputs : InputsTyped env ctx p)
    {a : Piece env ctx p first bodyExpected} (left : BodyCasts inputs a casts)
    (rightTarget : CastTyping env 0 casts ctx b cmdType)
    (nextTyped : CastTyping env 0 casts ctx next (.forallE stateType (optionType Step.stepState)))
    (nextProof : CastTyping env 0 casts ctx proofNext actual)
    (beta : casts ctx actual (sequenceContinuationType inputs b next))
    (registered : env.constants ``WordLoopFacts.sequence = some ⟨0,sequenceSignature⟩) :
    CastTyping env 0 casts ctx
      (applications (.const ``WordLoopFacts.sequence [])
        ([a.represented.val,b] ++ inputs.args ++
          [left.sourceCore.val,next,a.checked.proofCore.val,proofNext]))
      (Step.expected
        (bodyValue inputs.i.val inputs.x.val inputs.y.val
          (applications (.const ``HybridWord.Cmd.seq []) [a.represented.val,b]) inputs.s.val inputs.ls.val)
        (applications header [left.sourceCore.val,next])) := by
  have fact : CastTyping env 0 casts ctx (.const ``WordLoopFacts.sequence []) sequenceSignature :=
    .constant (levels := []) registered (by simp) rfl
  have a1 := CastTyping.application fact left.target
  simp only [Step.expected,Step.lifted,Step.stepState,sequenceSignature,inputsType,cmdType,wordType,stateType,wordsType,optionType,VExpr.inst] at a1
  have a2 := CastTyping.application a1 rightTarget
  simp only [VExpr.inst] at a2
  have a3 := inputs.apply_casts a2
  simp only [Step.expected,Step.lifted,Step.stepState,InputsTyped.instantiate,sequenceFirstPremise,sequenceNextPremise,sequenceResult,
    bodyValue,equalValues,optionType,stateType,wordType,applications,Nat.reduceAdd,
    ← VExpr.lift_instN_lo,VExpr.inst_lift,header_inst,VExpr.inst,
    VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] at a3
  have a4 := CastTyping.application a3 left.value
  simp only [Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst_lift,header_inst,VExpr.inst,
    VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] at a4
  have a5 := CastTyping.application a4 nextTyped
  simp only [Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst_lift,header_inst,VExpr.inst,
    VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] at a5
  have a6 := CastTyping.application a5 left.equality
  simp only [Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst_lift,header_inst,VExpr.inst,
    VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] at a6
  have cast := beta
  simp only [Step.expected,Step.lifted,Step.stepState,sequenceContinuationType,bodyValue,equalValues,optionType,stateType] at cast
  simpa only [Step.expected,Step.lifted,Step.stepState,InputsTyped.args,applications,List.cons_append,List.nil_append,bodyValue,
    equalValues,optionType,stateType,Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst_lift,
    header_inst,VExpr.inst,VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] using
    CastTyping.convertedApplication a6 nextProof cast

def sequenceNextActual (inputs : InputsTyped env ctx p) (b source : VExpr) : VExpr :=
  .forallE stateType (Step.expected
    (bodyValue inputs.i.val.lift inputs.x.val.lift inputs.y.val.lift b.lift
      (.bvar 0) inputs.ls.val.lift) source)

theorem sequence_next_typed (inputs : InputsTyped env ctx p)
    (closed : ClosedConstantTypes env) (stable : ClosedCasts casts)
    (stateDeclared : env.constants ``HybridWord.State = some ⟨0,.sort (.succ .zero)⟩)
    {b : Piece env (stateType::ctx) {p.lift with s := .bvar 0} nextBody Mode.step.expected}
    (right : StepCasts (inputs.nextState closed) b casts proofCasts) :
    CastTyping env 0 casts ctx b.represented.val cmdType ∧
    CastTyping env 0 casts ctx (.lam stateType right.sourceCore.val)
      (.forallE stateType (optionType Step.stepState)) ∧
    CastTyping env 0 proofCasts ctx (.lam stateType b.checked.proofCore.val)
      (sequenceNextActual inputs b.represented.val right.sourceCore.val) := by
  have targetClosed : b.represented.val.ClosedN 0 := b.represented.property.closed 0 b.closed
  have stateTyped : DirectTyping env 0 ctx stateType (.sort (.succ .zero)) :=
    .constant stateDeclared (by simp) rfl
  refine ⟨right.target.closed_context stable targetClosed ctx,
    .lambda (stateTyped.withCasts casts) right.value,?_⟩
  have proof := CastTyping.lambda (stateTyped.withCasts proofCasts) right.equality
  simpa only [sequenceNextActual,InputsTyped.nextState,InputsTyped.lift,
    targetClosed.lift_eq] using proof


def sequenceSource (first next : Lean.Expr) : Lean.Expr := Lean.mkApp2 nativeHeader first next

theorem sequence_finish (inputs : InputsTyped env ctx p)
    (closed : ClosedConstantTypes env) (stable : ClosedCasts casts)
    (embeds : ∀ scope a b, casts scope a b → proofCasts scope a b)
    (stateDeclared : env.constants ``HybridWord.State = some ⟨0,.sort (.succ .zero)⟩)
    {a : Piece env ctx p first bodyExpected} (left : BodyCasts inputs a casts proofCasts)
    {b : Piece env (stateType::ctx) {p.lift with s := .bvar 0} nextBody Mode.step.expected}
    (right : StepCasts (inputs.nextState closed) b casts proofCasts)
    (beta : proofCasts ctx (sequenceNextActual inputs b.represented.val right.sourceCore.val)
      (sequenceContinuationType inputs b.represented.val (.lam stateType right.sourceCore.val)))
    (registered : env.constants ``WordLoopFacts.sequence = some ⟨0,sequenceSignature⟩)
    (coverage : Conversion.Covers conv 0 proofCasts) (exposure : Exposure env)
    (binder : Lean.Name) (info : Lean.BinderInfo) :
    ∃ result, finish env conv exposure ctx
      (stepExpected (evalCmd p (app ``HybridWord.Cmd.seq [a.code,b.code]))
        (sequenceSource first (.lam binder state nextBody info)))
      (app ``HybridWord.Cmd.seq [a.code,b.code])
      (app ``WordLoopFacts.sequence ([a.code,b.code] ++ p.args ++
        [first,.lam binder state nextBody info,a.checked.proof,.lam binder state b.checked.proof info]))
      (a.checked.known.orElse b.checked.known) = some result ∧
      CastTyping env 0 proofCasts ctx result.proofCore.val result.core.val ∧
      result.code = app ``HybridWord.Cmd.seq [a.code,b.code] ∧
      result.proof = app ``WordLoopFacts.sequence ([a.code,b.code] ++ p.args ++
        [first,.lam binder state nextBody info,a.checked.proof,.lam binder state b.checked.proof info]) := by
  obtain ⟨target,nextTyped,nextProof⟩ := sequence_next_typed inputs closed stable stateDeclared right
  have typed := sequence_typed inputs (left.inProofCasts embeds) (target.mono embeds)
    (nextTyped.mono embeds) nextProof beta registered
  exact finish_cast_complete
    (Step.expected_represents (evalCmd_represents inputs
      (app_represents (.constant rfl) (.cons a.represented.property (.cons b.represented.property .nil))))
      (.app (.app header_represents left.sourceCore.property) (.lam (.constant rfl) right.sourceCore.property)))
    (app_represents (.constant rfl) (.cons a.represented.property (.cons b.represented.property
      (.cons inputs.i.property (.cons inputs.x.property (.cons inputs.y.property
        (.cons inputs.s.property (.cons inputs.ls.property (.cons left.sourceCore.property
          (.cons (.lam (.constant rfl) right.sourceCore.property)
            (.cons a.checked.proofCore.property (.cons (.lam (.constant rfl) b.checked.proofCore.property) .nil))))))))))))
    typed ((known_casts a.checked left.proof).orElse (known_casts b.checked right.proof))
    coverage exposure _

theorem sequence_complete_code (inputs : InputsTyped env ctx p)
    (closed : ClosedConstantTypes env) (stable : ClosedCasts casts)
    (embeds : ∀ scope a b, casts scope a b → proofCasts scope a b)
    (stateDeclared : env.constants ``HybridWord.State = some ⟨0,.sort (.succ .zero)⟩)
    {a : Piece env ctx p first bodyExpected} (left : BodyCasts inputs a casts proofCasts)
    {b : Piece env (stateType::ctx) {p.lift with s := .bvar 0} nextBody Mode.step.expected}
    (right : StepCasts (inputs.nextState closed) b casts proofCasts)
    (beta : proofCasts ctx (sequenceNextActual inputs b.represented.val right.sourceCore.val)
      (sequenceContinuationType inputs b.represented.val (.lam stateType right.sourceCore.val)))
    (registered : env.constants ``WordLoopFacts.sequence = some ⟨0,sequenceSignature⟩)
    (constructor : env.constants ``HybridWord.Cmd.seq = some ⟨0,sequenceConstructor⟩)
    (coverage : Conversion.Covers conv 0 proofCasts) (exposure : Exposure env)
    (bindLibrary : BindSignatures env)
    (steps : Step.Signatures env)
    (binder : Lean.Name) (info : Lean.BinderInfo)
    (firstParsed : StructuralBody.bodyRetained env conv exposure ctx p first = some a)
    (nextParsed : visit env conv exposure nextBody (stateType::ctx) {p.lift with s := .bvar 0}
      .step .identity (fun _ => none) = some b) :
    ∃ piece, visit env conv exposure (sequenceSource first (.lam binder state nextBody info)) ctx p
      .step .identity (fun _ => none) = some piece ∧
      Nonempty (StepCasts inputs piece casts proofCasts) ∧
      piece.code = app ``HybridWord.Cmd.seq [a.code,b.code] := by
  obtain ⟨artifact,checked,typed,_,_⟩ := sequence_finish inputs closed stable embeds stateDeclared
    left right beta registered coverage exposure binder info
  let code := ClosedTerm.app ``HybridWord.Cmd.seq [a.closedTerm,b.closedTerm]
  let piece : Piece env ctx p (sequenceSource first (.lam binder state nextBody info)) Mode.step.expected :=
    ⟨code.val,artifact,code.closed,code.represented⟩
  obtain ⟨_,nextTyped,_⟩ := sequence_next_typed inputs closed stable stateDeclared right
  have applied := CastTyping.application ((bindLibrary.header_typed (domain := stateType) (result := Step.stepState)
    (.constant stateDeclared (by simp) rfl) steps.step_typed (by trivial) (by trivial)).withCasts casts) left.value
  simp only [optionType,stateType,Step.stepState,VExpr.inst] at applied
  have sourceTyped := CastTyping.application applied nextTyped
  refine ⟨piece,?_,⟨⟨⟨_,.app (.app header_represents left.sourceCore.property)
    (.lam (.constant rfl) right.sourceCore.property)⟩,sourceTyped,?_,typed⟩⟩,rfl⟩
  · have ss : sameTerm state state = true := sameTerm_complete (Represents.constant rfl) (Represents.constant rfl)
    have sc : compatible env conv ctx state state = true :=
      compatible_same (Represents.constant rfl) (Represents.constant rfl) env conv ctx
    have st : translate state = some ⟨stateType,Represents.constant rfl⟩ := rfl
    have su : sameTerm state (.const ``PUnit [.succ .zero]) = false := rfl
    have modeValue : (Mode.step == Mode.value) = false := rfl
    have modeStep : (Mode.step == Mode.step) = true := rfl
    have args : (sequenceSource first (.lam binder state nextBody info)).getAppArgs =
      #[.const ``Option [.zero],Lean.mkAppN (.const ``Monad.toBind [.zero,.zero])
        #[.const ``Option [.zero],.const ``instMonadOption [.zero]],state,stepType,first,.lam binder state nextBody info] := rfl
    have empty : underFunctions (fun _ => (none : Option (Continuation env))) = (fun _ => none) := by
      funext n; cases n <;> rfl
    have firstParsed' : visit env conv exposure first ctx p .body .identity (fun _ => none) = some a := firstParsed
    rw [visit]
    simp [node,modeValue,modeStep,letParts,applicationHead,makeContinuation,continuationParts,lambdaChain,
      Substitution.apply,ScalarEnvironment.arguments,ScalarEnvironment.below,lambdaParts,under,
      empty,ss,sc,st,sequenceSource,nativeHeader,Lean.mkApp,Lean.mkApp2,Lean.mkAppB,
      Lean.Expr.getAppFn,Lean.Expr.constName?,bindHead,Lean.mkAppN,List.map_cons,List.map_nil]
    simp only [sequenceSource,nativeHeader,Lean.mkApp,Lean.mkApp2,Lean.mkAppB,bindHead,Lean.mkAppN] at args
    simp only [List.map_append,List.map_cons,List.map_nil,List.nil_append,List.cons_append,
      Function.comp_apply,List.length_cons,List.length_nil,Nat.reduceAdd,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.unattach_some,
      args,Array.getElem?_eq_getElem,Array.back?,su,ss,sc,st,
      Option.bind_some,Bool.false_eq_true,Bool.true_eq_false,ite_false,ite_true]
    simp [firstParsed',nextParsed,finishBody,Mode.expected,ClosedTerm.app,Piece.closedTerm,
      code,piece,sequenceSource,nativeHeader,Lean.mkApp2,Lean.mkAppB,Lean.mkApp,app] at checked ⊢
    refine ⟨first,?_,a,firstParsed',artifact,checked,rfl⟩
    rfl
  · obtain ⟨target,_,_⟩ := sequence_next_typed inputs closed stable stateDeclared right
    have fact : CastTyping env 0 casts ctx (.const ``HybridWord.Cmd.seq []) sequenceConstructor :=
      .constant constructor (by simp) rfl
    have first := CastTyping.application fact left.target
    simp only [sequenceConstructor,cmdType,VExpr.inst] at first
    exact .application first target

theorem sequence_complete (inputs : InputsTyped env ctx p)
    (closed : ClosedConstantTypes env) (stable : ClosedCasts casts)
    (embeds : ∀ scope a b, casts scope a b → proofCasts scope a b)
    (stateDeclared : env.constants ``HybridWord.State = some ⟨0,.sort (.succ .zero)⟩)
    {a : Piece env ctx p first bodyExpected} (left : BodyCasts inputs a casts proofCasts)
    {b : Piece env (stateType::ctx) {p.lift with s := .bvar 0} nextBody Mode.step.expected}
    (right : StepCasts (inputs.nextState closed) b casts proofCasts)
    (beta : proofCasts ctx (sequenceNextActual inputs b.represented.val right.sourceCore.val)
      (sequenceContinuationType inputs b.represented.val (.lam stateType right.sourceCore.val)))
    (registered : env.constants ``WordLoopFacts.sequence = some ⟨0,sequenceSignature⟩)
    (constructor : env.constants ``HybridWord.Cmd.seq = some ⟨0,sequenceConstructor⟩)
    (coverage : Conversion.Covers conv 0 proofCasts) (exposure : Exposure env)
    (bindLibrary : BindSignatures env)
    (steps : Step.Signatures env)
    (binder : Lean.Name) (info : Lean.BinderInfo)
    (firstParsed : StructuralBody.bodyRetained env conv exposure ctx p first = some a)
    (nextParsed : visit env conv exposure nextBody (stateType::ctx) {p.lift with s := .bvar 0}
      .step .identity (fun _ => none) = some b) :
    ∃ piece, visit env conv exposure (sequenceSource first (.lam binder state nextBody info)) ctx p
      .step .identity (fun _ => none) = some piece ∧
      Nonempty (StepCasts inputs piece casts proofCasts) := by
  obtain ⟨piece,success,typed,_⟩ := sequence_complete_code inputs closed stable embeds stateDeclared left right beta registered constructor coverage exposure bindLibrary steps binder info firstParsed nextParsed
  exact ⟨piece,success,typed⟩

namespace Conditional
open Certificate.Branch

def choice (v decision yes no : VExpr) : VExpr := iteValue (optionType Step.stepState) (condition v) decision yes no
def source (v decision yes no : Lean.Expr) : Lean.Expr :=
  Step.nativeChoice (option stepType) (nativeCondition v) decision yes no

theorem source_represents (vRep : Represents v vc) (dRep : Represents d dc)
    (aRep : Represents a ac) (bRep : Represents b bc) : Represents (source v d a b) (choice vc dc ac bc) :=
  Step.nativeChoice_represents (.app (.constant rfl) (.app (.constant rfl) (.constant rfl)))
    (condition_represents vRep) dRep aRep bRep

def leftPremise : VExpr := Step.expected
  (bodyValue (.bvar 9) (.bvar 8) (.bvar 7) (.bvar 11) (.bvar 6) (.bvar 5)) (.bvar 2)
def rightPremise : VExpr := Step.expected
  (bodyValue (.bvar 10) (.bvar 9) (.bvar 8) (.bvar 11) (.bvar 7) (.bvar 6)) (.bvar 2)
def resultType : VExpr := Step.expected
  (bodyValue (.bvar 11) (.bvar 10) (.bvar 9)
    (applications (.const ``HybridWord.Cmd.branch []) [.bvar 14,.bvar 13,.bvar 12]) (.bvar 8) (.bvar 7))
  (choice (.bvar 6) (.bvar 5) (.bvar 4) (.bvar 3))
def signature : VExpr := .forallE exprType (.forallE cmdType (.forallE cmdType
  (inputsType (.forallE wordType (.forallE (.app (.const ``Decidable []) (condition (.bvar 0)))
    (.forallE (optionType Step.stepState) (.forallE (optionType Step.stepState)
      (.forallE scalarPremise (.forallE leftPremise (.forallE rightPremise resultType))))))))))
theorem fact_typed (inputs : InputsTyped env ctx p)
    {e : Piece env ctx p v scalarExpected} (value : ScalarCasts inputs e casts)
    {a : Piece env ctx p yes Mode.step.expected} (left : StepCasts inputs a casts)
    {b : Piece env ctx p no Mode.step.expected} (right : StepCasts inputs b casts)
    (decisionTyped : CheckedTyping env 0 casts ctx decision (.app (.const ``Decidable []) (condition value.sourceCore.val)))
    (registered : env.constants ``WordLoopFacts.branchCmd = some ⟨0,signature⟩) :
    CastTyping env 0 casts ctx
      (applications (.const ``WordLoopFacts.branchCmd [])
        ([e.represented.val,a.represented.val,b.represented.val] ++ inputs.args ++
          [value.sourceCore.val,decision,left.sourceCore.val,right.sourceCore.val,
            e.checked.proofCore.val,a.checked.proofCore.val,b.checked.proofCore.val]))
      (Step.expected
        (bodyValue inputs.i.val inputs.x.val inputs.y.val
          (applications (.const ``HybridWord.Cmd.branch []) [e.represented.val,a.represented.val,b.represented.val])
          inputs.s.val inputs.ls.val)
        (choice value.sourceCore.val decision left.sourceCore.val right.sourceCore.val)) := by
  have fact : CastTyping env 0 casts ctx (.const ``WordLoopFacts.branchCmd []) signature :=
    by
      have h := CastTyping.constant (casts := casts) (ctx := ctx) (U := 0) (levels := [])
        registered (by simp) rfl
      simpa [Step.expected,Step.lifted,Step.stepState,signature,inputsType,scalarPremise,leftPremise,rightPremise,resultType,
        choice,iteValue,condition,testHeader,Arithmetic.literalTerm,Arithmetic.width,
        exprType,cmdType,wordType,stateType,wordsType,equalValues,optionType,
        scalarValue,bodyValue,someValue,applications,VExpr.instL,VLevel.inst,numeral,
        Arithmetic.natType] using h
  have a1 := CastTyping.application fact value.target
  simp only [Step.expected,Step.lifted,Step.stepState,signature,inputsType,exprType,cmdType,wordType,stateType,wordsType,optionType,VExpr.inst] at a1
  have a2 := CastTyping.application a1 left.target
  simp only [VExpr.inst] at a2
  have a3 := CastTyping.application a2 right.target
  try simp only [VExpr.inst] at a3
  have a4 := inputs.apply_casts a3
  simp only [Step.expected,Step.lifted,Step.stepState,InputsTyped.instantiate,scalarPremise,leftPremise,rightPremise,resultType,choice,iteValue,
    scalarValue,bodyValue,equalValues,someValue,optionType,stateType,wordType,applications,
    Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst_lift,condition_inst,VExpr.inst,
    VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] at a4
  have a5 := CastTyping.checkedApplication a4 value.value
  simp only [Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst_lift,condition_inst,VExpr.inst,
    VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] at a5
  have a6 := CastTyping.checkedApplication a5 decisionTyped
  simp only [Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst_lift,condition_inst,VExpr.inst,
    VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] at a6
  have a7 := CastTyping.application a6 left.value
  simp only [Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst_lift,condition_inst,VExpr.inst,
    VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] at a7
  have a8 := CastTyping.application a7 right.value
  simp only [Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst_lift,condition_inst,VExpr.inst,
    VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] at a8
  have a9 := CastTyping.application a8 value.equality
  simp only [Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst_lift,condition_inst,VExpr.inst,
    VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] at a9
  have a10 := CastTyping.application a9 left.equality
  simp only [Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst_lift,condition_inst,VExpr.inst,
    VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] at a10
  have a11 := CastTyping.application a10 right.equality
  simp only [Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst_lift,condition_inst,VExpr.inst,
    VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] at a11
  simpa only [Step.expected,Step.lifted,Step.stepState,InputsTyped.args,applications,List.cons_append,List.nil_append,bodyValue,
    equalValues,optionType,stateType,choice,iteValue] using a11

theorem finish_complete (inputs : InputsTyped env ctx p)
    {e : Piece env ctx p v scalarExpected} (value : ScalarCasts inputs e casts)
    {a : Piece env ctx p yes Mode.step.expected} (left : StepCasts inputs a casts)
    {b : Piece env ctx p no Mode.step.expected} (right : StepCasts inputs b casts)
    (decisionRep : Represents d dc)
    (decisionTyped : CastTyping env 0 casts ctx dc (.app (.const ``Decidable []) (condition value.sourceCore.val)))
    (registered : env.constants ``WordLoopFacts.branchCmd = some ⟨0,signature⟩)
    (coverage : Conversion.Covers conv 0 casts) (exposure : Exposure env) :
    ∃ result, finish env conv exposure ctx
      (Mode.step.expected p (app ``HybridWord.Cmd.branch [e.code,a.code,b.code]) (source v d yes no))
      (app ``HybridWord.Cmd.branch [e.code,a.code,b.code])
      (app ``WordLoopFacts.branchCmd ([e.code,a.code,b.code] ++ p.args ++
        [v,d,yes,no,e.checked.proof,a.checked.proof,b.checked.proof]))
      (e.checked.known.orElse (a.checked.known.orElse b.checked.known)) = some result ∧
      CastTyping env 0 casts ctx result.proofCore.val result.core.val ∧
      result.code = app ``HybridWord.Cmd.branch [e.code,a.code,b.code] ∧
      result.proof = app ``WordLoopFacts.branchCmd ([e.code,a.code,b.code] ++ p.args ++
        [v,d,yes,no,e.checked.proof,a.checked.proof,b.checked.proof]) := by
  have targetRep := app_represents (f := Lean.Expr.const ``HybridWord.Cmd.branch []) (.constant rfl)
    (.cons e.represented.property (.cons a.represented.property (.cons b.represented.property .nil)))
  have proofRep := app_represents (f := Lean.Expr.const ``WordLoopFacts.branchCmd []) (.constant rfl)
    (.cons e.represented.property (.cons a.represented.property (.cons b.represented.property
      (.cons inputs.i.property (.cons inputs.x.property (.cons inputs.y.property
        (.cons inputs.s.property (.cons inputs.ls.property
          (.cons value.sourceCore.property (.cons decisionRep (.cons left.sourceCore.property
            (.cons right.sourceCore.property (.cons e.checked.proofCore.property
              (.cons a.checked.proofCore.property (.cons b.checked.proofCore.property .nil)))))))))))))))
  exact finish_cast_complete (Step.expected_represents (evalCmd_represents inputs targetRep)
    (source_represents value.sourceCore.property decisionRep left.sourceCore.property right.sourceCore.property))
    proofRep (fact_typed inputs value left right decisionTyped registered)
    ((known_casts e.checked value.proof).orElse
      ((known_casts a.checked left.proof).orElse (known_casts b.checked right.proof))) coverage exposure _


theorem split_complete_code (inputs : InputsTyped env ctx p)
    {e : Piece env ctx p v scalarExpected} (value : ScalarCasts inputs e casts proofCasts)
    {a : Piece env ctx p yes Mode.step.expected} (left : StepCasts inputs a casts proofCasts)
    {b : Piece env ctx p no Mode.step.expected} (right : StepCasts inputs b casts proofCasts)
    (decisionRep : Represents d dc)
    (predicateTyped : CastTyping env 0 casts ctx (condition value.sourceCore.val) (.sort .zero))
    (decisionTyped : CastTyping env 0 casts ctx dc (.app (.const ``Decidable []) (condition value.sourceCore.val)))
    (optionTyped : DirectTyping env 0 ctx (optionType Step.stepState) (.sort (.succ .zero)))
    (iteDecl : env.constants ``ite = some iteSignature)
    (registered : env.constants ``WordLoopFacts.branchCmd = some ⟨0,signature⟩)
    (constructor : env.constants ``HybridWord.Cmd.branch = some ⟨0,constructorSignature⟩)
    (embeds : ∀ scope a b, casts scope a b → proofCasts scope a b)
    (coverage : Conversion.Covers conv 0 proofCasts) (exposure : Exposure env)
    (valueParsed : ScalarEnvironment.parse env conv exposure ctx p v = some e)
    (leftParsed : visit env conv exposure yes ctx p .step .identity (fun _ => none) = some a)
    (rightParsed : visit env conv exposure no ctx p .step .identity (fun _ => none) = some b) :
    ∃ piece, visit env conv exposure (source v d yes no) ctx p .step .identity (fun _ => none) = some piece ∧
      Nonempty (StepCasts inputs piece casts proofCasts) ∧ piece.code = app ``HybridWord.Cmd.branch [e.code,a.code,b.code] := by
  obtain ⟨artifact,checked,proofTyped,_,_⟩ := finish_complete inputs (value.inProofCasts embeds)
    (left.inProofCasts embeds) (right.inProofCasts embeds) decisionRep (decisionTyped.mono embeds)
    registered coverage exposure
  let code := ClosedTerm.app ``HybridWord.Cmd.branch [e.closedTerm,a.closedTerm,b.closedTerm]
  let piece : Piece env ctx p (source v d yes no) Mode.step.expected :=
    ⟨code.val,artifact,code.closed,code.represented⟩
  refine ⟨piece,?_,⟨⟨⟨_,source_represents value.sourceCore.property decisionRep
    left.sourceCore.property right.sourceCore.property⟩,?_,?_,proofTyped⟩⟩,rfl⟩
  · have mode : (Mode.step == Mode.value) = false := rfl
    have modeStep : (Mode.step == Mode.step) = true := rfl
    have args : (source v d yes no).getAppArgs.toList =
      [option stepType,nativeCondition v,d,yes,no] := rfl
    have test : nonzeroValue (nativeCondition v) = some v := rfl
    rw [visit]
    simp [node,mode,modeStep,letParts,applicationHead,makeContinuation,continuationParts,lambdaChain,
      Substitution.apply,ScalarEnvironment.arguments,ScalarEnvironment.below,
      source,Step.nativeChoice,Lean.mkApp5,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,
      Lean.mkApp,Lean.mkAppB,List.map_cons,List.map_nil,Lean.Expr.getAppFn,
      Lean.Expr.constName?,StructuralBody.arguments]
    simp only [source,Step.nativeChoice,Lean.mkApp5,Lean.mkApp4,Lean.mkApp3,
      Lean.mkApp2,Lean.mkApp,Lean.mkAppB] at args
    simp only [args,test,Option.bind_some,valueParsed,leftParsed,rightParsed]
    simp [finishBody,Mode.expected,ClosedTerm.app,Piece.closedTerm,code,piece,
      source,Step.nativeChoice,app] at checked ⊢
    exact ⟨e,valueParsed,artifact,checked,rfl⟩
  · exact ite_typed optionTyped (by trivial) predicateTyped decisionTyped left.value right.value iteDecl
  · have h : CastTyping env 0 casts ctx (.const ``HybridWord.Cmd.branch []) constructorSignature :=
      .constant constructor (by simp) rfl
    have a1 := CastTyping.application h value.target
    simp only [constructorSignature,exprType,cmdType,VExpr.inst] at a1
    have a2 := CastTyping.application a1 left.target
    simp only [VExpr.inst] at a2
    exact .application a2 right.target

theorem split_complete (inputs : InputsTyped env ctx p)
    {e : Piece env ctx p v scalarExpected} (value : ScalarCasts inputs e casts proofCasts)
    {a : Piece env ctx p yes Mode.step.expected} (left : StepCasts inputs a casts proofCasts)
    {b : Piece env ctx p no Mode.step.expected} (right : StepCasts inputs b casts proofCasts)
    (decisionRep : Represents d dc)
    (predicateTyped : CastTyping env 0 casts ctx (condition value.sourceCore.val) (.sort .zero))
    (decisionTyped : CastTyping env 0 casts ctx dc (.app (.const ``Decidable []) (condition value.sourceCore.val)))
    (optionTyped : DirectTyping env 0 ctx (optionType Step.stepState) (.sort (.succ .zero)))
    (iteDecl : env.constants ``ite = some iteSignature)
    (registered : env.constants ``WordLoopFacts.branchCmd = some ⟨0,signature⟩)
    (constructor : env.constants ``HybridWord.Cmd.branch = some ⟨0,constructorSignature⟩)
    (embeds : ∀ scope a b, casts scope a b → proofCasts scope a b)
    (coverage : Conversion.Covers conv 0 proofCasts) (exposure : Exposure env)
    (valueParsed : ScalarEnvironment.parse env conv exposure ctx p v = some e)
    (leftParsed : visit env conv exposure yes ctx p .step .identity (fun _ => none) = some a)
    (rightParsed : visit env conv exposure no ctx p .step .identity (fun _ => none) = some b) :
    ∃ piece, visit env conv exposure (source v d yes no) ctx p .step .identity (fun _ => none) = some piece ∧
      Nonempty (StepCasts inputs piece casts proofCasts) := by
  obtain ⟨piece,success,typed,_⟩ := split_complete_code inputs value left right decisionRep
    predicateTyped decisionTyped optionTyped iteDecl registered constructor embeds coverage exposure
    valueParsed leftParsed rightParsed
  exact ⟨piece,success,typed⟩

theorem complete (inputs : InputsTyped env ctx p)
    {e : Piece env ctx p v scalarExpected} (value : ScalarCasts inputs e casts)
    {a : Piece env ctx p yes Mode.step.expected} (left : StepCasts inputs a casts proofCasts)
    {b : Piece env ctx p no Mode.step.expected} (right : StepCasts inputs b casts proofCasts)
    (decisionRep : Represents d dc)
    (predicateTyped : CastTyping env 0 casts ctx (condition value.sourceCore.val) (.sort .zero))
    (decisionTyped : CastTyping env 0 casts ctx dc (.app (.const ``Decidable []) (condition value.sourceCore.val)))
    (optionTyped : DirectTyping env 0 ctx (optionType Step.stepState) (.sort (.succ .zero)))
    (iteDecl : env.constants ``ite = some iteSignature)
    (registered : env.constants ``WordLoopFacts.branchCmd = some ⟨0,signature⟩)
    (constructor : env.constants ``HybridWord.Cmd.branch = some ⟨0,constructorSignature⟩)
    (embeds : ∀ scope a b, casts scope a b → proofCasts scope a b)
    (coverage : Conversion.Covers conv 0 proofCasts) (exposure : Exposure env)
    (valueParsed : ScalarEnvironment.parse env conv exposure ctx p v = some e)
    (leftParsed : visit env conv exposure yes ctx p .step .identity (fun _ => none) = some a)
    (rightParsed : visit env conv exposure no ctx p .step .identity (fun _ => none) = some b) :
    ∃ piece, visit env conv exposure (source v d yes no) ctx p .step .identity (fun _ => none) = some piece ∧
      Nonempty (StepCasts inputs piece casts proofCasts) := by
  exact split_complete inputs (value.mapProofs embeds) left right decisionRep predicateTyped decisionTyped
    optionTyped iteDecl registered constructor embeds coverage exposure valueParsed leftParsed rightParsed

end Conditional

namespace Alias
def premise : VExpr := .forallE stateType
  (Step.expected
    (bodyValue (.bvar 6) (.bvar 5) (.bvar 4) (.bvar 7) (.bvar 0) (.bvar 2))
    (.app (.bvar 1) (.bvar 0)))
def resultType : VExpr := Step.expected
  (bodyValue (.bvar 6) (.bvar 5) (.bvar 4) (.bvar 7) (.bvar 3) (.bvar 2))
  (.app (.bvar 1) (.bvar 3))
def signature : VExpr := .forallE cmdType (inputsType
  (.forallE (.forallE stateType (optionType Step.stepState)) (.forallE premise resultType)))

theorem fact_typed (inputs : InputsTyped env ctx p)
    (targetTyped : CastTyping env 0 casts ctx code cmdType)
    (nextTyped : CastTyping env 0 casts ctx next (.forallE stateType (optionType Step.stepState)))
    (proofTyped : CastTyping env 0 casts ctx proof actual)
    (beta : casts ctx actual (sequenceContinuationType inputs code next))
    (registered : env.constants ``WordLoopFacts.letStateAlias = some ⟨0,signature⟩) :
    CastTyping env 0 casts ctx
      (applications (.const ``WordLoopFacts.letStateAlias []) ([code] ++ inputs.args ++ [next,proof]))
      (Step.expected
        (bodyValue inputs.i.val inputs.x.val inputs.y.val code inputs.s.val inputs.ls.val)
        (.app next inputs.s.val)) := by
  have fact : CastTyping env 0 casts ctx (.const ``WordLoopFacts.letStateAlias []) signature :=
    .constant registered (by simp) rfl
  have a1 := CastTyping.application fact targetTyped
  simp only [Step.expected,Step.lifted,Step.stepState,signature,inputsType,cmdType,wordType,stateType,wordsType,optionType,VExpr.inst] at a1
  have a2 := inputs.apply_casts a1
  simp only [Step.expected,Step.lifted,Step.stepState,InputsTyped.instantiate,premise,resultType,bodyValue,equalValues,optionType,stateType,applications,
    VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower,Nat.reduceAdd,
    ← VExpr.lift_instN_lo,VExpr.inst_lift] at a2
  have a3 := CastTyping.application a2 nextTyped
  simp only [Step.expected,Step.lifted,Step.stepState,VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower,Nat.reduceAdd,
    ← VExpr.lift_instN_lo,VExpr.inst_lift] at a3
  have cast := beta
  simp only [Step.expected,Step.lifted,Step.stepState,sequenceContinuationType,bodyValue,equalValues,optionType,stateType,applications] at cast
  simpa only [InputsTyped.args,applications,List.cons_append,List.nil_append,bodyValue,equalValues,
    optionType,stateType,VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower,
    Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst_lift] using CastTyping.convertedApplication a3 proofTyped cast

theorem substitute_latest_let (σ : Substitution) :
    σ.apply (.letE binder state st nextBody nondep) =
      .letE binder state (σ.apply st) ((under σ).apply nextBody) nondep := by
  cases σ <;> rfl

theorem mapped_alias_complete_code (inputs : InputsTyped env ctx p)
    (closed : ClosedConstantTypes env) (stable : ClosedCasts casts)
    (embeds : ∀ scope a b, casts scope a b → proofCasts scope a b)
    (stateDeclared : env.constants ``HybridWord.State = some ⟨0,.sort (.succ .zero)⟩)
    {b : Piece env (stateType::ctx) {p.lift with s := .bvar 0} ((under σ).apply nextBody) Mode.step.expected}
    (right : StepCasts (inputs.nextState closed) b casts proofCasts)
    (beta : proofCasts ctx (sequenceNextActual inputs b.represented.val right.sourceCore.val)
      (sequenceContinuationType inputs b.represented.val (.lam stateType right.sourceCore.val)))
    (registered : env.constants ``WordLoopFacts.letStateAlias = some ⟨0,signature⟩)
    (coverage : Conversion.Covers conv 0 proofCasts) (exposure : Exposure env)
    (binder : Lean.Name) (nondep : Bool)
    (current : σ.apply st = p.s)
    (parsed : visit env conv exposure nextBody (stateType::ctx) {p.lift with s := .bvar 0}
      .step (under σ) (underFunctions fs) = some b) :
    ∃ piece, visit env conv exposure (.letE binder state st nextBody nondep) ctx p
      .step σ fs = some piece ∧
      Nonempty (StepCasts inputs piece casts proofCasts) ∧ piece.code = b.code := by
  obtain ⟨target,nextTyped,nextProof⟩ := sequence_next_typed inputs closed stable stateDeclared right
  have fact := fact_typed inputs (target.mono embeds) (nextTyped.mono embeds) nextProof beta registered
  have sourceRep : Represents (σ.apply (.letE binder state st nextBody nondep))
      (.app (.lam stateType right.sourceCore.val) inputs.s.val) :=
    by
      rw [substitute_latest_let,current]
      exact .letE (.constant rfl) inputs.s.property right.sourceCore.property
  have nextRep : Represents (.lam binder state ((under σ).apply nextBody) .default) (.lam stateType right.sourceCore.val) :=
    .lam (.constant rfl) right.sourceCore.property
  have proofRep : Represents (.lam binder state b.checked.proof .default) (.lam stateType b.checked.proofCore.val) :=
    .lam (.constant rfl) b.checked.proofCore.property
  obtain ⟨artifact,checked,typed,_,_⟩ := finish_cast_complete
    (Step.expected_represents (evalCmd_represents inputs b.represented.property) sourceRep)
    (app_represents (Represents.constant (name := ``WordLoopFacts.letStateAlias) (us := []) rfl)
      (.cons b.represented.property (.cons inputs.i.property (.cons inputs.x.property (.cons inputs.y.property
        (.cons inputs.s.property (.cons inputs.ls.property (.cons nextRep (.cons proofRep .nil)))))))))
    fact (known_casts b.checked right.proof) coverage exposure b.code
  let piece : Piece env ctx p (σ.apply (.letE binder state st nextBody nondep)) Mode.step.expected :=
    ⟨b.code,artifact,b.closed,b.represented⟩
  refine ⟨piece,?_,⟨⟨⟨_,sourceRep⟩,CastTyping.application nextTyped (inputs.hs.withCasts casts),target,typed⟩⟩,rfl⟩
  have typeSame := sameTerm_complete (a := state) (b := state) (Represents.constant rfl) (Represents.constant rfl)
  have valueSame := sameTerm_complete inputs.s.property inputs.s.property
  have translated : translate state = some ⟨stateType,Represents.constant rfl⟩ := rfl
  have stateApply : σ.apply state = state := by cases σ <;> rfl
  have modeValue : (Mode.step == Mode.value) = false := rfl
  have modeStep : (Mode.step == Mode.step) = true := rfl
  cases σ
  all_goals
    rw [visit]
    simp only [node,letParts,modeValue,modeStep,Substitution.apply,LeanBindings.substitute,under,
      state,WordFrontend.state] at current parsed checked typeSame translated ⊢
    simp only [current,typeSame,valueSame,translated,Bool.false_eq_true,ite_false,Bool.true_and,
      Bool.true_eq_false,Bool.and_self,Bool.and_true,ite_true,bind,Option.bind,pure,Option.pure_def]
    rw [parsed]
    dsimp only
    simp only [finishBody,Mode.expected,piece,Piece.closedTerm,app,ClosedTerm.const,
      List.map_cons,List.map_nil,List.foldl_cons,List.foldl_nil,Substitution.apply,LeanBindings.substitute,
      state,WordFrontend.state] at checked ⊢
    simp only [Inputs.args,List.cons_append,List.nil_append,List.foldl_cons,List.foldl_nil] at checked ⊢
    rw [checked]
    all_goals rfl

theorem alias_step_complete (inputs : InputsTyped env ctx p)
    (closed : ClosedConstantTypes env) (stable : ClosedCasts casts)
    (embeds : ∀ scope a b, casts scope a b → proofCasts scope a b)
    (stateDeclared : env.constants ``HybridWord.State = some ⟨0,.sort (.succ .zero)⟩)
    {b : Piece env (stateType::ctx) {p.lift with s := .bvar 0} nextBody Mode.step.expected}
    (right : StepCasts (inputs.nextState closed) b casts proofCasts)
    (beta : proofCasts ctx (sequenceNextActual inputs b.represented.val right.sourceCore.val)
      (sequenceContinuationType inputs b.represented.val (.lam stateType right.sourceCore.val)))
    (registered : env.constants ``WordLoopFacts.letStateAlias = some ⟨0,signature⟩)
    (coverage : Conversion.Covers conv 0 proofCasts) (exposure : Exposure env)
    (binder : Lean.Name) (nondep : Bool)
    (parsed : visit env conv exposure nextBody (stateType::ctx) {p.lift with s := .bvar 0}
      .step .identity (fun _ => none) = some b) :
    ∃ piece, visit env conv exposure (.letE binder state p.s nextBody nondep) ctx p
      .step .identity (fun _ => none) = some piece ∧
      Nonempty (StepCasts inputs piece casts proofCasts) ∧ piece.code = b.code := by
  have empty : underFunctions (fun _ => (none : Option (Continuation env))) = (fun _ => none) := by
    funext n; cases n <;> rfl
  exact mapped_alias_complete_code (σ := .identity) (fs := fun _ => none) (st := p.s) inputs
    closed stable embeds stateDeclared right beta registered coverage exposure binder nondep rfl
    (by simpa only [under,empty] using parsed)

end Alias

end IRComparison.WordFrontend.StructuralStep
