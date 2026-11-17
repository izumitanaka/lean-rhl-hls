import IRComparison.Frontend.WordStructuralSyntax

/-! Typing of the direct structural loop traversal. Its command certificate
already relates the command to the original ForInStep-valued body; no
intermediate normalized source or second body traversal is required. -/
namespace IRComparison.WordFrontend.StructuralLoop
open Lean4Lean LeanTyped LeanTypeInference Certificate StructuralBody
variable {casts proofCasts : TypeCasts} [Arithmetic.Includes casts] [Arithmetic.Includes proofCasts]
set_option maxHeartbeats 1800000

structure ValueCasts (inputs : InputsTyped env ctx p)
    (piece : Piece env ctx p source Mode.value.expected) (casts : TypeCasts)
    (proofCasts : TypeCasts := casts) where
  sourceCore : {core // Represents source core}
  value : CastTyping env 0 casts ctx sourceCore.val stateType
  target : CastTyping env 0 casts ctx piece.represented.val cmdType
  proof : CastTyping env 0 proofCasts ctx piece.checked.proofCore.val piece.checked.core.val

def ValueCasts.asBody {piece : Piece env ctx p source Mode.value.expected}
    (typed : ValueCasts inputs piece casts proofCasts) (returns : Return.Signatures env) :
    BodyCasts inputs (⟨piece.code,piece.checked,piece.closed,piece.represented⟩ :
      Piece env ctx p (someExpr state source) bodyExpected) casts proofCasts where
  sourceCore := ⟨_,.app (.app (.constant rfl) (.constant rfl)) typed.sourceCore.property⟩
  value := .application ((returns.header_typed .some).withCasts casts) typed.value
  target := typed.target
  proof := typed.proof

theorem value_skip_complete_code (inputs : InputsTyped env ctx p)
    (registered : env.constants ``WordFrontendFacts.skip = some ⟨0,Return.Form.some.signature⟩)
    (constructor : env.constants ``HybridWord.Cmd.skip = some ⟨0,cmdType⟩)
    (conv : Conversion env) (exposure : Exposure env) (casts : TypeCasts) [Arithmetic.Includes casts] (coverage : conv.Covers 0 casts) :
    ∃ piece, visit env conv exposure p.s ctx p .value .identity (fun _ => none) = some piece ∧
      Nonempty (ValueCasts inputs piece casts) ∧ piece.code = .const ``HybridWord.Cmd.skip [] := by
  obtain ⟨artifact,checked,proofTyped,_,_⟩ := finish_cast_complete
    (bodyExpected_represents inputs (code := Lean.Expr.const ``HybridWord.Cmd.skip []) (.constant rfl)
      (.app Return.Form.some.header_represents inputs.s.property))
    (app_represents (f := Lean.Expr.const ``WordFrontendFacts.skip []) (.constant rfl) inputs.arguments)
    (Return.skip_typed inputs .some registered)
    (known := noKnownTypes env 0) (by intro _ _ _ h; cases h) coverage exposure (.const ``HybridWord.Cmd.skip [])
  let code := ClosedTerm.const ``HybridWord.Cmd.skip
  let piece : Piece env ctx p p.s Mode.value.expected := ⟨code.val,artifact,code.closed,code.represented⟩
  refine ⟨piece,?_,⟨⟨inputs.s,inputs.hs.withCasts casts,
    .constant constructor (by simp) rfl,proofTyped⟩⟩,rfl⟩
  have same := sameTerm_complete inputs.s.property inputs.s.property
  rw [visit]
  have mode : (Mode.value == Mode.value) = true := rfl
  simp [node,mode,Substitution.apply,same,finishBody,code,piece,ClosedTerm.const,Mode.expected,
    Return.Form.source,Return.Form.nativeHeader,Return.Form.fact,checked]
  exact checked

theorem value_skip_complete (inputs : InputsTyped env ctx p)
    (registered : env.constants ``WordFrontendFacts.skip = some ⟨0,Return.Form.some.signature⟩)
    (constructor : env.constants ``HybridWord.Cmd.skip = some ⟨0,cmdType⟩)
    (conv : Conversion env) (exposure : Exposure env) (casts : TypeCasts) [Arithmetic.Includes casts] (coverage : conv.Covers 0 casts) :
    ∃ piece, visit env conv exposure p.s ctx p .value .identity (fun _ => none) = some piece ∧
      Nonempty (ValueCasts inputs piece casts) := by
  obtain ⟨piece,success,typed,_⟩ := value_skip_complete_code inputs registered constructor conv exposure casts coverage
  exact ⟨piece,success,typed⟩

theorem value_assign_split_complete_code (inputs : InputsTyped env ctx p)
    (register : NatArgument env ctx r) {a : Piece env ctx p v scalarExpected}
    (value : ScalarCasts inputs a casts proofCasts)
    (registered : env.constants ``WordFrontendFacts.assign = some ⟨0,assignSignatureWith Return.Form.some.header⟩)
    (constructor : env.constants ``HybridWord.Cmd.assign = some ⟨0,Return.assignConstructor⟩)
    (setter : env.constants ``HybridWord.State.set = some ⟨0,Return.setterSignature⟩)
    (embeds : ∀ scope a b, casts scope a b → proofCasts scope a b)
    (coverage : Conversion.Covers conv 0 proofCasts) (exposure : Exposure env)
    (parsed : ScalarEnvironment.parse env conv exposure ctx p v = some a) :
    ∃ piece, visit env conv exposure (app ``HybridWord.State.set [p.s,r,v]) ctx p .value .identity (fun _ => none) = some piece ∧
      Nonempty (ValueCasts inputs piece casts proofCasts) ∧ piece.code = app ``HybridWord.Cmd.assign [r,a.code] := by
  obtain ⟨artifact,checked,proofTyped,_,_⟩ := Return.assign_finish inputs .some register (value.inProofCasts embeds) registered coverage exposure
  obtain ⟨rc,translated,rcSame⟩ := register.represented.property.translate_complete
  let registerCode : ClosedTerm := ⟨r,register.closed,rc⟩
  let code := ClosedTerm.app ``HybridWord.Cmd.assign [registerCode,a.closedTerm]
  let result : Piece env ctx p (app ``HybridWord.State.set [p.s,r,v]) Mode.value.expected :=
    ⟨code.val,artifact,code.closed,code.represented⟩
  have setRep := app_represents (f := Lean.Expr.const ``HybridWord.State.set []) (.constant rfl)
    (.cons inputs.s.property (.cons register.represented.property (.cons value.sourceCore.property .nil)))
  refine ⟨result,?_,⟨⟨⟨_,setRep⟩,?_,?_,proofTyped⟩⟩,rfl⟩
  · have same := sameTerm_complete inputs.s.property inputs.s.property
    have different : sameTerm (app ``HybridWord.State.set [p.s,r,v]) p.s = false := by
      cases found : sameTerm (app ``HybridWord.State.set [p.s,r,v]) p.s with
      | false => rfl
      | true =>
        have sizes := congrArg sizeOf (sameTerm_sound setRep inputs.s.property found)
        simp [applications] at sizes
        omega
    have mode : (Mode.value == Mode.value) = true := rfl
    have args : (app ``HybridWord.State.set [p.s,r,v]).getAppArgs.toList = [p.s,r,v] := rfl
    rw [visit]
    simp only [node,mode,Substitution.apply,↓reduceIte,different,Bool.false_eq_true]
    simp [same,args,parsed,closedTerm,register.closed,translated,
      finishBody,Mode.expected,ClosedTerm.app,ClosedTerm.const,Piece.closedTerm,registerCode,code,result,
      Return.Form.source,Return.Form.assignFact,Return.Form.nativeHeader,app,Lean.Expr.getAppFn,Lean.Expr.constName?] at checked ⊢
    simp only [app,List.foldl_cons,List.foldl_nil] at args
    simp only [args,same,Bool.true_eq_false,ite_false]
    simpa [parsed,closedTerm,register.closed,translated,finishBody,Mode.expected,
      ClosedTerm.app,Piece.closedTerm,registerCode,code,result,app] using checked
  · have h : CastTyping env 0 casts ctx (.const ``HybridWord.State.set []) Return.setterSignature :=
      .constant setter (by simp) rfl
    have a1 := CastTyping.application h (inputs.hs.withCasts casts)
    simp only [Return.setterSignature,stateType,wordType,VExpr.inst] at a1
    have a2 := CastTyping.application a1 (register.typed.withCasts casts)
    simp only [VExpr.inst] at a2
    exact .checkedApplication a2 value.value
  · have h : CastTyping env 0 casts ctx (.const ``HybridWord.Cmd.assign []) Return.assignConstructor :=
      .constant constructor (by simp) rfl
    have a1 := CastTyping.application h (register.typed.withCasts casts)
    simp only [Return.assignConstructor,cmdType,exprType,VExpr.inst] at a1
    change CastTyping env 0 casts ctx
      (applications (.const ``HybridWord.Cmd.assign []) [rc.val,a.represented.val]) cmdType
    rw [rcSame]
    exact .application a1 value.target

theorem value_assign_split_complete (inputs : InputsTyped env ctx p)
    (register : NatArgument env ctx r) {a : Piece env ctx p v scalarExpected}
    (value : ScalarCasts inputs a casts proofCasts)
    (registered : env.constants ``WordFrontendFacts.assign = some ⟨0,assignSignatureWith Return.Form.some.header⟩)
    (constructor : env.constants ``HybridWord.Cmd.assign = some ⟨0,Return.assignConstructor⟩)
    (setter : env.constants ``HybridWord.State.set = some ⟨0,Return.setterSignature⟩)
    (embeds : ∀ scope a b, casts scope a b → proofCasts scope a b)
    (coverage : Conversion.Covers conv 0 proofCasts) (exposure : Exposure env)
    (parsed : ScalarEnvironment.parse env conv exposure ctx p v = some a) :
    ∃ piece, visit env conv exposure (app ``HybridWord.State.set [p.s,r,v]) ctx p .value .identity (fun _ => none) = some piece ∧
      Nonempty (ValueCasts inputs piece casts proofCasts) := by
  obtain ⟨piece,success,typed,_⟩ := value_assign_split_complete_code inputs register value registered constructor setter embeds coverage exposure parsed
  exact ⟨piece,success,typed⟩

theorem value_assign_complete (inputs : InputsTyped env ctx p)
    (register : NatArgument env ctx r) {a : Piece env ctx p v scalarExpected}
    (value : ScalarCasts inputs a casts)
    (registered : env.constants ``WordFrontendFacts.assign = some ⟨0,assignSignatureWith Return.Form.some.header⟩)
    (constructor : env.constants ``HybridWord.Cmd.assign = some ⟨0,Return.assignConstructor⟩)
    (setter : env.constants ``HybridWord.State.set = some ⟨0,Return.setterSignature⟩)
    (coverage : Conversion.Covers conv 0 casts) (exposure : Exposure env)
    (parsed : ScalarEnvironment.parse env conv exposure ctx p v = some a) :
    ∃ piece, visit env conv exposure (app ``HybridWord.State.set [p.s,r,v]) ctx p .value .identity (fun _ => none) = some piece ∧
      Nonempty (ValueCasts inputs piece casts) := by
  exact value_assign_split_complete inputs register value registered constructor setter
    (fun _ _ _ h => h) coverage exposure parsed

structure StepCasts (inputs : InputsTyped env ctx p)
    (piece : Piece env ctx p source Mode.step.expected) (casts : TypeCasts)
    (proofCasts : TypeCasts := casts) where
  sourceCore : {core // Represents source core}
  value : CastTyping env 0 casts ctx sourceCore.val (optionType Step.stepState)
  target : CastTyping env 0 casts ctx piece.represented.val cmdType
  proof : CastTyping env 0 proofCasts ctx piece.checked.proofCore.val piece.checked.core.val

def StepCasts.inProofCasts {piece : Piece env ctx p source Mode.step.expected}
    (typed : StepCasts inputs piece casts proofCasts)
    (embeds : ∀ scope a b, casts scope a b → proofCasts scope a b) :
    StepCasts inputs piece proofCasts :=
  ⟨typed.sourceCore,typed.value.mono embeds,typed.target.mono embeds,typed.proof⟩

theorem StepCasts.equality {piece : Piece env ctx p source Mode.step.expected}
    (typed : StepCasts inputs piece casts proofCasts) :
    CastTyping env 0 proofCasts ctx piece.checked.proofCore.val
      (Step.expected
        (bodyValue inputs.i.val inputs.x.val inputs.y.val piece.represented.val inputs.s.val inputs.ls.val)
        typed.sourceCore.val) := by
  exact piece.checked.core.property.unique
    (Step.expected_represents (evalCmd_represents inputs piece.represented.property) typed.sourceCore.property) ▸ typed.proof

theorem yield_certificate (inputs : InputsTyped env ctx p)
    (signatures : Step.Signatures env)
    (evalDeclared : env.constants ``HybridWord.Cmd.eval = some ⟨0,evalSignature⟩)
    (composeDeclared : env.constants ``WordLoopFacts.compose = some ⟨0,For.composeSignature⟩)
    (embeds : ∀ scope a b, casts scope a b → proofCasts scope a b)
    {a : Piece env ctx p v Mode.value.expected} (typed : ValueCasts inputs a casts proofCasts)
    (coverage : Conversion.Covers conv 0 proofCasts) (exposure : Exposure env)
 :
    ∃ artifact, finish env conv exposure ctx
      (stepExpected (evalCmd p a.code) (Step.yieldSource v)) a.code
      (app ``WordLoopFacts.compose [evalCmd p a.code,someExpr state v,Step.yieldSource v,
        a.checked.proof,app ``WordLoopFacts.someYield [v]]) a.checked.known = some artifact ∧
      CastTyping env 0 proofCasts ctx artifact.proofCore.val artifact.core.val := by
  let ordinary := typed.asBody signatures.toSignatures
  have evaluation := eval_cast_typed inputs evalDeclared typed.target
  have source := Step.yield_typed signatures typed.value
  have equation := For.compose_typed (evaluation.mono embeds) (ordinary.value.mono embeds)
    (source.mono embeds) ordinary.equality
    (Step.yield_fact_typed signatures (typed.value.mono embeds)) composeDeclared
  have valueRep := typed.sourceCore.property
  have codeRep := a.represented.property
  have someRep : Represents (someExpr state v) (someValue stateType typed.sourceCore.val) :=
    .app (.app (.constant rfl) (.constant rfl)) valueRep
  have proofRep := app_represents (Represents.constant (name := ``WordLoopFacts.compose) (us := []) rfl)
    (.cons (evalCmd_represents inputs codeRep) (.cons someRep (.cons (Step.yield_represents valueRep)
      (.cons a.checked.proofCore.property (.cons (Represents.app (Represents.constant (name := ``WordLoopFacts.someYield) (us := []) rfl) valueRep) .nil)))))
  obtain ⟨artifact,checked,proofTyped,_,_⟩ := finish_cast_complete
    (Step.expected_represents (evalCmd_represents inputs codeRep) (Step.yield_represents valueRep))
    proofRep equation (known_casts a.checked typed.proof) coverage exposure a.code
  exact ⟨artifact,checked,proofTyped⟩

theorem yield_complete_code (inputs : InputsTyped env ctx p)
    (signatures : Step.Signatures env)
    (evalDeclared : env.constants ``HybridWord.Cmd.eval = some ⟨0,evalSignature⟩)
    (composeDeclared : env.constants ``WordLoopFacts.compose = some ⟨0,For.composeSignature⟩)
    (embeds : ∀ scope a b, casts scope a b → proofCasts scope a b)
    {a : Piece env ctx p v Mode.value.expected} (typed : ValueCasts inputs a casts proofCasts)
    (coverage : Conversion.Covers conv 0 proofCasts) (exposure : Exposure env)
    (parsed : visit env conv exposure v ctx p .value .identity (fun _ => none) = some a) :
    ∃ piece, visit env conv exposure (Step.yieldSource v) ctx p .step .identity (fun _ => none) = some piece ∧
      Nonempty (StepCasts inputs piece casts proofCasts) ∧ piece.code = a.code := by
  obtain ⟨artifact,checked,proofTyped⟩ := yield_certificate inputs signatures evalDeclared composeDeclared
    embeds typed coverage exposure
  have valueRep := typed.sourceCore.property
  have source := Step.yield_typed signatures typed.value
  let piece : Piece env ctx p (Step.yieldSource v) Mode.step.expected :=
    ⟨a.code,artifact,a.closed,a.represented⟩
  refine ⟨piece,?_,⟨⟨⟨_,Step.yield_represents valueRep⟩,source,typed.target,proofTyped⟩⟩,rfl⟩
  have modeValue : (Mode.step == Mode.value) = false := rfl
  have modeStep : (Mode.step == Mode.step) = true := rfl
  rw [visit]
  simp [node,modeValue,modeStep,letParts,applicationHead,makeContinuation,continuationParts,lambdaChain,
    ScalarEnvironment.arguments,ScalarEnvironment.below,Substitution.apply,
    Step.yieldSource,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,Lean.mkAppB,Lean.mkApp,
    Lean.Expr.getAppFn,Lean.Expr.constName?,List.map_cons,List.map_nil,
    finishBody,Mode.expected,parsed,piece] at checked ⊢
  try simp only [List.map_append,List.map_cons,List.map_nil,List.nil_append,List.cons_append,
    List.getLast?_cons_cons,List.getLast?_singleton,Option.unattach_some,Option.bind_some]
  simp [arguments,ScalarEnvironment.arguments,ScalarEnvironment.below,parsed,finishBody,
    Mode.expected,Piece.closedTerm,piece,app,Step.yieldSource,Lean.mkApp4,Lean.mkApp3,
    Lean.mkApp2,Lean.mkAppB,Lean.mkApp] at checked ⊢
  refine ⟨v,⟨?_,rfl⟩,a,parsed,artifact,checked,rfl,HEq.rfl,HEq.rfl⟩
  simp [syntaxSize]
  omega

theorem yield_complete (inputs : InputsTyped env ctx p)
    (signatures : Step.Signatures env)
    (evalDeclared : env.constants ``HybridWord.Cmd.eval = some ⟨0,evalSignature⟩)
    (composeDeclared : env.constants ``WordLoopFacts.compose = some ⟨0,For.composeSignature⟩)
    (embeds : ∀ scope a b, casts scope a b → proofCasts scope a b)
    {a : Piece env ctx p v Mode.value.expected} (typed : ValueCasts inputs a casts proofCasts)
    (coverage : Conversion.Covers conv 0 proofCasts) (exposure : Exposure env)
    (parsed : visit env conv exposure v ctx p .value .identity (fun _ => none) = some a) :
    ∃ piece, visit env conv exposure (Step.yieldSource v) ctx p .step .identity (fun _ => none) = some piece ∧
      Nonempty (StepCasts inputs piece casts proofCasts) := by
  obtain ⟨piece,success,typed,_⟩ := yield_complete_code inputs signatures evalDeclared composeDeclared embeds typed coverage exposure parsed
  exact ⟨piece,success,typed⟩

theorem next_typed (inputs : InputsTyped env ctx p)
    (closed : ClosedConstantTypes env) (stable : ClosedCasts casts)
    (wordDeclared : env.constants ``HybridWord.Word = some ⟨0,.sort (.succ .zero)⟩)
    (stateDeclared : env.constants ``HybridWord.State = some ⟨0,.sort (.succ .zero)⟩)
    (consDeclared : env.constants ``List.cons = some consSignature)
    {b : Piece env (stateType::wordType::ctx) (For.parameters p) original Mode.step.expected}
    (typed : StepCasts (For.nextInputs inputs closed wordDeclared consDeclared) b casts proofCasts) :
    CastTyping env 0 casts ctx b.represented.val cmdType ∧
    CastTyping env 0 casts ctx (.lam wordType (.lam stateType typed.sourceCore.val)) For.functionType ∧
    CastTyping env 0 proofCasts ctx (.lam wordType (.lam stateType b.checked.proofCore.val))
      (For.actualPremise inputs b.represented.val typed.sourceCore.val) := by
  have targetClosed := b.represented.property.closed 0 b.closed
  have wordTyped : DirectTyping env 0 ctx wordType (.sort (.succ .zero)) := .constant wordDeclared (by simp) rfl
  have stateTyped : DirectTyping env 0 (wordType::ctx) stateType (.sort (.succ .zero)) := .constant stateDeclared (by simp) rfl
  refine ⟨typed.target.closed_context stable targetClosed ctx,
    .lambda (wordTyped.withCasts casts) (.lambda (stateTyped.withCasts casts) typed.value),?_⟩
  have abstracted := CastTyping.lambda (wordTyped.withCasts proofCasts)
    (CastTyping.lambda (stateTyped.withCasts proofCasts) typed.equality)
  simpa only [For.actualPremise,For.nextInputs,InputsTyped.nextState,InputsTyped.nextWord,InputsTyped.lift,
    VExpr.lift,VExpr.liftN,applications,wordType,stateType] using abstracted

theorem finish_complete (inputs : InputsTyped env ctx p)
    (closed : ClosedConstantTypes env) (stable : ClosedCasts casts)
    (embeds : ∀ scope a b, casts scope a b → proofCasts scope a b)
    (startBound : For.Bound env ctx start) (stopBound : For.Bound env ctx stop) (strideBound : For.Bound env ctx stride)
    (wordDeclared : env.constants ``HybridWord.Word = some ⟨0,.sort (.succ .zero)⟩)
    (stateDeclared : env.constants ``HybridWord.State = some ⟨0,.sort (.succ .zero)⟩)
    (consDeclared : env.constants ``List.cons = some consSignature)
    {b : Piece env (stateType::wordType::ctx) (For.parameters p) original Mode.step.expected}
    (typed : StepCasts (For.nextInputs inputs closed wordDeclared consDeclared) b casts proofCasts)
    (beta : proofCasts ctx (For.actualPremise inputs b.represented.val typed.sourceCore.val)
      (For.continuationType inputs b.represented.val (.lam wordType (.lam stateType typed.sourceCore.val))))
    (registered : env.constants ``WordLoopFacts.forStatic = some ⟨0,For.signature⟩)
    (coverage : Conversion.Covers conv 0 proofCasts) (exposure : Exposure env)
    (kn tn : Lean.Name) (ki ti : Lean.BinderInfo) :
    ∃ result, finish env conv exposure ctx
      (bodyExpected p (app ``HybridWord.Cmd.forStatic [start,stop,stride,b.code])
        (For.source start stop stride p.s (.lam kn word (.lam tn state original ti) ki)))
      (app ``HybridWord.Cmd.forStatic [start,stop,stride,b.code])
      (app ``WordLoopFacts.forStatic ([start,stop,stride,b.code] ++ p.args ++
        [.lam kn word (.lam tn state original ti) ki,
          .lam kn word (.lam tn state b.checked.proof ti) ki]))
      b.checked.known = some result ∧
      CastTyping env 0 proofCasts ctx result.proofCore.val result.core.val := by
  obtain ⟨target,next,proofTyped⟩ := next_typed inputs closed stable wordDeclared stateDeclared consDeclared typed
  have fact := For.fact_typed inputs (startBound.typed.mono Arithmetic.Includes.embed) (stopBound.typed.mono Arithmetic.Includes.embed)
    (strideBound.typed.mono Arithmetic.Includes.embed) (target.mono embeds) (next.mono embeds) proofTyped beta registered
  have codeArgs := List.Forall₂.cons startBound.represented.property (.cons stopBound.represented.property
    (.cons strideBound.represented.property (.cons b.represented.property .nil)))
  have fnRep : Represents (.lam kn word (.lam tn state original ti) ki)
      (.lam wordType (.lam stateType typed.sourceCore.val)) :=
    .lam (.constant rfl) (.lam (.constant rfl) typed.sourceCore.property)
  have proofLambdaRep : Represents (.lam kn word (.lam tn state b.checked.proof ti) ki)
      (.lam wordType (.lam stateType b.checked.proofCore.val)) :=
    .lam (.constant rfl) (.lam (.constant rfl) b.checked.proofCore.property)
  have certificateRep := app_represents (Represents.constant (name := ``WordLoopFacts.forStatic) (us := []) rfl)
    (.cons startBound.represented.property (.cons stopBound.represented.property
      (.cons strideBound.represented.property (.cons b.represented.property
        (.cons inputs.i.property (.cons inputs.x.property (.cons inputs.y.property
          (.cons inputs.s.property (.cons inputs.ls.property (.cons fnRep
            (.cons proofLambdaRep .nil)))))))))))
  obtain ⟨result,checked,proofTyped,_,_⟩ := finish_cast_complete
    (bodyExpected_represents inputs (app_represents (Represents.constant (name := ``HybridWord.Cmd.forStatic) (us := []) rfl) codeArgs)
      (For.source_represents startBound.represented.property stopBound.represented.property
        strideBound.represented.property inputs.s.property fnRep)) certificateRep fact
    (known_casts b.checked typed.proof) coverage exposure (app ``HybridWord.Cmd.forStatic [start,stop,stride,b.code])
  exact ⟨result,checked,proofTyped⟩


theorem substitute_forStatic (σ : Substitution) :
    σ.apply (For.source start stop stride st (.lam kn word (.lam tn state original ti) ki)) =
      For.source (σ.apply start) (σ.apply stop) (σ.apply stride) (σ.apply st)
        (.lam kn word (.lam tn state ((under (under σ)).apply original) ti) ki) := by
  cases σ <;> rfl

open Certificate.For in
theorem mapped_forStatic_complete_code (inputs : InputsTyped env ctx p)
    (closed : ClosedConstantTypes env) (stable : ClosedCasts casts)
    (embeds : ∀ scope a b, casts scope a b → proofCasts scope a b)
    (startBound : Bound env ctx (σ.apply start)) (stopBound : Bound env ctx (σ.apply stop)) (strideBound : Bound env ctx (σ.apply stride))
    (wordDeclared : env.constants ``HybridWord.Word = some ⟨0,.sort (.succ .zero)⟩)
    (stateDeclared : env.constants ``HybridWord.State = some ⟨0,.sort (.succ .zero)⟩)
    (consDeclared : env.constants ``List.cons = some consSignature)
    {b : Piece env (stateType::wordType::ctx) (For.parameters p) ((under (under σ)).apply original) Mode.step.expected}
    (bodyTyped : StructuralLoop.StepCasts (For.nextInputs inputs closed wordDeclared consDeclared) b casts proofCasts)
    (beta : proofCasts ctx (actualPremise inputs b.represented.val bodyTyped.sourceCore.val)
      (continuationType inputs b.represented.val (.lam wordType (.lam stateType bodyTyped.sourceCore.val))))
    (registered : env.constants ``WordLoopFacts.forStatic = some ⟨0,signature⟩)
    (constructor : env.constants ``HybridWord.Cmd.forStatic = some ⟨0,constructorSignature⟩)
    (rangeDeclared : env.constants ``HybridWord.range = some ⟨0,rangeSignature⟩)
    (headerTyped : CastTyping env 0 casts ctx header headerType)
    (coverage : Conversion.Covers conv 0 proofCasts) (exposure : Exposure env)
    (kn tn : Lean.Name) (ki ti : Lean.BinderInfo)
    (current : σ.apply st = p.s)
    (bodyParsed : StructuralBody.visit env conv exposure original (stateType::wordType::ctx)
      (For.parameters p) .step (under (under σ)) (underFunctions (underFunctions fs)) = some b) :
    ∃ piece, StructuralBody.visit env conv exposure
      (source start stop stride st (.lam kn word (.lam tn state original ti) ki)) ctx p .body σ fs = some piece ∧
      Nonempty (BodyCasts inputs piece casts proofCasts) ∧
      piece.code = app ``HybridWord.Cmd.forStatic [σ.apply start,σ.apply stop,σ.apply stride,b.code] := by
  have assembled := StructuralLoop.finish_complete inputs closed stable embeds
    startBound stopBound strideBound wordDeclared stateDeclared consDeclared
    bodyTyped beta registered coverage exposure kn tn ki ti
  have sourceSame := substitute_forStatic (start := start) (stop := stop) (stride := stride)
    (st := st) (original := original) (kn := kn) (tn := tn) (ki := ki) (ti := ti) σ
  rw [current] at sourceSame
  rw [← sourceSame] at assembled
  obtain ⟨artifact,checked,typed⟩ := assembled
  let code := ClosedTerm.app ``HybridWord.Cmd.forStatic [startBound.term,stopBound.term,strideBound.term,b.closedTerm]
  let piece : Piece env ctx p (σ.apply (source start stop stride st (.lam kn word (.lam tn state original ti) ki))) bodyExpected :=
    ⟨code.val,artifact,code.closed,code.represented⟩
  obtain ⟨target,next,_⟩ := StructuralLoop.next_typed inputs closed stable wordDeclared stateDeclared consDeclared bodyTyped
  have represented : Represents (σ.apply (source start stop stride st (.lam kn word (.lam tn state original ti) ki)))
      (applications header [applications (.const ``HybridWord.range []) [startBound.represented.val,stopBound.represented.val,strideBound.represented.val],
        inputs.s.val,.lam wordType (.lam stateType bodyTyped.sourceCore.val)]) := by
    rw [sourceSame]
    exact source_represents startBound.represented.property stopBound.represented.property
      strideBound.represented.property inputs.s.property
      (.lam (.constant rfl) (.lam (.constant rfl) bodyTyped.sourceCore.property))
  refine ⟨piece,?_,⟨⟨⟨_,represented⟩,
    source_typed headerTyped rangeDeclared (startBound.typed.mono Arithmetic.Includes.embed) (stopBound.typed.mono Arithmetic.Includes.embed)
      (strideBound.typed.mono Arithmetic.Includes.embed) (inputs.hs.withCasts casts) next,?_,typed⟩⟩,rfl⟩
  · have stateSame := sameTerm_complete (a := state) (b := state) (Represents.constant rfl) (Represents.constant rfl)
    have wordSame := sameTerm_complete (a := word) (b := word) (Represents.constant rfl) (Represents.constant rfl)
    have same := sameTerm_complete inputs.s.property inputs.s.property
    have stateCompatible : compatible env conv ctx state state = true := by simp only [compatible,stateSame]; rfl
    have wordCompatible : compatible env conv ctx word word = true := by simp only [compatible,wordSame]; rfl
    have stateTranslated : translate state = some ⟨stateType,Represents.constant rfl⟩ := rfl
    have wordTranslated : translate word = some ⟨wordType,Represents.constant rfl⟩ := rfl
    have bodyValue : (Mode.body == Mode.value) = false := rfl
    have bodyBody : (Mode.body != Mode.body) = false := rfl
    have stateApply : σ.apply state = state := by cases σ <;> rfl
    have wordApply : σ.apply word = word := by cases σ <;> rfl
    have translatedState : (translate (σ.apply state)).unattach = some stateType := by rw [stateApply]; rfl
    have translatedWord : (translate (σ.apply word)).unattach = some wordType := by rw [wordApply]; rfl
    have rangeArgs : ((((Lean.Expr.const ``HybridWord.range []).app start).app stop).app stride).getAppArgs.toList = [start,stop,stride] := rfl
    have lambdaSame : σ.apply (.lam kn word (.lam tn state original ti) ki) =
        .lam kn word (.lam tn state ((under (under σ)).apply original) ti) ki := by cases σ <;> rfl
    rw [StructuralBody.visit]
    simp [-heq_eq_eq,StructuralBody.node,bodyValue,bodyBody,letParts,applicationHead,makeContinuation,continuationParts,lambdaChain,
      ScalarEnvironment.arguments,ScalarEnvironment.below,lambdaParts,
      source,Lean.mkApp3,Lean.mkAppB,Lean.Expr.getAppFn,Lean.Expr.constName?,nativeHeader,Lean.mkApp5,Lean.mkApp4,Lean.mkApp,
      Lean.mkAppN,List.map_cons,List.map_nil]
    simp only [List.map_append,List.map_cons,List.map_nil,List.nil_append,List.cons_append,
      Function.comp_apply,List.length_cons,List.length_nil,Nat.reduceAdd,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.unattach_some,
      current,same,stateApply,wordApply,stateCompatible,wordCompatible,stateTranslated,wordTranslated,
      translatedState,translatedWord,startBound.closedTerm_complete,stopBound.closedTerm_complete,strideBound.closedTerm_complete,
      Bool.and_self,Bool.not_true,Bool.or_self,Option.bind_some]
    simp only [For.parameters] at bodyParsed
    dsimp only [GetElem?.getElem?]
    simp [-heq_eq_eq,Lean.Expr.getAppFn,Lean.Expr.constName?,current,same,rangeArgs,
      startBound.closedTerm_complete,stopBound.closedTerm_complete,strideBound.closedTerm_complete,
      translatedState,translatedWord,stateApply,wordApply,stateCompatible,wordCompatible,
      bodyParsed,StructuralBody.finishBody,code,piece,ClosedTerm.app,Bound.term,Piece.closedTerm,
      app,Mode.expected,source,Lean.mkApp3,Lean.mkAppB,Lean.mkApp,lambdaSame] at checked ⊢
    try simp only [List.getElem?_cons,Nat.reduceEqDiff,ite_false,ite_true,Nat.reduceSub,
      List.getElem?_cons_zero,Option.unattach_some,Option.bind_some,current,same,
      Lean.Expr.getAppFn,Lean.Expr.constName?]
    try simp [-heq_eq_eq,rangeArgs,startBound.closedTerm_complete,stopBound.closedTerm_complete,
      strideBound.closedTerm_complete,Bound.term,checked]
    refine ⟨app ``HybridWord.range [start,stop,stride],rfl,st,⟨by simp [syntaxSize]; omega,rfl⟩,?_⟩
    simp [-heq_eq_eq,current,same,app,Lean.Expr.getAppFn,Lean.Expr.constName?,rangeArgs,
      startBound.closedTerm_complete,stopBound.closedTerm_complete,strideBound.closedTerm_complete,
      Bound.term] at checked ⊢
    exact ⟨artifact,checked,rfl⟩
  · have h : CastTyping env 0 casts ctx (.const ``HybridWord.Cmd.forStatic []) constructorSignature :=
      .constant constructor (by simp) rfl
    have a1 := CastTyping.application h (startBound.typed.mono Arithmetic.Includes.embed)
    simp only [constructorSignature,For.intType,cmdType,VExpr.inst] at a1
    have a2 := CastTyping.application a1 (stopBound.typed.mono Arithmetic.Includes.embed)
    simp only [VExpr.inst] at a2
    have a3 := CastTyping.application a2 (strideBound.typed.mono Arithmetic.Includes.embed)
    simp only [VExpr.inst] at a3
    exact .application a3 target

open Certificate.For in
theorem body_forStatic_complete_code (inputs : InputsTyped env ctx p)
    (closed : ClosedConstantTypes env) (stable : ClosedCasts casts)
    (embeds : ∀ scope a b, casts scope a b → proofCasts scope a b)
    (startBound : Bound env ctx start) (stopBound : Bound env ctx stop) (strideBound : Bound env ctx stride)
    (wordDeclared : env.constants ``HybridWord.Word = some ⟨0,.sort (.succ .zero)⟩)
    (stateDeclared : env.constants ``HybridWord.State = some ⟨0,.sort (.succ .zero)⟩)
    (consDeclared : env.constants ``List.cons = some consSignature)
    {b : Piece env (stateType::wordType::ctx) (For.parameters p) original Mode.step.expected}
    (bodyTyped : StepCasts (For.nextInputs inputs closed wordDeclared consDeclared) b casts proofCasts)
    (beta : proofCasts ctx (actualPremise inputs b.represented.val bodyTyped.sourceCore.val)
      (continuationType inputs b.represented.val (.lam wordType (.lam stateType bodyTyped.sourceCore.val))))
    (registered : env.constants ``WordLoopFacts.forStatic = some ⟨0,signature⟩)
    (constructor : env.constants ``HybridWord.Cmd.forStatic = some ⟨0,constructorSignature⟩)
    (rangeDeclared : env.constants ``HybridWord.range = some ⟨0,rangeSignature⟩)
    (headerTyped : CastTyping env 0 casts ctx header headerType)
    (coverage : Conversion.Covers conv 0 proofCasts) (exposure : Exposure env)
    (kn tn : Lean.Name) (ki ti : Lean.BinderInfo)
    (bodyParsed : StructuralBody.visit env conv exposure original (stateType::wordType::ctx)
      (For.parameters p) .step .identity (fun _ => none) = some b) :
    ∃ piece, StructuralBody.bodyRetained env conv exposure ctx p
      (source start stop stride p.s (.lam kn word (.lam tn state original ti) ki)) = some piece ∧
      Nonempty (BodyCasts inputs piece casts proofCasts) ∧
      piece.code = app ``HybridWord.Cmd.forStatic [start,stop,stride,b.code] := by
  have empty : underFunctions (fun _ => (none : Option (Continuation env))) = (fun _ => none) := by
    funext n; cases n <;> rfl
  have parsed : StructuralBody.visit env conv exposure original (stateType::wordType::ctx)
      (For.parameters p) .step (under (under .identity))
      (underFunctions (underFunctions (fun _ => none))) = some b := by
    simpa only [under,empty] using bodyParsed
  exact mapped_forStatic_complete_code (σ := .identity) (st := p.s) (start := start) (stop := stop) (stride := stride) inputs closed stable embeds
    startBound stopBound strideBound wordDeclared stateDeclared consDeclared bodyTyped beta
    registered constructor rangeDeclared headerTyped coverage exposure kn tn ki ti rfl parsed

open Certificate.For in
theorem body_forStatic_complete (inputs : InputsTyped env ctx p)
    (closed : ClosedConstantTypes env) (stable : ClosedCasts casts)
    (embeds : ∀ scope a b, casts scope a b → proofCasts scope a b)
    (startBound : Bound env ctx start) (stopBound : Bound env ctx stop) (strideBound : Bound env ctx stride)
    (wordDeclared : env.constants ``HybridWord.Word = some ⟨0,.sort (.succ .zero)⟩)
    (stateDeclared : env.constants ``HybridWord.State = some ⟨0,.sort (.succ .zero)⟩)
    (consDeclared : env.constants ``List.cons = some consSignature)
    {b : Piece env (stateType::wordType::ctx) (For.parameters p) original Mode.step.expected}
    (bodyTyped : StepCasts (For.nextInputs inputs closed wordDeclared consDeclared) b casts proofCasts)
    (beta : proofCasts ctx (actualPremise inputs b.represented.val bodyTyped.sourceCore.val)
      (continuationType inputs b.represented.val (.lam wordType (.lam stateType bodyTyped.sourceCore.val))))
    (registered : env.constants ``WordLoopFacts.forStatic = some ⟨0,signature⟩)
    (constructor : env.constants ``HybridWord.Cmd.forStatic = some ⟨0,constructorSignature⟩)
    (rangeDeclared : env.constants ``HybridWord.range = some ⟨0,rangeSignature⟩)
    (headerTyped : CastTyping env 0 casts ctx header headerType)
    (coverage : Conversion.Covers conv 0 proofCasts) (exposure : Exposure env)
    (kn tn : Lean.Name) (ki ti : Lean.BinderInfo)
    (bodyParsed : StructuralBody.visit env conv exposure original (stateType::wordType::ctx)
      (For.parameters p) .step .identity (fun _ => none) = some b) :
    ∃ piece, StructuralBody.bodyRetained env conv exposure ctx p
      (source start stop stride p.s (.lam kn word (.lam tn state original ti) ki)) = some piece ∧
      Nonempty (BodyCasts inputs piece casts proofCasts) := by
  obtain ⟨piece,success,typed,_⟩ := body_forStatic_complete_code inputs closed stable embeds startBound stopBound strideBound wordDeclared stateDeclared consDeclared bodyTyped beta registered constructor rangeDeclared headerTyped coverage exposure kn tn ki ti bodyParsed
  exact ⟨piece,success,typed⟩

end IRComparison.WordFrontend.StructuralLoop
