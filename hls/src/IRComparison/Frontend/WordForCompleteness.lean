import IRComparison.Frontend.WordStepConversion

/-! The existing signed-range `for` parser, composing arbitrary body and
normalization certificates. Bounds are compile-time terms, as in the agreed
input syntax; the proof does not unroll iterations. -/
namespace IRComparison.WordFrontend.Certificate.For
open Lean4Lean LeanTyped LeanTypeInference
variable {casts proofCasts : TypeCasts} [Arithmetic.Includes casts] [Arithmetic.Includes proofCasts]
set_option maxHeartbeats 1500000

def intType : VExpr := .const ``Int []
def functionType : VExpr := .forallE wordType (.forallE stateType (optionType Step.stepState))

def header : VExpr := applications (.const ``ForIn.forIn [.zero,.zero,.zero,.zero])
  [.const ``Option [.zero], wordsType, wordType,
    applications (.const ``instForInOfForIn' [.zero,.zero,.zero,.zero])
      [.const ``Option [.zero],wordsType,wordType,
        applications (.const ``inferInstance [.succ .zero])
          [applications (.const ``Membership [.zero,.zero]) [wordType,wordsType],
            .app (.const ``List.instMembership [.zero]) wordType],
        applications (.const ``List.instForIn'InferInstanceMembershipOfMonad [.zero,.zero,.zero])
          [.const ``Option [.zero],wordType,.const ``instMonadOption [.zero]]],stateType]

def nativeHeader : Lean.Expr := Lean.mkApp5 (.const ``ForIn.forIn [.zero,.zero,.zero,.zero])
  (.const ``Option [.zero]) (Lean.mkApp (.const ``List [.zero]) word) word
  (Lean.mkApp5 (.const ``instForInOfForIn' [.zero,.zero,.zero,.zero])
    (.const ``Option [.zero]) (Lean.mkApp (.const ``List [.zero]) word) word
    (Lean.mkApp2 (.const ``inferInstance [.succ .zero])
      (Lean.mkApp2 (.const ``Membership [.zero,.zero]) word (Lean.mkApp (.const ``List [.zero]) word))
      (Lean.mkApp (.const ``List.instMembership [.zero]) word))
    (Lean.mkApp3 (.const ``List.instForIn'InferInstanceMembershipOfMonad [.zero,.zero,.zero])
      (.const ``Option [.zero]) word (.const ``instMonadOption [.zero]))) state

theorem header_represents : Represents nativeHeader header := by
  repeat first | apply Represents.app | exact Represents.constant rfl

def range (start stop stride : VExpr) : VExpr :=
  applications (.const ``HybridWord.range []) [start,stop,stride]
def loop (start stop stride s fn : VExpr) : VExpr :=
  applications header [range start stop stride,s,fn]
def source (start stop stride s fn : Lean.Expr) : Lean.Expr :=
  Lean.mkApp3 nativeHeader (Lean.mkApp3 (.const ``HybridWord.range []) start stop stride) s fn

theorem app8_arguments (name : Lean.Name) (levels : List Lean.Level)
    (a b c d e f g h : Lean.Expr) :
    (Lean.mkApp3 (Lean.mkApp5 (.const name levels) a b c d e) f g h).getAppArgs.toList =
      [a,b,c,d,e,f,g,h] := by
  change (((((((((Array.replicate 8 (Lean.mkSort Lean.levelZero)).set! 7 h).set! 6 g).set! 5 f).set! 4 e).set! 3 d).set! 2 c).set! 1 b).set! 0 a).toList = _
  simp only [Array.set!_eq_setIfInBounds,Array.toList_setIfInBounds,Array.toList_replicate]
  rfl

theorem source_arguments (start stop stride s fn : Lean.Expr) :
    (source start stop stride s fn).getAppArgs.toList =
      [.const ``Option [.zero],Lean.mkApp (.const ``List [.zero]) word,word,
        nativeHeader.getAppArgs[3]!,state,
        Lean.mkApp3 (.const ``HybridWord.range []) start stop stride,s,fn] :=
  app8_arguments _ _ _ _ _ _ _ _ _ _

theorem source_represents (startRep : Represents start sc) (stopRep : Represents stop ec)
    (strideRep : Represents stride dc) (stateRep : Represents s tc) (functionRep : Represents fn fc) :
    Represents (source start stop stride s fn) (loop sc ec dc tc fc) :=
  .app (.app (.app header_represents (.app (.app (.app (.constant rfl) startRep) stopRep) strideRep)) stateRep) functionRep

def composeSignature : VExpr := .forallE (optionType stateType) (.forallE (optionType stateType)
  (.forallE (optionType Step.stepState)
    (.forallE (equalValues (optionType stateType) (.bvar 2) (.bvar 1))
      (.forallE (Step.expected (.bvar 2) (.bvar 1)) (Step.expected (.bvar 4) (.bvar 2))))))

def premise : VExpr := .forallE wordType (.forallE stateType
  (Step.expected
    (bodyValue (.bvar 7) (.bvar 6) (.bvar 5) (.bvar 8) (.bvar 0)
      (applications (.const ``List.cons [.zero]) [wordType,.bvar 1,.bvar 3]))
    (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))))
def resultType : VExpr := equalValues (optionType stateType)
  (bodyValue (.bvar 6) (.bvar 5) (.bvar 4)
    (applications (.const ``HybridWord.Cmd.forStatic []) [.bvar 10,.bvar 9,.bvar 8,.bvar 7])
    (.bvar 3) (.bvar 2))
  (loop (.bvar 10) (.bvar 9) (.bvar 8) (.bvar 3) (.bvar 1))
def signature : VExpr := .forallE intType (.forallE intType (.forallE intType
  (.forallE cmdType (inputsType (.forallE functionType (.forallE premise resultType))))))
def constructorSignature : VExpr := .forallE intType (.forallE intType (.forallE intType (.forallE cmdType cmdType)))
def rangeSignature : VExpr := .forallE intType (.forallE intType (.forallE intType wordsType))
def headerType : VExpr := .forallE wordsType (.forallE stateType (.forallE functionType (optionType stateType)))

theorem compose_typed
    (resultTyped : CastTyping env 0 casts ctx result (optionType stateType))
    (plainTyped : CastTyping env 0 casts ctx plain (optionType stateType))
    (originalTyped : CastTyping env 0 casts ctx original (optionType Step.stepState))
    (bodyProof : CastTyping env 0 casts ctx h (equalValues (optionType stateType) result plain))
    (stepProof : CastTyping env 0 casts ctx hn (Step.expected plain original))
    (registered : env.constants ``WordLoopFacts.compose = some ⟨0,composeSignature⟩) :
    CastTyping env 0 casts ctx
      (applications (.const ``WordLoopFacts.compose []) [result,plain,original,h,hn])
      (Step.expected result original) := by
  have fact : CastTyping env 0 casts ctx (.const ``WordLoopFacts.compose []) composeSignature :=
    .constant registered (by simp) rfl
  have a1 := CastTyping.application fact resultTyped
  simp only [composeSignature,Step.expected,Step.lifted,Step.stepState,optionType,stateType,
    equalValues,VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower,
    ← VExpr.lift_instN_lo,VExpr.inst_lift,Nat.reduceAdd] at a1
  have a2 := CastTyping.application a1 plainTyped
  simp only [VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower,
    ← VExpr.lift_instN_lo,VExpr.inst_lift,Nat.reduceAdd] at a2
  have a3 := CastTyping.application a2 originalTyped
  simp only [VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower,
    ← VExpr.lift_instN_lo,VExpr.inst_lift,Nat.reduceAdd] at a3
  have a4 := CastTyping.application a3 bodyProof
  simp only [VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower,
    ← VExpr.lift_instN_lo,VExpr.inst_lift,Nat.reduceAdd] at a4
  simpa only [Step.expected,Step.lifted,Step.stepState,optionType,stateType,equalValues,
    VExpr.inst,VExpr.inst_lift] using CastTyping.application a4 stepProof

def continuationType (inputs : InputsTyped env ctx p) (code fn : VExpr) : VExpr :=
  .forallE wordType (.forallE stateType (Step.expected
    (bodyValue inputs.i.val.lift.lift inputs.x.val.lift.lift inputs.y.val.lift.lift
      code.lift.lift (.bvar 0)
      (applications (.const ``List.cons [.zero]) [wordType,.bvar 1,inputs.ls.val.lift.lift]))
    (.app (.app fn.lift.lift (.bvar 1)) (.bvar 0))))

theorem fact_typed (inputs : InputsTyped env ctx p)
    (startTyped : CastTyping env 0 casts ctx start intType)
    (stopTyped : CastTyping env 0 casts ctx stop intType)
    (strideTyped : CastTyping env 0 casts ctx stride intType)
    (targetTyped : CastTyping env 0 casts ctx code cmdType)
    (functionTyped : CastTyping env 0 casts ctx fn functionType)
    (proofTyped : CastTyping env 0 casts ctx proof actual)
    (beta : casts ctx actual (continuationType inputs code fn))
    (registered : env.constants ``WordLoopFacts.forStatic = some ⟨0,signature⟩) :
    CastTyping env 0 casts ctx
      (applications (.const ``WordLoopFacts.forStatic []) ([start,stop,stride,code] ++ inputs.args ++ [fn,proof]))
      (equalValues (optionType stateType)
        (bodyValue inputs.i.val inputs.x.val inputs.y.val
          (applications (.const ``HybridWord.Cmd.forStatic []) [start,stop,stride,code]) inputs.s.val inputs.ls.val)
        (loop start stop stride inputs.s.val fn)) := by
  have fact : CastTyping env 0 casts ctx (.const ``WordLoopFacts.forStatic []) signature :=
    .constant registered (by simp) rfl
  have a1 := CastTyping.application fact startTyped
  simp only [signature,intType,inputsType,cmdType,wordType,stateType,wordsType,optionType,Step.stepState,functionType,VExpr.inst] at a1
  have a2 := CastTyping.application a1 stopTyped
  simp only [VExpr.inst] at a2
  have a3 := CastTyping.application a2 strideTyped
  simp only [VExpr.inst] at a3
  have a4 := CastTyping.application a3 targetTyped
  simp only [VExpr.inst] at a4
  have a5 := inputs.apply_casts a4
  simp only [InputsTyped.instantiate,premise,resultType,loop,range,Step.expected,Step.lifted,
    bodyValue,equalValues,optionType,stateType,wordType,wordsType,Step.stepState,applications,
    VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower,Nat.reduceAdd,
    ← VExpr.lift_instN_lo,VExpr.inst_lift] at a5
  have a6 := CastTyping.application a5 functionTyped
  simp only [VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower,Nat.reduceAdd,
    ← VExpr.lift_instN_lo,VExpr.inst_lift] at a6
  have cast := beta
  simp only [continuationType,Step.expected,Step.lifted,Step.stepState,bodyValue,equalValues,
    optionType,stateType,wordType,applications] at cast
  simpa only [InputsTyped.args,applications,List.cons_append,List.nil_append,loop,range,
    Step.expected,Step.lifted,Step.stepState,bodyValue,equalValues,optionType,stateType,wordType,
    VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower,Nat.reduceAdd,
    ← VExpr.lift_instN_lo,VExpr.inst_lift] using CastTyping.convertedApplication a6 proofTyped cast

def parameters (p : Inputs) : Inputs :=
  {p.lift.lift with s := .bvar 0,locals := .bvar 1::p.lift.lift.locals}

def nextInputs (inputs : InputsTyped env ctx p) (closed : ClosedConstantTypes env)
    (wordDeclared : env.constants ``HybridWord.Word = some ⟨0,.sort (.succ .zero)⟩)
    (consDeclared : env.constants ``List.cons = some consSignature) :
    InputsTyped env (stateType::wordType::ctx) (parameters p) :=
  (inputs.nextWord closed wordDeclared consDeclared).nextState closed

def actualPremise (inputs : InputsTyped env ctx p) (code original : VExpr) : VExpr :=
  .forallE wordType (.forallE stateType (Step.expected
    (bodyValue inputs.i.val.lift.lift inputs.x.val.lift.lift inputs.y.val.lift.lift
      code (.bvar 0)
      (applications (.const ``List.cons [.zero]) [wordType,.bvar 1,inputs.ls.val.lift.lift])) original))

def composition (p : Inputs) (code plain original bodyProof stepProof : Lean.Expr) : Lean.Expr :=
  app ``WordLoopFacts.compose [evalCmd (parameters p) code,plain,original,bodyProof,stepProof]

theorem next_typed (inputs : InputsTyped env ctx p)
    (closed : ClosedConstantTypes env) (stable : ClosedCasts casts)
    (embeds : ∀ scope a b, casts scope a b → proofCasts scope a b)
    (wordDeclared : env.constants ``HybridWord.Word = some ⟨0,.sort (.succ .zero)⟩)
    (stateDeclared : env.constants ``HybridWord.State = some ⟨0,.sort (.succ .zero)⟩)
    (consDeclared : env.constants ``List.cons = some consSignature)
    (evalDeclared : env.constants ``HybridWord.Cmd.eval = some ⟨0,evalSignature⟩)
    (composeDeclared : env.constants ``WordLoopFacts.compose = some ⟨0,composeSignature⟩)
    {normalized : StepPiece env (stateType::wordType::ctx) original}
    (stepTyped : Step.StepCasts normalized casts proofCasts)
    {b : Piece env (stateType::wordType::ctx) (parameters p) normalized.plain bodyExpected}
    (bodyTyped : BodyCasts (nextInputs inputs closed wordDeclared consDeclared) b casts proofCasts) :
    CastTyping env 0 casts ctx b.represented.val cmdType ∧
    CastTyping env 0 casts ctx (.lam wordType (.lam stateType stepTyped.sourceCore.val)) functionType ∧
    ∃ proof, Represents (composition p b.code normalized.plain original b.checked.proof normalized.checked.proof) proof ∧
      CastTyping env 0 proofCasts ctx (.lam wordType (.lam stateType proof))
        (actualPremise inputs b.represented.val stepTyped.sourceCore.val) := by
  have targetClosed : b.represented.val.ClosedN 0 := b.represented.property.closed 0 b.closed
  have wordTyped : DirectTyping env 0 ctx wordType (.sort (.succ .zero)) := .constant wordDeclared (by simp) rfl
  have stateTyped : DirectTyping env 0 (wordType::ctx) stateType (.sort (.succ .zero)) := .constant stateDeclared (by simp) rfl
  have evaluation := eval_cast_typed (nextInputs inputs closed wordDeclared consDeclared) evalDeclared bodyTyped.target
  have composed := compose_typed (evaluation.mono embeds) (stepTyped.plain.mono embeds)
    (stepTyped.source.mono embeds)
    (stepTyped.plainCore.property.unique bodyTyped.sourceCore.property ▸ bodyTyped.equality)
    stepTyped.equality composeDeclared
  have represented : Represents (composition p b.code normalized.plain original b.checked.proof normalized.checked.proof)
      (applications (.const ``WordLoopFacts.compose [])
        [bodyValue (nextInputs inputs closed wordDeclared consDeclared).i.val
          (nextInputs inputs closed wordDeclared consDeclared).x.val
          (nextInputs inputs closed wordDeclared consDeclared).y.val b.represented.val
          (nextInputs inputs closed wordDeclared consDeclared).s.val
          (nextInputs inputs closed wordDeclared consDeclared).ls.val,
        stepTyped.plainCore.val,stepTyped.sourceCore.val,b.checked.proofCore.val,normalized.checked.proofCore.val]) :=
    app_represents (.constant rfl) (.cons (evalCmd_represents (nextInputs inputs closed wordDeclared consDeclared) b.represented.property)
      (.cons stepTyped.plainCore.property (.cons stepTyped.sourceCore.property
        (.cons b.checked.proofCore.property (.cons normalized.checked.proofCore.property .nil)))))
  refine ⟨bodyTyped.target.closed_context stable targetClosed ctx,
    .lambda (wordTyped.withCasts casts) (.lambda (stateTyped.withCasts casts) stepTyped.source),
    _,represented,?_⟩
  have abstracted := CastTyping.lambda (wordTyped.withCasts proofCasts)
    (CastTyping.lambda (stateTyped.withCasts proofCasts) composed)
  simpa only [actualPremise,nextInputs,InputsTyped.nextState,InputsTyped.nextWord,InputsTyped.lift,
    VExpr.lift,VExpr.liftN,applications,wordType,stateType] using abstracted

structure Bound (env : VEnv) (ctx : List VExpr) (value : Lean.Expr) where
  represented : {core // Represents value core}
  typed : CastTyping env 0 Arithmetic.Casts ctx represented.val intType
  closed : isClosed value = true

def Bound.term (bound : Bound env ctx value) : ClosedTerm := ⟨value,bound.closed,bound.represented⟩

theorem finish_complete (inputs : InputsTyped env ctx p)
    (closed : ClosedConstantTypes env) (stable : ClosedCasts casts)
    (embeds : ∀ scope a b, casts scope a b → proofCasts scope a b)
    (startBound : Bound env ctx start) (stopBound : Bound env ctx stop) (strideBound : Bound env ctx stride)
    (wordDeclared : env.constants ``HybridWord.Word = some ⟨0,.sort (.succ .zero)⟩)
    (stateDeclared : env.constants ``HybridWord.State = some ⟨0,.sort (.succ .zero)⟩)
    (consDeclared : env.constants ``List.cons = some consSignature)
    (evalDeclared : env.constants ``HybridWord.Cmd.eval = some ⟨0,evalSignature⟩)
    (composeDeclared : env.constants ``WordLoopFacts.compose = some ⟨0,composeSignature⟩)
    {normalized : StepPiece env (stateType::wordType::ctx) original}
    (stepTyped : Step.StepCasts normalized casts proofCasts)
    {b : Piece env (stateType::wordType::ctx) (parameters p) normalized.plain bodyExpected}
    (bodyTyped : BodyCasts (nextInputs inputs closed wordDeclared consDeclared) b casts proofCasts)
    (beta : proofCasts ctx (actualPremise inputs b.represented.val stepTyped.sourceCore.val)
      (continuationType inputs b.represented.val (.lam wordType (.lam stateType stepTyped.sourceCore.val))))
    (registered : env.constants ``WordLoopFacts.forStatic = some ⟨0,signature⟩)
    (coverage : Conversion.Covers conv 0 proofCasts) (exposure : Exposure env)
    (kn tn : Lean.Name) (ki ti : Lean.BinderInfo) :
    ∃ result, finish env conv exposure ctx
      (bodyExpected p (app ``HybridWord.Cmd.forStatic [start,stop,stride,b.code])
        (source start stop stride p.s (.lam kn word (.lam tn state original ti) ki)))
      (app ``HybridWord.Cmd.forStatic [start,stop,stride,b.code])
      (app ``WordLoopFacts.forStatic ([start,stop,stride,b.code] ++ p.args ++
        [.lam kn word (.lam tn state original ti) ki,
          .lam kn word (.lam tn state (composition p b.code normalized.plain original
            b.checked.proof normalized.checked.proof) ti) ki]))
      (b.checked.known.orElse normalized.checked.known) = some result ∧
      CastTyping env 0 proofCasts ctx result.proofCore.val result.core.val := by
  obtain ⟨target,next,proof,proofRep,proofTyped⟩ := next_typed inputs closed stable embeds
    wordDeclared stateDeclared consDeclared evalDeclared composeDeclared stepTyped bodyTyped
  have fact := fact_typed inputs (startBound.typed.mono Arithmetic.Includes.embed) (stopBound.typed.mono Arithmetic.Includes.embed)
    (strideBound.typed.mono Arithmetic.Includes.embed) (target.mono embeds) (next.mono embeds) proofTyped beta registered
  have codeArgs := List.Forall₂.cons startBound.represented.property (.cons stopBound.represented.property
    (.cons strideBound.represented.property (.cons b.represented.property .nil)))
  have fnRep : Represents (.lam kn word (.lam tn state original ti) ki)
      (.lam wordType (.lam stateType stepTyped.sourceCore.val)) :=
    .lam (.constant rfl) (.lam (.constant rfl) stepTyped.sourceCore.property)
  have proofLambdaRep : Represents
      (.lam kn word (.lam tn state (composition p b.code normalized.plain original
        b.checked.proof normalized.checked.proof) ti) ki)
      (.lam wordType (.lam stateType proof)) := .lam (.constant rfl) (.lam (.constant rfl) proofRep)
  have certificateRep := app_represents (Represents.constant (name := ``WordLoopFacts.forStatic) (us := []) rfl)
    (.cons startBound.represented.property (.cons stopBound.represented.property
      (.cons strideBound.represented.property (.cons b.represented.property
        (.cons inputs.i.property (.cons inputs.x.property (.cons inputs.y.property
          (.cons inputs.s.property (.cons inputs.ls.property (.cons fnRep
            (.cons proofLambdaRep .nil)))))))))))
  obtain ⟨result,checked,typed,_,_⟩ := finish_cast_complete
    (bodyExpected_represents inputs (app_represents (Represents.constant (name := ``HybridWord.Cmd.forStatic) (us := []) rfl) codeArgs)
      (source_represents startBound.represented.property stopBound.represented.property
        strideBound.represented.property inputs.s.property fnRep)) certificateRep fact
    ((known_casts b.checked bodyTyped.proof).orElse (known_casts normalized.checked stepTyped.proof))
    coverage exposure (app ``HybridWord.Cmd.forStatic [start,stop,stride,b.code])
  exact ⟨result,checked,typed⟩

theorem Bound.closedTerm_complete (bound : Bound env ctx value) : closedTerm value = some bound.term := by
  obtain ⟨core,translated,same⟩ := bound.represented.property.translate_complete
  have exactTranslation : translate value = some bound.represented := by
    have equal : core = bound.represented := Subtype.ext same
    exact equal ▸ translated
  simp only [closedTerm,bound.closed,exactTranslation,Bound.term,bind,Option.bind,pure,Option.pure_def,dite_true]

theorem source_typed
    (headerTyped : CastTyping env 0 casts ctx header headerType)
    (rangeDeclared : env.constants ``HybridWord.range = some ⟨0,rangeSignature⟩)
    (startTyped : CastTyping env 0 casts ctx start intType)
    (stopTyped : CastTyping env 0 casts ctx stop intType)
    (strideTyped : CastTyping env 0 casts ctx stride intType)
    (stateTyped : CastTyping env 0 casts ctx s stateType)
    (functionTyped : CastTyping env 0 casts ctx fn functionType) :
    CastTyping env 0 casts ctx (loop start stop stride s fn) (optionType stateType) := by
  have rangeHead : CastTyping env 0 casts ctx (.const ``HybridWord.range []) rangeSignature :=
    .constant rangeDeclared (by simp) rfl
  have a1 := CastTyping.application rangeHead startTyped
  simp only [rangeSignature,intType,wordsType,wordType,VExpr.inst] at a1
  have a2 := CastTyping.application a1 stopTyped
  simp only [VExpr.inst] at a2
  have a3 := CastTyping.application a2 strideTyped
  have loopHead := CastTyping.application headerTyped a3
  simp only [headerType,functionType,optionType,Step.stepState,wordsType,wordType,stateType,VExpr.inst] at loopHead
  have a4 := CastTyping.application loopHead stateTyped
  simp only [VExpr.inst] at a4
  exact .application a4 functionTyped

end IRComparison.WordFrontend.Certificate.For
