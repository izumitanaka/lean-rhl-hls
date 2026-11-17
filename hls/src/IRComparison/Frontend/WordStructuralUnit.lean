import IRComparison.Frontend.WordStructuralStateLet
import IRComparison.Frontend.WordUnitCompleteness

/-! Administrative Unit sequencing for both command result modes. This
retains the binder during traversal and composes one command certificate. -/
namespace IRComparison.WordFrontend.StructuralUnit
open Lean4Lean LeanTyped LeanTypeInference Certificate StructuralBody
variable {casts proofCasts : TypeCasts} [Arithmetic.Includes casts] [Arithmetic.Includes proofCasts]
open UnitStep (unitType unitValue nativeUnitType nativeUnitValue pureUnit nativePureUnit)
set_option maxHeartbeats 1800000

def mode (isStep : Bool) : Mode := if isStep then .step else .body
def nativeResult (isStep : Bool) : Lean.Expr := if isStep then stepType else state
def factName (isStep : Bool) : Lean.Name :=
  if isStep then ``WordLoopFacts.unitSequence else ``WordFrontendFacts.unitSequence

def source (isStep : Bool) (binder : Lean.Name) (next : Lean.Expr) (info : Lean.BinderInfo) : Lean.Expr :=
  Lean.mkApp2 (bindHead nativeUnitType (nativeResult isStep)) nativePureUnit (.lam binder nativeUnitType next info)

def header (isStep : Bool) : VExpr := optionBindHeader unitType (For.unitResult isStep)

theorem header_represents (isStep : Bool) :
    Represents (bindHead nativeUnitType (nativeResult isStep)) (header isStep) := by
  cases isStep
  · exact .app (.app (.app (.app (.constant rfl) (.constant rfl))
      (.app (.app (.constant rfl) (.constant rfl)) (.constant rfl))) (.constant rfl)) (.constant rfl)
  · exact .app (.app (.app (.app (.constant rfl) (.constant rfl))
      (.app (.app (.constant rfl) (.constant rfl)) (.constant rfl))) (.constant rfl))
      (.app (.constant rfl) (.constant rfl))

theorem header_inst (isStep : Bool) (v : VExpr) (k : Nat) :
    (header isStep).inst v k = header isStep :=
  ((header_represents isStep).closed 0 (by cases isStep <;> rfl)).instN_eq (Nat.zero_le k)

def nextPremise (isStep : Bool) : VExpr := .forallE unitType
  (For.unitEquation isStep
    (bodyValue (.bvar 6) (.bvar 5) (.bvar 4) (.bvar 7) (.bvar 3) (.bvar 2))
    (.app (.bvar 1) (.bvar 0)))
def resultType (isStep : Bool) : VExpr := For.unitEquation isStep
  (bodyValue (.bvar 6) (.bvar 5) (.bvar 4) (.bvar 7) (.bvar 3) (.bvar 2))
  (applications (header isStep) [pureUnit,.bvar 1])
def signature (isStep : Bool) : VExpr := .forallE cmdType (inputsType
  (.forallE (.forallE unitType (optionType (For.unitResult isStep)))
    (.forallE (nextPremise isStep) (resultType isStep))))

def lhs (inputs : InputsTyped env ctx p) (code : VExpr) : VExpr :=
  bodyValue inputs.i.val.lift inputs.x.val.lift inputs.y.val.lift code.lift
    inputs.s.val.lift inputs.ls.val.lift

def continuationType (isStep : Bool) (inputs : InputsTyped env ctx p) (code next : VExpr) : VExpr :=
  .forallE unitType (For.unitEquation isStep (lhs inputs code) (.app next.lift (.bvar 0)))

structure CommandCasts (inputs : InputsTyped env ctx p)
    (piece : Piece env ctx p original (mode isStep).expected) (casts : TypeCasts)
    (proofCasts : TypeCasts := casts) where
  sourceCore : {core // Represents original core}
  value : CastTyping env 0 casts ctx sourceCore.val (optionType (For.unitResult isStep))
  target : CastTyping env 0 casts ctx piece.represented.val cmdType
  proof : CastTyping env 0 proofCasts ctx piece.checked.proofCore.val piece.checked.core.val

theorem expected_represents (isStep : Bool) (inputs : InputsTyped env ctx p)
    (code : Represents nativeCode coreCode) (value : Represents nativeSource coreSource) :
    Represents ((mode isStep).expected p nativeCode nativeSource)
      (For.unitEquation isStep (bodyValue inputs.i.val inputs.x.val inputs.y.val coreCode inputs.s.val inputs.ls.val) coreSource) := by
  cases isStep
  · exact bodyExpected_represents inputs code value
  · exact Step.expected_represents (evalCmd_represents inputs code) value

theorem CommandCasts.equality {piece : Piece env ctx p original (mode isStep).expected}
    (typed : CommandCasts inputs piece casts proofCasts) :
    CastTyping env 0 proofCasts ctx piece.checked.proofCore.val
      (For.unitEquation isStep (bodyValue inputs.i.val inputs.x.val inputs.y.val piece.represented.val inputs.s.val inputs.ls.val)
        typed.sourceCore.val) :=
  piece.checked.core.property.unique (expected_represents isStep inputs piece.represented.property
    typed.sourceCore.property) ▸ typed.proof

theorem next_typed (inputs : InputsTyped env ctx p) (closed : ClosedConstantTypes env)
    (stable : ClosedCasts casts) (units : UnitStep.Signatures env)
    {b : Piece env (unitType::ctx) p.lift nextBody (mode isStep).expected}
    (right : CommandCasts (inputs.lift closed unitType) b casts proofCasts) :
    CastTyping env 0 casts ctx b.represented.val cmdType ∧
    CastTyping env 0 casts ctx (.lam unitType right.sourceCore.val)
      (.forallE unitType (optionType (For.unitResult isStep))) ∧
    CastTyping env 0 proofCasts ctx (.lam unitType b.checked.proofCore.val)
      (For.unitActual isStep (lhs inputs b.represented.val) right.sourceCore.val) := by
  have targetClosed := b.represented.property.closed 0 b.closed
  refine ⟨right.target.closed_context stable targetClosed ctx,
    .lambda (units.type_typed.withCasts casts) right.value,?_⟩
  have proof := CastTyping.lambda (units.type_typed.withCasts proofCasts) right.equality
  simpa only [For.unitActual,lhs,InputsTyped.lift,targetClosed.lift_eq] using proof

theorem fact_typed (isStep : Bool) (inputs : InputsTyped env ctx p)
    (targetTyped : CastTyping env 0 casts ctx code cmdType)
    (nextTyped : CastTyping env 0 casts ctx next (.forallE unitType (optionType (For.unitResult isStep))))
    (proofTyped : CastTyping env 0 casts ctx proof actual)
    (beta : casts ctx actual (continuationType isStep inputs code next))
    (registered : env.constants (factName isStep) = some ⟨0,signature isStep⟩) :
    CastTyping env 0 casts ctx
      (applications (.const (factName isStep) []) ([code] ++ inputs.args ++ [next,proof]))
      (For.unitEquation isStep (bodyValue inputs.i.val inputs.x.val inputs.y.val code inputs.s.val inputs.ls.val)
        (applications (header isStep) [pureUnit,next])) := by
  cases isStep <;> (
    have fact := CastTyping.constant (casts := casts) (ctx := ctx) (U := 0) (levels := [])
      registered (by simp) rfl
    simp only [signature,nextPremise,resultType,For.unitResult,For.unitEquation,Step.expected,Step.lifted,
      Step.stepState,header,optionBindHeader,inputsType,cmdType,wordType,stateType,wordsType,optionType,
      unitType,pureUnit,Return.Form.headerFor,Return.pureInstance,unitValue,bodyValue,equalValues,
      applications,VExpr.instL,VLevel.inst,List.map_nil,Bool.false_eq_true,ite_false,ite_true] at fact
    have a1 := CastTyping.application fact targetTyped
    simp only [signature,For.unitResult,inputsType,cmdType,wordType,stateType,wordsType,optionType,
      unitType,Step.stepState,Bool.false_eq_true,ite_false,ite_true,VExpr.inst] at a1
    have a2 := inputs.apply_casts a1
    simp only [InputsTyped.instantiate,nextPremise,resultType,For.unitEquation,Step.expected,Step.lifted,
      Step.stepState,unitType,bodyValue,equalValues,optionType,stateType,applications,pureUnit,
      Return.Form.headerFor,Return.pureInstance,unitValue,header_inst,
      VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower,Nat.reduceAdd,
      ← VExpr.lift_instN_lo,VExpr.inst_lift,Bool.false_eq_true,ite_false,ite_true] at a2
    have a3 := CastTyping.application a2 nextTyped
    simp only [VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower,Nat.reduceAdd,
      ← VExpr.lift_instN_lo,VExpr.inst_lift,header_inst] at a3
    have cast := beta
    simp only [continuationType,lhs,For.unitEquation,Step.expected,Step.lifted,Step.stepState,
      bodyValue,equalValues,optionType,stateType,applications,unitType,Bool.false_eq_true,ite_false,ite_true] at cast
    simpa only [factName,InputsTyped.args,applications,List.cons_append,List.nil_append,For.unitEquation,
      Step.expected,Step.lifted,Step.stepState,bodyValue,equalValues,optionType,stateType,unitType,
      pureUnit,Return.Form.headerFor,Return.pureInstance,unitValue,Bool.false_eq_true,ite_false,ite_true,
      VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower,Nat.reduceAdd,
      ← VExpr.lift_instN_lo,VExpr.inst_lift,header_inst] using CastTyping.convertedApplication a3 proofTyped cast)


theorem substitute_source (σ : Substitution) (isStep : Bool) :
    σ.apply (source isStep binder nextBody info) = source isStep binder ((under σ).apply nextBody) info := by
  cases σ <;> cases isStep <;> rfl

theorem mapped_complete_code (isStep : Bool) (inputs : InputsTyped env ctx p)
    (closed : ClosedConstantTypes env) (stable : ClosedCasts casts)
    (embeds : ∀ scope a b, casts scope a b → proofCasts scope a b)
    (units : UnitStep.Signatures env) (steps : Step.Signatures env) (binds : BindSignatures env)
    {b : Piece env (unitType::ctx) p.lift ((under σ).apply nextBody) (mode isStep).expected}
    (right : CommandCasts (inputs.lift closed unitType) b casts proofCasts)
    (beta : proofCasts ctx (For.unitActual isStep (lhs inputs b.represented.val) right.sourceCore.val)
      (continuationType isStep inputs b.represented.val (.lam unitType right.sourceCore.val)))
    (registered : env.constants (factName isStep) = some ⟨0,signature isStep⟩)
    (coverage : Conversion.Covers conv 0 proofCasts) (exposure : Exposure env)
    (binder : Lean.Name) (info : Lean.BinderInfo)
    (parsed : visit env conv exposure nextBody (unitType::ctx) p.lift (mode isStep) (under σ) (underFunctions fs) = some b) :
    ∃ piece, visit env conv exposure (source isStep binder nextBody info) ctx p (mode isStep)
      σ fs = some piece ∧ Nonempty (CommandCasts inputs piece casts proofCasts) ∧ piece.code = b.code := by
  obtain ⟨target,nextTyped,nextProof⟩ := next_typed inputs closed stable units right
  have normalizedRep := Represents.app (.app (header_represents isStep) UnitStep.pure_represents)
    (Represents.lam (ty := nativeUnitType) (name := binder) (info := info) (.constant rfl) right.sourceCore.property)
  have sourceRep : Represents (σ.apply (source isStep binder nextBody info))
      (applications (header isStep) [pureUnit,.lam unitType right.sourceCore.val]) := by
    rw [substitute_source]; exact normalizedRep
  have typed := fact_typed isStep inputs (target.mono embeds) (nextTyped.mono embeds) nextProof beta registered
  obtain ⟨artifact,checked,proofTyped,_,_⟩ := finish_cast_complete
    (expected_represents isStep inputs b.represented.property sourceRep)
    (app_represents (Represents.constant (name := factName isStep) (us := []) rfl)
      (.cons b.represented.property (.cons inputs.i.property (.cons inputs.x.property (.cons inputs.y.property
        (.cons inputs.s.property (.cons inputs.ls.property
          (.cons (Represents.lam (ty := nativeUnitType) (name := binder) (info := info) (.constant rfl) right.sourceCore.property)
            (.cons (Represents.lam (ty := nativeUnitType) (name := binder) (info := info) (.constant rfl) b.checked.proofCore.property) .nil)))))))))
    typed (known_casts b.checked right.proof) coverage exposure b.code
  let piece : Piece env ctx p (σ.apply (source isStep binder nextBody info)) (mode isStep).expected :=
    ⟨b.code,artifact,b.closed,b.represented⟩
  have resultTyped : DirectTyping env 0 ctx (For.unitResult isStep) (.sort (.succ .zero)) := by
    cases isStep
    · exact .constant steps.state (by simp) rfl
    · exact steps.step_typed
  have resultClosed : (For.unitResult isStep).ClosedN 0 := by cases isStep <;> trivial
  have headTyped := (binds.header_typed units.type_typed resultTyped (by trivial) resultClosed).withCasts casts
  have firstTyped := CastTyping.application headTyped ((UnitStep.pure_typed steps units).withCasts casts)
  have instResult : (optionType (For.unitResult isStep)).inst pureUnit = optionType (For.unitResult isStep) := by
    cases isStep <;> rfl
  simp only [VExpr.inst,unitType,optionType,resultClosed.instN_eq (Nat.zero_le _)] at firstTyped
  have sourceTyped := CastTyping.application firstTyped nextTyped
  simp only [VExpr.inst,unitType,optionType,resultClosed.instN_eq (Nat.zero_le _)] at sourceTyped
  refine ⟨piece,?_,⟨⟨⟨_,sourceRep⟩,sourceTyped,target,proofTyped⟩⟩,rfl⟩
  have translated : translate nativeUnitType = some ⟨unitType,Represents.constant rfl⟩ := rfl
  have same : sameTerm nativeUnitType (.const ``PUnit [.succ .zero]) = true := rfl
  have args : (source isStep binder nextBody info).getAppArgs =
    #[.const ``Option [.zero],Lean.mkAppN (.const ``Monad.toBind [.zero,.zero])
      #[.const ``Option [.zero],.const ``instMonadOption [.zero]],nativeUnitType,nativeResult isStep,
      nativePureUnit,.lam binder nativeUnitType nextBody info] := rfl
  have modeValue : (mode isStep == Mode.value) = false := by cases isStep <;> rfl
  have modeStep : (mode isStep == Mode.step) = isStep := by cases isStep <;> rfl
  rw [visit]
  cases isStep <;> cases σ
  all_goals
    simp [node,modeValue,modeStep,letParts,applicationHead,makeContinuation,continuationParts,lambdaChain,
      Substitution.apply,LeanBindings.substitute,ScalarEnvironment.arguments,ScalarEnvironment.below,lambdaParts,under,
      same,translated,source,Lean.mkApp,Lean.mkApp2,Lean.mkAppB,
      Lean.Expr.getAppFn,Lean.Expr.constName?,bindHead,Lean.mkAppN,List.map_cons,List.map_nil,
      nativeResult,nativeUnitType,nativePureUnit,UnitStep.nativeUnitValue] at parsed checked ⊢
    simp only [source,Lean.mkApp,Lean.mkApp2,Lean.mkAppB,bindHead,Lean.mkAppN] at args
    try simp only [List.map_append,List.map_cons,List.map_nil,List.nil_append,List.cons_append,
      Function.comp_apply,List.length_cons,List.length_nil,Nat.reduceAdd,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.unattach_some,
      args,Array.getElem?_eq_getElem,Array.back?,same,translated,
      Option.bind_some,Bool.false_eq_true,Bool.true_eq_false,ite_false,ite_true]
    simp [parsed,finishBody,ClosedTerm.app,Piece.closedTerm,piece,source,Lean.mkApp2,
      Lean.mkAppB,Lean.mkApp,app,factName] at checked ⊢
    try simp only [List.map_cons,List.map_nil,List.nil_append,List.cons_append,List.length_cons,List.length_nil,
      Nat.reduceAdd,Function.comp_apply,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.unattach_some]
    try simp only [List.map_append,List.map_cons,List.map_nil,List.nil_append,List.cons_append,List.length_cons,List.length_nil,
      Nat.reduceAdd,Function.comp_apply,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.unattach_some]
    simp only [nativeUnitType] at same translated
    simp only [same,translated,Option.unattach_some,Option.bind_some,ite_true,parsed]
    refine ⟨nativePureUnit,rfl,unitType,rfl,?_⟩
    rw [parsed]
    simp only [Option.bind_some]
    simp only [Inputs.args,List.foldl_cons,List.foldl_nil] at checked ⊢
    rw [checked]
    rfl

theorem complete_code (isStep : Bool) (inputs : InputsTyped env ctx p)
    (closed : ClosedConstantTypes env) (stable : ClosedCasts casts)
    (embeds : ∀ scope a b, casts scope a b → proofCasts scope a b)
    (units : UnitStep.Signatures env) (steps : Step.Signatures env) (binds : BindSignatures env)
    {b : Piece env (unitType::ctx) p.lift nextBody (mode isStep).expected}
    (right : CommandCasts (inputs.lift closed unitType) b casts proofCasts)
    (beta : proofCasts ctx (For.unitActual isStep (lhs inputs b.represented.val) right.sourceCore.val)
      (continuationType isStep inputs b.represented.val (.lam unitType right.sourceCore.val)))
    (registered : env.constants (factName isStep) = some ⟨0,signature isStep⟩)
    (coverage : Conversion.Covers conv 0 proofCasts) (exposure : Exposure env)
    (binder : Lean.Name) (info : Lean.BinderInfo)
    (parsed : visit env conv exposure nextBody (unitType::ctx) p.lift (mode isStep) .identity (fun _ => none) = some b) :
    ∃ piece, visit env conv exposure (source isStep binder nextBody info) ctx p (mode isStep)
      .identity (fun _ => none) = some piece ∧ Nonempty (CommandCasts inputs piece casts proofCasts) ∧ piece.code = b.code := by
  have empty : underFunctions (fun _ => (none : Option (Continuation env))) = (fun _ => none) := by
    funext n; cases n <;> rfl
  exact mapped_complete_code (σ := .identity) (fs := fun _ => none) isStep inputs closed stable embeds
    units steps binds right beta registered coverage exposure binder info (by simpa only [under,empty] using parsed)

theorem complete (isStep : Bool) (inputs : InputsTyped env ctx p)
    (closed : ClosedConstantTypes env) (stable : ClosedCasts casts)
    (embeds : ∀ scope a b, casts scope a b → proofCasts scope a b)
    (units : UnitStep.Signatures env) (steps : Step.Signatures env) (binds : BindSignatures env)
    {b : Piece env (unitType::ctx) p.lift nextBody (mode isStep).expected}
    (right : CommandCasts (inputs.lift closed unitType) b casts proofCasts)
    (beta : proofCasts ctx (For.unitActual isStep (lhs inputs b.represented.val) right.sourceCore.val)
      (continuationType isStep inputs b.represented.val (.lam unitType right.sourceCore.val)))
    (registered : env.constants (factName isStep) = some ⟨0,signature isStep⟩)
    (coverage : Conversion.Covers conv 0 proofCasts) (exposure : Exposure env)
    (binder : Lean.Name) (info : Lean.BinderInfo)
    (parsed : visit env conv exposure nextBody (unitType::ctx) p.lift (mode isStep) .identity (fun _ => none) = some b) :
    ∃ piece, visit env conv exposure (source isStep binder nextBody info) ctx p (mode isStep)
      .identity (fun _ => none) = some piece ∧ Nonempty (CommandCasts inputs piece casts proofCasts) := by
  obtain ⟨piece,success,typed,_⟩ := complete_code isStep inputs closed stable embeds units steps binds right beta registered coverage exposure binder info parsed
  exact ⟨piece,success,typed⟩

end IRComparison.WordFrontend.StructuralUnit
