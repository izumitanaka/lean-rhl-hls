import IRComparison.Frontend.WordForConversion

/-! Naming the current State is a source binder, not a memory copy. Its
certificate uses the existing state-continuation proof and leaves the body
command unchanged. -/
namespace IRComparison.WordFrontend.Certificate.StateAlias
open Lean4Lean LeanTyped LeanTypeInference
variable {casts proofCasts : TypeCasts} [Arithmetic.Includes casts] [Arithmetic.Includes proofCasts]
set_option maxHeartbeats 1200000

def premise : VExpr := .forallE stateType
  (equalValues (optionType stateType)
    (bodyValue (.bvar 6) (.bvar 5) (.bvar 4) (.bvar 7) (.bvar 0) (.bvar 2))
    (.app (.bvar 1) (.bvar 0)))
def resultType : VExpr := equalValues (optionType stateType)
  (bodyValue (.bvar 6) (.bvar 5) (.bvar 4) (.bvar 7) (.bvar 3) (.bvar 2))
  (.app (.bvar 1) (.bvar 3))
def signature : VExpr := .forallE cmdType (inputsType
  (.forallE (.forallE stateType (optionType stateType)) (.forallE premise resultType)))

theorem fact_typed (inputs : InputsTyped env ctx p)
    (targetTyped : CastTyping env 0 casts ctx code cmdType)
    (nextTyped : CastTyping env 0 casts ctx next (.forallE stateType (optionType stateType)))
    (proofTyped : CastTyping env 0 casts ctx proof actual)
    (beta : casts ctx actual (sequenceContinuationType inputs code next))
    (registered : env.constants ``WordFrontendFacts.letStateAlias = some ⟨0,signature⟩) :
    CastTyping env 0 casts ctx
      (applications (.const ``WordFrontendFacts.letStateAlias []) ([code] ++ inputs.args ++ [next,proof]))
      (equalValues (optionType stateType)
        (bodyValue inputs.i.val inputs.x.val inputs.y.val code inputs.s.val inputs.ls.val)
        (.app next inputs.s.val)) := by
  have fact : CastTyping env 0 casts ctx (.const ``WordFrontendFacts.letStateAlias []) signature :=
    .constant registered (by simp) rfl
  have a1 := CastTyping.application fact targetTyped
  simp only [signature,inputsType,cmdType,wordType,stateType,wordsType,optionType,VExpr.inst] at a1
  have a2 := inputs.apply_casts a1
  simp only [InputsTyped.instantiate,premise,resultType,bodyValue,equalValues,optionType,stateType,applications,
    VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower,Nat.reduceAdd,
    ← VExpr.lift_instN_lo,VExpr.inst_lift] at a2
  have a3 := CastTyping.application a2 nextTyped
  simp only [VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower,Nat.reduceAdd,
    ← VExpr.lift_instN_lo,VExpr.inst_lift] at a3
  have cast := beta
  simp only [sequenceContinuationType,bodyValue,equalValues,optionType,stateType,applications] at cast
  simpa only [InputsTyped.args,applications,List.cons_append,List.nil_append,bodyValue,equalValues,
    optionType,stateType,VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower,
    Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst_lift] using CastTyping.convertedApplication a3 proofTyped cast

theorem alias_certificate (inputs : InputsTyped env ctx p)
    (closed : ClosedConstantTypes env) (stable : ClosedCasts casts)
    (embeds : ∀ scope a b, casts scope a b → proofCasts scope a b)
    (stateDeclared : env.constants ``HybridWord.State = some ⟨0,.sort (.succ .zero)⟩)
    {b : Piece env (stateType::ctx) {p.lift with s := .bvar 0} nextBody bodyExpected}
    (right : BodyCasts (inputs.nextState closed) b casts proofCasts)
    (beta : proofCasts ctx (sequenceNextActual inputs b.represented.val right.sourceCore.val)
      (sequenceContinuationType inputs b.represented.val (.lam stateType right.sourceCore.val)))
    (registered : env.constants ``WordFrontendFacts.letStateAlias = some ⟨0,signature⟩)
    (coverage : Conversion.Covers conv 0 proofCasts) (exposure : Exposure env)
    (binder : Lean.Name) (nondep : Bool) :
    ∃ artifact, finish env conv exposure ctx
      (bodyExpected p b.code (.letE binder state p.s nextBody nondep)) b.code
      (app ``WordFrontendFacts.letStateAlias ([b.code] ++ p.args ++
        [.lam binder state nextBody .default,.lam binder state b.checked.proof .default]))
      b.checked.known = some artifact ∧
      ∃ typed : BodyCasts inputs
        (⟨b.code,artifact,b.closed,b.represented⟩ : Piece env ctx p (.letE binder state p.s nextBody nondep) bodyExpected)
        casts proofCasts, typed.sourceCore.val = .app (.lam stateType right.sourceCore.val) inputs.s.val := by
  obtain ⟨target,nextTyped,nextProof⟩ := sequence_next_typed inputs closed stable stateDeclared right
  have fact := fact_typed inputs (target.mono embeds) (nextTyped.mono embeds) nextProof beta registered
  have sourceRep : Represents (.letE binder state p.s nextBody nondep)
      (.app (.lam stateType right.sourceCore.val) inputs.s.val) :=
    .letE (.constant rfl) inputs.s.property right.sourceCore.property
  have nextRep : Represents (.lam binder state nextBody .default) (.lam stateType right.sourceCore.val) :=
    .lam (.constant rfl) right.sourceCore.property
  have proofRep : Represents (.lam binder state b.checked.proof .default) (.lam stateType b.checked.proofCore.val) :=
    .lam (.constant rfl) b.checked.proofCore.property
  obtain ⟨artifact,checked,typed,_,_⟩ := finish_cast_complete
    (bodyExpected_represents inputs b.represented.property sourceRep)
    (app_represents (Represents.constant (name := ``WordFrontendFacts.letStateAlias) (us := []) rfl)
      (.cons b.represented.property (.cons inputs.i.property (.cons inputs.x.property (.cons inputs.y.property
        (.cons inputs.s.property (.cons inputs.ls.property (.cons nextRep (.cons proofRep .nil)))))))))
    fact (known_casts b.checked right.proof) coverage exposure b.code
  let piece : Piece env ctx p (.letE binder state p.s nextBody nondep) bodyExpected :=
    ⟨b.code,artifact,b.closed,b.represented⟩
  exact ⟨artifact,checked,⟨⟨_,sourceRep⟩,CastTyping.application nextTyped (inputs.hs.withCasts casts),target,typed⟩,rfl⟩

theorem alias_step_complete (inputs : InputsTyped env ctx p)
    (closed : ClosedConstantTypes env) (stable : ClosedCasts casts)
    (embeds : ∀ scope a b, casts scope a b → proofCasts scope a b)
    (stateDeclared : env.constants ``HybridWord.State = some ⟨0,.sort (.succ .zero)⟩)
    {b : Piece env (stateType::ctx) {p.lift with s := .bvar 0} nextBody bodyExpected}
    (right : BodyCasts (inputs.nextState closed) b casts proofCasts)
    (beta : proofCasts ctx (sequenceNextActual inputs b.represented.val right.sourceCore.val)
      (sequenceContinuationType inputs b.represented.val (.lam stateType right.sourceCore.val)))
    (registered : env.constants ``WordFrontendFacts.letStateAlias = some ⟨0,signature⟩)
    (coverage : Conversion.Covers conv 0 proofCasts) (exposure : Exposure env)
    (binder : Lean.Name) (nondep : Bool) (scalarCall : PieceParser env scalarExpected) (readCall : PieceParser env readExpected)
    (stepCall : StepParser env) (bodyCall : PieceParser env bodyExpected)
    (parsed : bodyCall (stateType::ctx) {p.lift with s := .bvar 0} nextBody = some b) :
    ∃ piece, bodyStep env conv exposure scalarCall readCall stepCall bodyCall ctx p (.letE binder state p.s nextBody nondep) = some piece ∧
      Nonempty (BodyCasts inputs piece casts proofCasts) ∧ piece.code = b.code := by
  obtain ⟨artifact,checked,typed,_⟩ := alias_certificate inputs closed stable embeds stateDeclared right beta registered
    coverage exposure binder nondep
  let piece : Piece env ctx p (.letE binder state p.s nextBody nondep) bodyExpected :=
    ⟨b.code,artifact,b.closed,b.represented⟩
  refine ⟨piece,?_,⟨typed⟩,rfl⟩
  have typeSame := sameTerm_complete (a := state) (b := state) (Represents.constant rfl) (Represents.constant rfl)
  have valueSame := sameTerm_complete inputs.s.property inputs.s.property
  have translated : translate state = some ⟨stateType,Represents.constant rfl⟩ := rfl
  simp only [bodyStep,typeSame,valueSame,Bool.and_self,translated,parsed,Option.bind_some]
  simp [checked,piece,Piece.closedTerm,app] at checked ⊢
  refine ⟨b,parsed,artifact,?_,rfl,HEq.rfl,HEq.rfl⟩
  simpa only [Inputs.args,List.foldl_cons,List.foldl_nil] using checked


end IRComparison.WordFrontend.Certificate.StateAlias
