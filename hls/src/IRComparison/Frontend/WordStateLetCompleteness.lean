import IRComparison.Frontend.WordStateAliasCompleteness

/-! Pure State updates use the same state continuation as monadic sequencing.
The source is an ordinary Lean let, and its generated command is sequencing. -/
namespace IRComparison.WordFrontend.Certificate.StateLet
open Lean4Lean LeanTyped LeanTypeInference
variable {casts proofCasts : TypeCasts} [Arithmetic.Includes casts] [Arithmetic.Includes proofCasts]
set_option maxHeartbeats 800000

def firstPremise : VExpr := equalValues (optionType stateType)
  (bodyValue (.bvar 6) (.bvar 5) (.bvar 4) (.bvar 8) (.bvar 3) (.bvar 2))
  (someValue stateType (.bvar 1))
def resultType : VExpr := equalValues (optionType stateType)
  (bodyValue (.bvar 8) (.bvar 7) (.bvar 6)
    (applications (.const ``HybridWord.Cmd.seq []) [.bvar 10,.bvar 9]) (.bvar 5) (.bvar 4))
  (.app (.bvar 2) (.bvar 3))
def signature : VExpr := .forallE cmdType (.forallE cmdType
  (inputsType (.forallE stateType
    (.forallE (.forallE stateType (optionType stateType))
      (.forallE firstPremise (.forallE sequenceNextPremise resultType))))))

def source (binder : Lean.Name) (value next : Lean.Expr) (nondep : Bool) : Lean.Expr :=
  .letE binder state value next nondep

theorem fact_typed (inputs : InputsTyped env ctx p)
    {a : Piece env ctx p (someExpr state first) bodyExpected} (left : BodyCasts inputs a casts)
    (valueRep : Represents first valueCore) (valueTyped : CastTyping env 0 casts ctx valueCore stateType)
    (rightTarget : CastTyping env 0 casts ctx b cmdType)
    (nextTyped : CastTyping env 0 casts ctx next (.forallE stateType (optionType stateType)))
    (nextProof : CastTyping env 0 casts ctx proofNext actual)
    (beta : casts ctx actual (sequenceContinuationType inputs b next))
    (registered : env.constants ``WordFrontendFacts.letState = some ⟨0,signature⟩) :
    CastTyping env 0 casts ctx
      (applications (.const ``WordFrontendFacts.letState [])
        ([a.represented.val,b] ++ inputs.args ++
          [valueCore,next,a.checked.proofCore.val,proofNext]))
      (equalValues (optionType stateType)
        (bodyValue inputs.i.val inputs.x.val inputs.y.val
          (applications (.const ``HybridWord.Cmd.seq []) [a.represented.val,b]) inputs.s.val inputs.ls.val)
        (.app next valueCore)) := by
  have fact : CastTyping env 0 casts ctx (.const ``WordFrontendFacts.letState []) signature :=
    .constant (levels := []) registered (by simp) rfl
  have a1 := CastTyping.application fact left.target
  simp only [signature,inputsType,exprType,cmdType,wordType,stateType,wordsType,optionType,VExpr.inst] at a1
  have a2 := CastTyping.application a1 rightTarget
  simp only [VExpr.inst] at a2
  have a3 := inputs.apply_casts a2
  simp only [InputsTyped.instantiate,firstPremise,sequenceNextPremise,resultType,
    bodyValue,scalarValue,someValue,equalValues,optionType,stateType,wordType,applications,Nat.reduceAdd,
    ← VExpr.lift_instN_lo,VExpr.inst_lift,VExpr.inst,
    VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] at a3
  have a4 := CastTyping.application a3 valueTyped
  simp only [Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst_lift,VExpr.inst,
    VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] at a4
  have a5 := CastTyping.application a4 nextTyped
  simp only [Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst_lift,VExpr.inst,
    VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] at a5
  have valueSource : left.sourceCore.val = someValue stateType valueCore :=
    left.sourceCore.property.unique (.app (.app (.constant rfl) (.constant rfl)) valueRep)
  have firstEquality := left.equality
  rw [valueSource] at firstEquality
  have a6 := CastTyping.application a5 firstEquality
  simp only [Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst_lift,VExpr.inst,
    VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] at a6
  have cast := beta
  simp only [sequenceContinuationType,bodyValue,scalarValue,someValue,equalValues,applications,optionType,wordType,stateType] at cast
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
    {b : Piece env (stateType::ctx) {p.lift with s := .bvar 0} nextBody bodyExpected}
    (right : BodyCasts (inputs.nextState closed) b casts proofCasts)
    (beta : proofCasts ctx (sequenceNextActual inputs b.represented.val right.sourceCore.val)
      (sequenceContinuationType inputs b.represented.val (.lam stateType right.sourceCore.val)))
    (registered : env.constants ``WordFrontendFacts.letState = some ⟨0,signature⟩)
    (coverage : Conversion.Covers conv 0 proofCasts) (exposure : Exposure env)
    (binder : Lean.Name) (nondep : Bool) :
    ∃ result, finish env conv exposure ctx
      (bodyExpected p (app ``HybridWord.Cmd.seq [a.code,b.code])
        (source binder first nextBody nondep))
      (app ``HybridWord.Cmd.seq [a.code,b.code])
      (app ``WordFrontendFacts.letState ([a.code,b.code] ++ p.args ++
        [first,.lam binder state nextBody .default,a.checked.proof,.lam binder state b.checked.proof .default]))
      (a.checked.known.orElse b.checked.known) = some result ∧
      CastTyping env 0 proofCasts ctx result.proofCore.val result.core.val ∧
      result.code = app ``HybridWord.Cmd.seq [a.code,b.code] ∧
      result.proof = app ``WordFrontendFacts.letState ([a.code,b.code] ++ p.args ++
        [first,.lam binder state nextBody .default,a.checked.proof,.lam binder state b.checked.proof .default]) := by
  obtain ⟨target,nextTyped,nextProof⟩ := sequence_next_typed inputs closed stable stateDeclared right
  have typed := fact_typed inputs (left.inProofCasts embeds) valueRep (valueTyped.mono embeds) (target.mono embeds)
    (nextTyped.mono embeds) nextProof beta registered
  exact finish_cast_complete
    (bodyExpected_represents inputs
      (app_represents (.constant rfl) (.cons a.represented.property (.cons b.represented.property .nil)))
      (.letE (.constant rfl) valueRep right.sourceCore.property))
    (app_represents (.constant rfl) (.cons a.represented.property (.cons b.represented.property
      (.cons inputs.i.property (.cons inputs.x.property (.cons inputs.y.property
        (.cons inputs.s.property (.cons inputs.ls.property (.cons valueRep
          (.cons (.lam (.constant rfl) right.sourceCore.property)
            (.cons a.checked.proofCore.property (.cons (.lam (.constant rfl) b.checked.proofCore.property) .nil))))))))))))
    typed ((known_casts a.checked left.proof).orElse (known_casts b.checked right.proof))
    coverage exposure _

end IRComparison.WordFrontend.Certificate.StateLet
