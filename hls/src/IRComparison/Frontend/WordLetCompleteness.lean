import IRComparison.Frontend.WordBindCompleteness

/-! Pure Lean let bindings reuse the value-continuation invariant and beta
comparison of read bindings. Only the source fact and parser branch differ. -/
namespace IRComparison.WordFrontend.Certificate
open Lean4Lean LeanTyped LeanTypeInference
variable {casts proofCasts : TypeCasts} [Arithmetic.Includes casts] [Arithmetic.Includes proofCasts]
set_option maxHeartbeats 800000

def letValueFirstPremise : VExpr := equalValues (optionType wordType)
  (scalarValue (.bvar 6) (.bvar 5) (.bvar 4) (.bvar 3) (.bvar 2) (.bvar 8))
  (someValue wordType (.bvar 1))
def letValueResult : VExpr := equalValues (optionType stateType)
  (bodyValue (.bvar 8) (.bvar 7) (.bvar 6)
    (applications (.const ``HybridWord.Cmd.letValue []) [.bvar 10,.bvar 9]) (.bvar 5) (.bvar 4))
  (.app (.bvar 2) (.bvar 3))
def letValueSignature : VExpr := .forallE exprType (.forallE cmdType
  (inputsType (.forallE wordType
    (.forallE (.forallE wordType (optionType stateType))
      (.forallE letValueFirstPremise (.forallE bindValueNextPremise letValueResult))))))

def letValueSource (binder : Lean.Name) (value next : Lean.Expr) (nondep : Bool) : Lean.Expr :=
  .letE binder word value next nondep

theorem letValue_typed (inputs : InputsTyped env ctx p)
    {a : Piece env ctx p first scalarExpected} (left : ScalarCasts inputs a casts)
    (rightTarget : CastTyping env 0 casts ctx b cmdType)
    (nextTyped : CheckedTyping env 0 casts ctx next (.forallE wordType (optionType stateType)))
    (nextProof : CastTyping env 0 casts ctx proofNext actual)
    (beta : casts ctx actual (bindValueContinuationType inputs b next))
    (registered : env.constants ``WordFrontendFacts.letValue = some ⟨0,letValueSignature⟩) :
    CastTyping env 0 casts ctx
      (applications (.const ``WordFrontendFacts.letValue [])
        ([a.represented.val,b] ++ inputs.args ++
          [left.sourceCore.val,next,a.checked.proofCore.val,proofNext]))
      (equalValues (optionType stateType)
        (bodyValue inputs.i.val inputs.x.val inputs.y.val
          (applications (.const ``HybridWord.Cmd.letValue []) [a.represented.val,b]) inputs.s.val inputs.ls.val)
        (.app next left.sourceCore.val)) := by
  have fact : CastTyping env 0 casts ctx (.const ``WordFrontendFacts.letValue []) letValueSignature :=
    .constant (levels := []) registered (by simp) rfl
  have a1 := CastTyping.application fact left.target
  simp only [letValueSignature,inputsType,exprType,cmdType,wordType,stateType,wordsType,optionType,VExpr.inst] at a1
  have a2 := CastTyping.application a1 rightTarget
  simp only [VExpr.inst] at a2
  have a3 := inputs.apply_casts a2
  simp only [InputsTyped.instantiate,letValueFirstPremise,bindValueNextPremise,letValueResult,
    bodyValue,scalarValue,someValue,equalValues,optionType,stateType,wordType,applications,Nat.reduceAdd,
    ← VExpr.lift_instN_lo,VExpr.inst_lift,VExpr.inst,
    VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] at a3
  have a4 := CastTyping.checkedApplication a3 left.value
  simp only [Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst_lift,VExpr.inst,
    VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] at a4
  have a5 := CastTyping.checkedApplication a4 nextTyped
  simp only [Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst_lift,VExpr.inst,
    VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] at a5
  have a6 := CastTyping.application a5 left.equality
  simp only [Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst_lift,VExpr.inst,
    VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] at a6
  have cast := beta
  simp only [bindValueContinuationType,bodyValue,scalarValue,someValue,equalValues,applications,optionType,wordType,stateType] at cast
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
    {b : Piece env (wordType::ctx) {p.lift with locals := .bvar 0 :: p.lift.locals} nextBody bodyExpected}
    (right : BodyCasts (inputs.nextWord closed wordDeclared consDeclared) b casts proofCasts)
    (beta : proofCasts ctx (bindValueNextActual inputs b.represented.val right.sourceCore.val)
      (bindValueContinuationType inputs b.represented.val (.lam wordType right.sourceCore.val)))
    (registered : env.constants ``WordFrontendFacts.letValue = some ⟨0,letValueSignature⟩)
    (coverage : Conversion.Covers conv 0 proofCasts) (exposure : Exposure env)
    (binder : Lean.Name) (nondep : Bool) :
    ∃ result, finish env conv exposure ctx
      (bodyExpected p (app ``HybridWord.Cmd.letValue [a.code,b.code])
        (letValueSource binder first nextBody nondep))
      (app ``HybridWord.Cmd.letValue [a.code,b.code])
      (app ``WordFrontendFacts.letValue ([a.code,b.code] ++ p.args ++
        [first,.lam binder word nextBody .default,a.checked.proof,.lam binder word b.checked.proof .default]))
      (a.checked.known.orElse b.checked.known) = some result ∧
      CastTyping env 0 proofCasts ctx result.proofCore.val result.core.val ∧
      result.code = app ``HybridWord.Cmd.letValue [a.code,b.code] ∧
      result.proof = app ``WordFrontendFacts.letValue ([a.code,b.code] ++ p.args ++
        [first,.lam binder word nextBody .default,a.checked.proof,.lam binder word b.checked.proof .default]) := by
  obtain ⟨target,nextTyped,nextProof⟩ := bindValue_next_typed inputs closed stable wordDeclared consDeclared right
  have typed := letValue_typed inputs (left.inProofCasts embeds) (target.mono embeds)
    (nextTyped.mono embeds) nextProof beta registered
  exact finish_cast_complete
    (bodyExpected_represents inputs
      (app_represents (.constant rfl) (.cons a.represented.property (.cons b.represented.property .nil)))
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
    {b : Piece env (wordType::ctx) {p.lift with locals := .bvar 0 :: p.lift.locals} nextBody bodyExpected}
    (right : BodyCasts (inputs.nextWord closed wordDeclared consDeclared) b casts proofCasts)
    (beta : proofCasts ctx (bindValueNextActual inputs b.represented.val right.sourceCore.val)
      (bindValueContinuationType inputs b.represented.val (.lam wordType right.sourceCore.val)))
    (registered : env.constants ``WordFrontendFacts.letValue = some ⟨0,letValueSignature⟩)
    (constructor : env.constants ``HybridWord.Cmd.letValue = some ⟨0,bindValueConstructor⟩)
    (coverage : Conversion.Covers conv 0 proofCasts) (exposure : Exposure env)
    (binder : Lean.Name) (nondep : Bool) (scalarCall : PieceParser env scalarExpected) (readCall : PieceParser env readExpected)
    (stepCall : StepParser env) (bodyCall : PieceParser env bodyExpected)
    (firstParsed : scalarCall ctx p first = some a)
    (nextParsed : bodyCall (wordType::ctx) {p.lift with locals := .bvar 0 :: p.lift.locals}
      nextBody = some b) :
    ∃ piece, bodyStep env conv exposure scalarCall readCall stepCall bodyCall ctx p
      (letValueSource binder first nextBody nondep) = some piece ∧
      Nonempty (BodyCasts inputs piece casts proofCasts) := by
  obtain ⟨artifact,checked,typed,_,_⟩ := letValue_finish inputs closed stable embeds wordDeclared consDeclared
    left right beta registered coverage exposure binder nondep
  let code := ClosedTerm.app ``HybridWord.Cmd.letValue [a.closedTerm,b.closedTerm]
  let piece : Piece env ctx p (letValueSource binder first nextBody nondep) bodyExpected :=
    ⟨code.val,artifact,code.closed,code.represented⟩
  obtain ⟨_,nextTyped,_⟩ := bindValue_next_typed inputs closed stable wordDeclared consDeclared right
  have sourceTyped := CastTyping.checkedApplication nextTyped left.value
  simp only [optionType,stateType,VExpr.inst] at sourceTyped
  refine ⟨piece,?_,⟨⟨⟨_,.letE (.constant rfl) left.sourceCore.property
    right.sourceCore.property⟩,sourceTyped,?_,typed⟩⟩⟩
  · have wordSame := sameTerm_complete (a := word) (b := word)
      (Represents.constant rfl) (Represents.constant rfl)
    have wordNotState : sameTerm word state = false := rfl
    have wordCompatible : compatible env conv ctx word word = true := by
      simp only [compatible,wordSame]; rfl
    have translated : translate word = some ⟨wordType,Represents.constant rfl⟩ := rfl
    simp only [bodyStep,letValueSource]
    simp [wordNotState,wordCompatible,translated,firstParsed,nextParsed,
      ClosedTerm.app,Piece.closedTerm,code,piece,app,letValueSource] at checked ⊢
    simp only [checked,Option.bind_some]
  · obtain ⟨target,_,_⟩ := bindValue_next_typed inputs closed stable wordDeclared consDeclared right
    have fact : CastTyping env 0 casts ctx (.const ``HybridWord.Cmd.letValue []) bindValueConstructor :=
      .constant constructor (by simp) rfl
    have first := CastTyping.application fact left.target
    simp only [bindValueConstructor,cmdType,VExpr.inst] at first
    exact .application first target


theorem letValue_step_complete (inputs : InputsTyped env ctx p)
    (closed : ClosedConstantTypes env) (stable : ClosedCasts casts)
    (embeds : ∀ scope a b, casts scope a b → proofCasts scope a b)
    (wordDeclared : env.constants ``HybridWord.Word = some ⟨0,.sort (.succ .zero)⟩)
    (consDeclared : env.constants ``List.cons = some consSignature)
    {a : Piece env ctx p first scalarExpected} (left : ScalarCasts inputs a casts)
    {b : Piece env (wordType::ctx) {p.lift with locals := .bvar 0 :: p.lift.locals} nextBody bodyExpected}
    (right : BodyCasts (inputs.nextWord closed wordDeclared consDeclared) b casts proofCasts)
    (beta : proofCasts ctx (bindValueNextActual inputs b.represented.val right.sourceCore.val)
      (bindValueContinuationType inputs b.represented.val (.lam wordType right.sourceCore.val)))
    (registered : env.constants ``WordFrontendFacts.letValue = some ⟨0,letValueSignature⟩)
    (constructor : env.constants ``HybridWord.Cmd.letValue = some ⟨0,bindValueConstructor⟩)
    (coverage : Conversion.Covers conv 0 proofCasts) (exposure : Exposure env)
    (binder : Lean.Name) (nondep : Bool) (scalarCall : PieceParser env scalarExpected) (readCall : PieceParser env readExpected)
    (stepCall : StepParser env) (bodyCall : PieceParser env bodyExpected)
    (firstParsed : scalarCall ctx p first = some a)
    (nextParsed : bodyCall (wordType::ctx) {p.lift with locals := .bvar 0 :: p.lift.locals}
      nextBody = some b) :
    ∃ piece, bodyStep env conv exposure scalarCall readCall stepCall bodyCall ctx p
      (letValueSource binder first nextBody nondep) = some piece ∧
      Nonempty (BodyCasts inputs piece casts proofCasts) := by
  exact letValue_step_split_complete inputs closed stable embeds wordDeclared consDeclared
    (left.mapProofs embeds) right beta registered constructor coverage exposure binder nondep scalarCall readCall stepCall bodyCall firstParsed nextParsed

end IRComparison.WordFrontend.Certificate
