import IRComparison.Frontend.WordBodyCompleteness

/-! Successful composition of an Option-valued read and its value continuation.
The input is the ordinary elaborated Lean bind, not a new source language. -/
namespace IRComparison.WordFrontend.Certificate
open Lean4Lean LeanTyped LeanTypeInference
variable {casts proofCasts : TypeCasts} [Arithmetic.Includes casts] [Arithmetic.Includes proofCasts]
set_option maxHeartbeats 800000

def valueBindHeader : VExpr := optionBindHeader wordType stateType

theorem valueBind_represents : Represents (bindHead word state) valueBindHeader := by
  exact .app (.app (.app (.app (.constant rfl) (.constant rfl))
    (.app (.app (.constant rfl) (.constant rfl)) (.constant rfl))) (.constant rfl)) (.constant rfl)

theorem valueBind_inst (v : VExpr) (k : Nat) : valueBindHeader.inst v k = valueBindHeader :=
  (valueBind_represents.closed 0 rfl).instN_eq (Nat.zero_le k)

def bindValueFirstPremise : VExpr := equalValues (optionType wordType)
  (scalarValue (.bvar 6) (.bvar 5) (.bvar 4) (.bvar 3) (.bvar 2) (.bvar 8)) (.bvar 1)
def bindValueNextPremise : VExpr := .forallE wordType
  (equalValues (optionType stateType)
    (bodyValue (.bvar 8) (.bvar 7) (.bvar 6) (.bvar 9) (.bvar 5)
      (applications (.const ``List.cons [.zero]) [wordType,.bvar 0,.bvar 4]))
    (.app (.bvar 2) (.bvar 0)))
def bindValueResult : VExpr := equalValues (optionType stateType)
  (bodyValue (.bvar 8) (.bvar 7) (.bvar 6)
    (applications (.const ``HybridWord.Cmd.letValue []) [.bvar 10,.bvar 9]) (.bvar 5) (.bvar 4))
  (applications valueBindHeader [.bvar 3,.bvar 2])
def bindValueSignature : VExpr := .forallE exprType (.forallE cmdType
  (inputsType (.forallE (optionType wordType)
    (.forallE (.forallE wordType (optionType stateType))
      (.forallE bindValueFirstPremise (.forallE bindValueNextPremise bindValueResult))))))

def bindValueContinuationType (inputs : InputsTyped env ctx p) (b next : VExpr) : VExpr :=
  .forallE wordType (equalValues (optionType stateType)
    (bodyValue inputs.i.val.lift inputs.x.val.lift inputs.y.val.lift b.lift
      inputs.s.val.lift (applications (.const ``List.cons [.zero]) [wordType,.bvar 0,inputs.ls.val.lift]))
    (.app next.lift (.bvar 0)))

theorem bindValue_typed (inputs : InputsTyped env ctx p)
    {a : Piece env ctx p first readExpected} (left : Read.ReadCasts inputs a casts)
    (rightTarget : CastTyping env 0 casts ctx b cmdType)
    (nextTyped : CheckedTyping env 0 casts ctx next (.forallE wordType (optionType stateType)))
    (nextProof : CastTyping env 0 casts ctx proofNext actual)
    (beta : casts ctx actual (bindValueContinuationType inputs b next))
    (registered : env.constants ``WordFrontendFacts.bindValue = some ⟨0,bindValueSignature⟩) :
    CastTyping env 0 casts ctx
      (applications (.const ``WordFrontendFacts.bindValue [])
        ([a.represented.val,b] ++ inputs.args ++
          [left.sourceCore.val,next,a.checked.proofCore.val,proofNext]))
      (equalValues (optionType stateType)
        (bodyValue inputs.i.val inputs.x.val inputs.y.val
          (applications (.const ``HybridWord.Cmd.letValue []) [a.represented.val,b]) inputs.s.val inputs.ls.val)
        (applications valueBindHeader [left.sourceCore.val,next])) := by
  have fact : CastTyping env 0 casts ctx (.const ``WordFrontendFacts.bindValue []) bindValueSignature :=
    .constant (levels := []) registered (by simp) rfl
  have a1 := CastTyping.application fact left.target
  simp only [bindValueSignature,inputsType,exprType,cmdType,wordType,stateType,wordsType,optionType,VExpr.inst] at a1
  have a2 := CastTyping.application a1 rightTarget
  simp only [VExpr.inst] at a2
  have a3 := inputs.apply_casts a2
  simp only [InputsTyped.instantiate,bindValueFirstPremise,bindValueNextPremise,bindValueResult,
    bodyValue,scalarValue,equalValues,optionType,stateType,wordType,applications,Nat.reduceAdd,
    ← VExpr.lift_instN_lo,VExpr.inst_lift,valueBind_inst,VExpr.inst,
    VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] at a3
  have a4 := CastTyping.checkedApplication a3 left.value
  simp only [Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst_lift,valueBind_inst,VExpr.inst,
    VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] at a4
  have a5 := CastTyping.checkedApplication a4 nextTyped
  simp only [Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst_lift,valueBind_inst,VExpr.inst,
    VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] at a5
  have a6 := CastTyping.application a5 left.equality
  simp only [Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst_lift,valueBind_inst,VExpr.inst,
    VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] at a6
  have cast := beta
  simp only [bindValueContinuationType,bodyValue,scalarValue,equalValues,applications,optionType,wordType,stateType] at cast
  simpa only [InputsTyped.args,applications,List.cons_append,List.nil_append,bodyValue,
    equalValues,optionType,wordType,stateType,Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst_lift,
    valueBind_inst,VExpr.inst,VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] using
    CastTyping.convertedApplication a6 nextProof cast

def bindValueNextActual (inputs : InputsTyped env ctx p) (b source : VExpr) : VExpr :=
  .forallE wordType (equalValues (optionType stateType)
    (bodyValue inputs.i.val.lift inputs.x.val.lift inputs.y.val.lift b.lift
      inputs.s.val.lift (applications (.const ``List.cons [.zero]) [wordType,.bvar 0,inputs.ls.val.lift])) source)

theorem bindValue_next_typed (inputs : InputsTyped env ctx p)
    (closed : ClosedConstantTypes env) (stable : ClosedCasts casts)
    (wordDeclared : env.constants ``HybridWord.Word = some ⟨0,.sort (.succ .zero)⟩)
    (consDeclared : env.constants ``List.cons = some consSignature)
    {b : Piece env (wordType::ctx) {p.lift with locals := .bvar 0 :: p.lift.locals} nextBody bodyExpected}
    (right : BodyCasts (inputs.nextWord closed wordDeclared consDeclared) b casts proofCasts) :
    CastTyping env 0 casts ctx b.represented.val cmdType ∧
    CastTyping env 0 casts ctx (.lam wordType right.sourceCore.val)
      (.forallE wordType (optionType stateType)) ∧
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

def bindValueSource (first next : Lean.Expr) : Lean.Expr := Lean.mkApp2 (bindHead word state) first next

theorem bindValue_finish (inputs : InputsTyped env ctx p)
    (closed : ClosedConstantTypes env) (stable : ClosedCasts casts)
    (embeds : ∀ scope a b, casts scope a b → proofCasts scope a b)
    (wordDeclared : env.constants ``HybridWord.Word = some ⟨0,.sort (.succ .zero)⟩)
    (consDeclared : env.constants ``List.cons = some consSignature)
    {a : Piece env ctx p first readExpected} (left : Read.ReadCasts inputs a casts proofCasts)
    {b : Piece env (wordType::ctx) {p.lift with locals := .bvar 0 :: p.lift.locals} nextBody bodyExpected}
    (right : BodyCasts (inputs.nextWord closed wordDeclared consDeclared) b casts proofCasts)
    (beta : proofCasts ctx (bindValueNextActual inputs b.represented.val right.sourceCore.val)
      (bindValueContinuationType inputs b.represented.val (.lam wordType right.sourceCore.val)))
    (registered : env.constants ``WordFrontendFacts.bindValue = some ⟨0,bindValueSignature⟩)
    (coverage : Conversion.Covers conv 0 proofCasts) (exposure : Exposure env)
    (binder : Lean.Name) (info : Lean.BinderInfo) :
    ∃ result, finish env conv exposure ctx
      (bodyExpected p (app ``HybridWord.Cmd.letValue [a.code,b.code])
        (bindValueSource first (.lam binder word nextBody info)))
      (app ``HybridWord.Cmd.letValue [a.code,b.code])
      (app ``WordFrontendFacts.bindValue ([a.code,b.code] ++ p.args ++
        [first,.lam binder word nextBody info,a.checked.proof,.lam binder word b.checked.proof info]))
      (a.checked.known.orElse b.checked.known) = some result ∧
      CastTyping env 0 proofCasts ctx result.proofCore.val result.core.val ∧
      result.code = app ``HybridWord.Cmd.letValue [a.code,b.code] ∧
      result.proof = app ``WordFrontendFacts.bindValue ([a.code,b.code] ++ p.args ++
        [first,.lam binder word nextBody info,a.checked.proof,.lam binder word b.checked.proof info]) := by
  obtain ⟨target,nextTyped,nextProof⟩ := bindValue_next_typed inputs closed stable wordDeclared consDeclared right
  have typed := bindValue_typed inputs (⟨left.sourceCore,left.value.mono embeds,left.target.mono embeds,left.proof⟩ : Read.ReadCasts inputs a proofCasts) (target.mono embeds)
    (.exact (nextTyped.mono embeds)) nextProof beta registered
  exact finish_cast_complete
    (bodyExpected_represents inputs
      (app_represents (.constant rfl) (.cons a.represented.property (.cons b.represented.property .nil)))
      (.app (.app valueBind_represents left.sourceCore.property) (.lam (.constant rfl) right.sourceCore.property)))
    (app_represents (.constant rfl) (.cons a.represented.property (.cons b.represented.property
      (.cons inputs.i.property (.cons inputs.x.property (.cons inputs.y.property
        (.cons inputs.s.property (.cons inputs.ls.property (.cons left.sourceCore.property
          (.cons (.lam (.constant rfl) right.sourceCore.property)
            (.cons a.checked.proofCore.property (.cons (.lam (.constant rfl) b.checked.proofCore.property) .nil))))))))))))
    typed ((known_casts a.checked left.proof).orElse (known_casts b.checked right.proof))
    coverage exposure _

def bindValueConstructor : VExpr := .forallE exprType (.forallE cmdType cmdType)

/-- Successful composition by the real body parser. The only additional
certificate conversion is the explicitly displayed continuation beta rule;
no successful typechecker execution is assumed. -/
theorem bindValue_step_complete_code (inputs : InputsTyped env ctx p)
    (closed : ClosedConstantTypes env) (stable : ClosedCasts casts)
    (embeds : ∀ scope a b, casts scope a b → proofCasts scope a b)
    (wordDeclared : env.constants ``HybridWord.Word = some ⟨0,.sort (.succ .zero)⟩)
    (consDeclared : env.constants ``List.cons = some consSignature)
    {a : Piece env ctx p first readExpected} (left : Read.ReadCasts inputs a casts proofCasts)
    {b : Piece env (wordType::ctx) {p.lift with locals := .bvar 0 :: p.lift.locals} nextBody bodyExpected}
    (right : BodyCasts (inputs.nextWord closed wordDeclared consDeclared) b casts proofCasts)
    (beta : proofCasts ctx (bindValueNextActual inputs b.represented.val right.sourceCore.val)
      (bindValueContinuationType inputs b.represented.val (.lam wordType right.sourceCore.val)))
    (registered : env.constants ``WordFrontendFacts.bindValue = some ⟨0,bindValueSignature⟩)
    (constructor : env.constants ``HybridWord.Cmd.letValue = some ⟨0,bindValueConstructor⟩)
    (coverage : Conversion.Covers conv 0 proofCasts) (exposure : Exposure env)
    (bindLibrary : BindSignatures env)
    (stateDeclared : env.constants ``HybridWord.State = some ⟨0,.sort (.succ .zero)⟩)
    (binder : Lean.Name) (info : Lean.BinderInfo)
    (scalarCall : ∀ ctx p source, Option (Piece env ctx p source scalarExpected))
    (readCall : ∀ ctx p source, Option (Piece env ctx p source readExpected))
    (stepCall : ∀ ctx source, Option (StepPiece env ctx source))
    (bodyCall : ∀ ctx p source, Option (Piece env ctx p source bodyExpected))
    (firstParsed : readCall ctx p first = some a)
    (nextParsed : bodyCall (wordType::ctx) {p.lift with locals := .bvar 0 :: p.lift.locals} nextBody = some b) :
    ∃ piece, bodyStep env conv exposure scalarCall readCall stepCall bodyCall ctx p
      (bindValueSource first (.lam binder word nextBody info)) = some piece ∧
      Nonempty (BodyCasts inputs piece casts proofCasts) ∧
      piece.code = app ``HybridWord.Cmd.letValue [a.code,b.code] := by
  obtain ⟨artifact,checked,typed,_,_⟩ := bindValue_finish inputs closed stable embeds wordDeclared consDeclared
    left right beta registered coverage exposure binder info
  let code := ClosedTerm.app ``HybridWord.Cmd.letValue [a.closedTerm,b.closedTerm]
  let piece : Piece env ctx p (bindValueSource first (.lam binder word nextBody info)) bodyExpected :=
    ⟨code.val,artifact,code.closed,code.represented⟩
  obtain ⟨_,nextTyped,_⟩ := bindValue_next_typed inputs closed stable wordDeclared consDeclared right
  have applied := CastTyping.checkedApplication ((bindLibrary.header_typed
    (domain := wordType) (result := stateType)
    (.constant wordDeclared (by simp) rfl) (.constant stateDeclared (by simp) rfl)
    (by trivial) (by trivial)).withCasts casts) left.value
  simp only [optionType,wordType,stateType,VExpr.inst] at applied
  have sourceTyped := CastTyping.application applied nextTyped
  refine ⟨piece,?_,⟨⟨⟨_,.app (.app valueBind_represents left.sourceCore.property)
    (.lam (.constant rfl) right.sourceCore.property)⟩,sourceTyped,?_,typed⟩⟩,rfl⟩
  · have wordSame := sameTerm_complete (a := word) (b := word)
      (Represents.constant rfl) (Represents.constant rfl)
    have wordNotState : sameTerm word state = false := rfl
    have wordCompatible : compatible env conv ctx word word = true := by
      simp only [compatible,wordSame]; rfl
    have translated : translate word = some ⟨wordType,Represents.constant rfl⟩ := rfl
    have reduced : leadingLet (bindValueSource first (.lam binder word nextBody info)) = none := rfl
    have head : (bindValueSource first (.lam binder word nextBody info)).getAppFn.constName? = some ``Bind.bind := rfl
    have args : (bindValueSource first (.lam binder word nextBody info)).getAppArgs.toList =
      [.const ``Option [.zero], Lean.mkAppN (.const ``Monad.toBind [.zero,.zero])
        #[.const ``Option [.zero],.const ``instMonadOption [.zero]],word,state,first,
        .lam binder word nextBody info] := rfl
    simp only [bodyStep,reduced,head,args]
    simp [wordNotState,wordCompatible,translated,firstParsed,nextParsed,
      ClosedTerm.app,Piece.closedTerm,code,piece,app,bindValueSource,Lean.mkApp2,Lean.mkAppB] at checked ⊢
    simp only [checked,Option.bind_some]
  · obtain ⟨target,_,_⟩ := bindValue_next_typed inputs closed stable wordDeclared consDeclared right
    have fact : CastTyping env 0 casts ctx (.const ``HybridWord.Cmd.letValue []) bindValueConstructor :=
      .constant constructor (by simp) rfl
    have first := CastTyping.application fact left.target
    simp only [bindValueConstructor,cmdType,VExpr.inst] at first
    exact .application first target

theorem bindValue_step_complete (inputs : InputsTyped env ctx p)
    (closed : ClosedConstantTypes env) (stable : ClosedCasts casts)
    (embeds : ∀ scope a b, casts scope a b → proofCasts scope a b)
    (wordDeclared : env.constants ``HybridWord.Word = some ⟨0,.sort (.succ .zero)⟩)
    (consDeclared : env.constants ``List.cons = some consSignature)
    {a : Piece env ctx p first readExpected} (left : Read.ReadCasts inputs a casts proofCasts)
    {b : Piece env (wordType::ctx) {p.lift with locals := .bvar 0 :: p.lift.locals} nextBody bodyExpected}
    (right : BodyCasts (inputs.nextWord closed wordDeclared consDeclared) b casts proofCasts)
    (beta : proofCasts ctx (bindValueNextActual inputs b.represented.val right.sourceCore.val)
      (bindValueContinuationType inputs b.represented.val (.lam wordType right.sourceCore.val)))
    (registered : env.constants ``WordFrontendFacts.bindValue = some ⟨0,bindValueSignature⟩)
    (constructor : env.constants ``HybridWord.Cmd.letValue = some ⟨0,bindValueConstructor⟩)
    (coverage : Conversion.Covers conv 0 proofCasts) (exposure : Exposure env)
    (bindLibrary : BindSignatures env)
    (stateDeclared : env.constants ``HybridWord.State = some ⟨0,.sort (.succ .zero)⟩)
    (binder : Lean.Name) (info : Lean.BinderInfo)
    (scalarCall : ∀ ctx p source, Option (Piece env ctx p source scalarExpected))
    (readCall : ∀ ctx p source, Option (Piece env ctx p source readExpected))
    (stepCall : ∀ ctx source, Option (StepPiece env ctx source))
    (bodyCall : ∀ ctx p source, Option (Piece env ctx p source bodyExpected))
    (firstParsed : readCall ctx p first = some a)
    (nextParsed : bodyCall (wordType::ctx) {p.lift with locals := .bvar 0 :: p.lift.locals} nextBody = some b) :
    ∃ piece, bodyStep env conv exposure scalarCall readCall stepCall bodyCall ctx p
      (bindValueSource first (.lam binder word nextBody info)) = some piece ∧
      Nonempty (BodyCasts inputs piece casts proofCasts) := by
  obtain ⟨piece,success,typed,_⟩ := bindValue_step_complete_code inputs closed stable embeds wordDeclared
    consDeclared left right beta registered constructor coverage exposure bindLibrary stateDeclared binder info
    scalarCall readCall stepCall bodyCall firstParsed nextParsed
  exact ⟨piece,success,typed⟩

end IRComparison.WordFrontend.Certificate
