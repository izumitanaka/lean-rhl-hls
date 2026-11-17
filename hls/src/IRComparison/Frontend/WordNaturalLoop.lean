import IRComparison.Frontend.WordStructuralLoop
import IRComparison.Frontend.WordNaturalScope

/-! The two existing native List.range loop forms. This module describes
their library signatures and composes their generated certificates. It does
not introduce a source DSL or expand the runtime iterations. -/
namespace IRComparison.WordFrontend.NaturalLoop
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic

set_option maxHeartbeats 1500000

inductive Kind where
  | forIn | fold
  deriving DecidableEq

def Kind.first : Kind → Lean.Name
  | .forIn => ``Nat | .fold => ``HybridWord.State
def Kind.second : Kind → Lean.Name
  | .forIn => ``HybridWord.State | .fold => ``Nat
def Kind.result : Kind → VExpr
  | .forIn => Step.stepState | .fold => stateType
def Kind.functionType (kind : Kind) : VExpr :=
  .forallE (.const kind.first [])
    (.forallE (.const kind.second []) (optionType kind.result))
def Kind.fact : Kind → Lean.Name
  | .forIn => ``WordLoopFacts.forIn | .fold => ``WordFrontendFacts.forRange
def Kind.index : Kind → VExpr
  | .forIn => .bvar 1 | .fold => .bvar 0
def Kind.state : Kind → VExpr
  | .forIn => .bvar 0 | .fold => .bvar 1
def Kind.lhs (kind : Kind) (value : VExpr) : VExpr :=
  match kind with | .forIn => Step.lifted value | .fold => value
def Kind.equation (kind : Kind) (value original : VExpr) : VExpr :=
  equalValues (optionType kind.result) (kind.lhs value) original

def foldHeader : VExpr := applications (.const ``List.foldlM [.zero,.zero,.zero])
  [.const ``Option [.zero],.const ``instMonadOption [.zero],stateType,natType]
def nativeFoldHeader : Lean.Expr := Lean.mkApp4 (.const ``List.foldlM [.zero,.zero,.zero])
  (.const ``Option [.zero]) (.const ``instMonadOption [.zero]) state (.const ``Nat [])
def Kind.header : Kind → VExpr
  | .forIn => For.Header.At.header ``Nat | .fold => foldHeader
def Kind.nativeHeader : Kind → Lean.Expr
  | .forIn => For.Header.At.nativeHeader ``Nat | .fold => nativeFoldHeader

theorem Kind.header_represents (kind : Kind) : Represents kind.nativeHeader kind.header := by
  cases kind with
  | forIn => exact For.Header.At.header_represents _
  | fold => repeat first | apply Represents.app | exact Represents.constant rfl

theorem Kind.header_closed (kind : Kind) : kind.header.ClosedN 0 := by
  exact kind.header_represents.closed 0 (by cases kind <;> rfl)

theorem Kind.header_inst (kind : Kind) (value : VExpr) (n : Nat) :
    kind.header.inst value n = kind.header := kind.header_closed.instN_eq (Nat.zero_le n)

def range (count : VExpr) : VExpr := .app (.const ``List.range []) (Read.wordIndexCore count)
def nativeRange (count : Lean.Expr) : Lean.Expr :=
  .app (.const ``List.range []) (Read.wordIndex count)

def Kind.loop (kind : Kind) (count initial fn : VExpr) : VExpr :=
  match kind with
  | .forIn => applications kind.header [range count,initial,fn]
  | .fold => applications kind.header [fn,initial,range count]

def Kind.source (kind : Kind) (count initial fn : Lean.Expr) : Lean.Expr :=
  match kind with
  | .forIn => Lean.mkApp3 kind.nativeHeader (nativeRange count) initial fn
  | .fold => Lean.mkApp3 kind.nativeHeader fn initial (nativeRange count)

theorem range_represents (represented : Represents count core) :
    Represents (nativeRange count) (range core) :=
  .app (.constant rfl) (.app (.app (.constant rfl) width_represents) represented)

theorem Kind.source_represents (kind : Kind)
    (count : Represents n nc) (initial : Represents s sc) (fn : Represents f fc) :
    Represents (kind.source n s f) (kind.loop nc sc fc) := by
  cases kind with
  | forIn => exact .app (.app (.app (Kind.header_represents .forIn) (range_represents count)) initial) fn
  | fold => exact .app (.app (.app (Kind.header_represents .fold) fn) initial) (range_represents count)

def countPremise : VExpr := equalValues (optionType wordType)
  (scalarValue (.bvar 6) (.bvar 5) (.bvar 4) (.bvar 3) (.bvar 2) (.bvar 8))
  (someValue wordType (.bvar 1))

def Kind.bodyPremise (kind : Kind) : VExpr :=
  .forallE (.const kind.first []) (.forallE (.const kind.second [])
    (kind.equation
      (bodyValue (.bvar 9) (.bvar 8) (.bvar 7) (.bvar 10) kind.state
        (wordCons (NaturalScope.index kind.index) (.bvar 5)))
      (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0))))

def Kind.resultType (kind : Kind) : VExpr := equalValues (optionType stateType)
  (bodyValue (.bvar 8) (.bvar 7) (.bvar 6)
    (applications (.const ``HybridWord.Cmd.forRange []) [.bvar 10,.bvar 9]) (.bvar 5) (.bvar 4))
  (kind.loop (.bvar 3) (.bvar 5) (.bvar 2))

def Kind.signature (kind : Kind) : VExpr :=
  .forallE exprType (.forallE cmdType
    (inputsType (.forallE wordType (.forallE kind.functionType
      (.forallE countPremise (.forallE kind.bodyPremise kind.resultType))))))

def constructorSignature : VExpr := .forallE exprType (.forallE cmdType cmdType)
def rangeSignature : VExpr := .forallE natType (For.Header.At.listType ``Nat)

def foldSignature : VConstant := ⟨3,(.forallE (.forallE (.sort (.succ (.param 0)))
 (.sort (.succ (.param 1))))
 (.forallE (.app (.const ``Monad [(.param 0),(.param 1)]) (.bvar 0))
 (.forallE (.sort (.succ (.param 0)))
 (.forallE (.sort (.succ (.param 2)))
 (.forallE (.forallE (.bvar 1)
 (.forallE (.bvar 1)
 (.app (.bvar 5) (.bvar 3))))
 (.forallE (.bvar 2)
 (.forallE (.app (.const ``List [(.param 2)]) (.bvar 2))
 (.app (.bvar 6) (.bvar 4)))))))))⟩

structure Signatures (env : VEnv) : Prop where
  ofNat : env.constants ``BitVec.ofNat = some ⟨0,NaturalScope.ofNatSignature⟩
  range : env.constants ``List.range = some ⟨0,rangeSignature⟩
  fold : env.constants ``List.foldlM = some foldSignature
  fact : ∀ kind : Kind, env.constants kind.fact = some ⟨0,kind.signature⟩
  constructor : env.constants ``HybridWord.Cmd.forRange = some ⟨0,constructorSignature⟩

def Kind.headerType (kind : Kind) : VExpr := match kind with
  | .forIn => For.Header.At.headerType ``Nat
  | .fold => .forallE kind.functionType
      (.forallE stateType (.forallE (For.Header.At.listType ``Nat) (optionType stateType)))

theorem header_typed (library : Signatures env) (arithmetic : Arithmetic.Signatures env)
    (iterator : For.Header.Signatures env) (kind : Kind) :
    CastTyping env 0 (SourceCasts env) ctx kind.header kind.headerType := by
  cases kind with
  | forIn => exact For.Header.At.header_typed iterator ``Nat arithmetic.natural
  | fold =>
    have fact : CastTyping env 0 (SourceCasts env) ctx (.const ``List.foldlM [.zero,.zero,.zero])
        (foldSignature.type.instL [.zero,.zero,.zero]) :=
      .constant library.fold (by simp [VLevel.WF]) rfl
    have a1 := CastTyping.application fact (iterator.option_typed.withCasts _)
    simp only [foldSignature,VExpr.instL,VLevel.inst,VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,
      VExpr.instVar_lower,Nat.reduceAdd] at a1
    have monad : CastTyping env 0 (SourceCasts env) ctx (.const ``instMonadOption [.zero])
        (optionMonadSignature.type.instL [.zero]) :=
      .constant iterator.monad (by simp [VLevel.WF]) rfl
    have a2 := CastTyping.application a1 monad
    simp only [VExpr.inst] at a2
    have stateTyped : CastTyping env 0 (SourceCasts env) ctx stateType (.sort (.succ .zero)) :=
      .constant iterator.state (by simp) rfl
    have a3 := CastTyping.application a2 stateTyped
    simp only [VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower,stateType] at a3
    have natTyped : CastTyping env 0 (SourceCasts env) ctx natType (.sort (.succ .zero)) :=
      .constant arithmetic.natural (by simp) rfl
    simpa only [Kind.header,Kind.headerType,Kind.functionType,Kind.first,Kind.second,Kind.result,
      foldHeader,applications,stateType,natType,optionType,For.Header.At.listType,VExpr.inst,
      VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower] using CastTyping.application a3 natTyped

theorem source_typed_state (library : Signatures env) (arithmetic : Arithmetic.Signatures env)
    (iterator : For.Header.Signatures env) (reads : Read.Signatures env)
    (stateTyped : CastTyping env 0 (SourceCasts env) ctx st stateType) (kind : Kind)
    (count : CheckedTyping env 0 (SourceCasts env) ctx n wordType)
    (fnTyped : CastTyping env 0 (SourceCasts env) ctx fn kind.functionType) :
    CastTyping env 0 (SourceCasts env) ctx (kind.loop n st fn) (optionType stateType) := by
  have rangeHead : CastTyping env 0 (SourceCasts env) ctx (.const ``List.range []) rangeSignature :=
    .constant library.range (by simp) rfl
  have rangeTyped := CastTyping.application rangeHead (reads.word_index_typed arithmetic count)
  simp only [rangeSignature,For.Header.At.listType,VExpr.inst] at rangeTyped
  have header := header_typed (ctx := ctx) library arithmetic iterator kind
  cases kind with
  | forIn =>
    have a1 := CastTyping.application header rangeTyped
    simp only [Kind.headerType,For.Header.At.headerType,For.Header.At.functionType,
      For.Header.At.listType,optionType,stateType,Step.stepState,VExpr.inst] at a1
    have a2 := CastTyping.application a1 stateTyped
    simp only [VExpr.inst] at a2
    exact .application a2 fnTyped
  | fold =>
    have a1 := CastTyping.application header fnTyped
    simp only [Kind.headerType,Kind.functionType,Kind.first,Kind.second,Kind.result,
      For.Header.At.listType,optionType,stateType,VExpr.inst] at a1
    have a2 := CastTyping.application a1 stateTyped
    simp only [VExpr.inst] at a2
    exact .application a2 rangeTyped

/-- Compatibility wrapper for proof-producing callers with a complete input environment. -/
theorem source_typed (library : Signatures env) (arithmetic : Arithmetic.Signatures env)
    (iterator : For.Header.Signatures env) (reads : Read.Signatures env)
    (inputs : InputsTyped env ctx p) (kind : Kind)
    (count : CheckedTyping env 0 (SourceCasts env) ctx n wordType)
    (fnTyped : CastTyping env 0 (SourceCasts env) ctx fn kind.functionType) :
    CastTyping env 0 (SourceCasts env) ctx (kind.loop n inputs.s.val fn) (optionType stateType) :=
  source_typed_state library arithmetic iterator reads (inputs.hs.withCasts _) kind count fnTyped

def Kind.continuationType (kind : Kind) (inputs : InputsTyped env ctx p) (code fn : VExpr) : VExpr :=
  .forallE (.const kind.first []) (.forallE (.const kind.second [])
    (kind.equation
      (bodyValue inputs.i.val.lift.lift inputs.x.val.lift.lift inputs.y.val.lift.lift
        code.lift.lift kind.state (wordCons (NaturalScope.index kind.index) inputs.ls.val.lift.lift))
      (.app (.app fn.lift.lift (.bvar 1)) (.bvar 0))))

theorem fact_typed (inputs : InputsTyped env ctx p) [Arithmetic.Includes casts]
    (kind : Kind) {count : Piece env ctx p n scalarExpected}
    (value : ScalarCasts inputs count casts)
    (bodyTyped : CastTyping env 0 casts ctx code cmdType)
    (functionTyped : CastTyping env 0 casts ctx fn kind.functionType)
    (proofTyped : CastTyping env 0 casts ctx proof actual)
    (beta : casts ctx actual (kind.continuationType inputs code fn))
    (registered : env.constants kind.fact = some ⟨0,kind.signature⟩) :
    CastTyping env 0 casts ctx
      (applications (.const kind.fact [])
        ([count.represented.val,code] ++ inputs.args ++
          [value.sourceCore.val,fn,count.checked.proofCore.val,proof]))
      (equalValues (optionType stateType)
        (bodyValue inputs.i.val inputs.x.val inputs.y.val
          (applications (.const ``HybridWord.Cmd.forRange []) [count.represented.val,code])
          inputs.s.val inputs.ls.val)
        (kind.loop value.sourceCore.val inputs.s.val fn)) := by
  have fact : CastTyping env 0 casts ctx (.const kind.fact []) kind.signature :=
    by
      have h := CastTyping.constant (casts := casts) (ctx := ctx) (U := 0) (levels := [])
        registered (by simp) rfl
      cases kind <;> simpa only [Kind.signature,Kind.functionType,Kind.first,Kind.second,Kind.result,
        Kind.bodyPremise,Kind.resultType,Kind.equation,Kind.lhs,Kind.state,Kind.index,Kind.loop,
        Kind.header,countPremise,inputsType,wordType,stateType,natType,wordsType,cmdType,exprType,
        equalValues,scalarValue,bodyValue,someValue,optionType,wordCons,NaturalScope.index,
        Step.lifted,Step.stepState,range,Read.wordIndexCore,For.Header.At.header,
        For.Header.At.forInValue,For.Header.At.listValue,For.Header.At.membershipValue,
        For.Header.At.membershipType,For.Header.At.listType,foldHeader,applications,
        VExpr.instL,VLevel.inst,List.map_nil,width_represents.instL_empty] using h
  have a1 := CastTyping.application fact value.target
  simp only [Kind.signature,inputsType,wordType,cmdType,exprType,stateType,wordsType,VExpr.inst] at a1
  have a2 := CastTyping.application a1 bodyTyped
  simp only [VExpr.inst] at a2
  have a3 := inputs.apply_casts a2
  cases kind <;>
    simp only [InputsTyped.instantiate,countPremise,Kind.bodyPremise,Kind.resultType,Kind.functionType,
      Kind.first,Kind.second,Kind.result,Kind.index,Kind.state,Kind.lhs,Kind.equation,Kind.loop,
      Kind.header,For.Header.At.header,foldHeader,range,Read.wordIndexCore,NaturalScope.index,
      wordCons,wordType,stateType,natType,wordsType,cmdType,exprType,Step.expected,Step.lifted,Step.stepState,
      optionType,equalValues,someValue,scalarValue,bodyValue,applications,
      Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst_lift,VExpr.inst,
      VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ,width_closed.instN_eq (Nat.zero_le _)] at a3
  all_goals
    have a4 := CastTyping.checkedApplication a3 value.value
    simp only [VExpr.inst,VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ,
      ← VExpr.lift_instN_lo,VExpr.inst_lift,Nat.reduceAdd,width_closed.instN_eq (Nat.zero_le _)] at a4
    have a5 := CastTyping.application a4 functionTyped
    simp only [VExpr.inst,VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ,
      ← VExpr.lift_instN_lo,VExpr.inst_lift,Nat.reduceAdd,width_closed.instN_eq (Nat.zero_le _)] at a5
    have a6 := CastTyping.application a5 value.equality
    simp only [VExpr.inst,VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ,
      ← VExpr.lift_instN_lo,VExpr.inst_lift,Nat.reduceAdd,width_closed.instN_eq (Nat.zero_le _)] at a6
    have final := CastTyping.convertedApplication a6 proofTyped beta
    simpa only [Kind.continuationType,Kind.loop,Kind.header,Kind.fact,Kind.first,Kind.second,
      Kind.result,Kind.index,Kind.state,Kind.lhs,Kind.equation,For.Header.At.header,foldHeader,
      range,Read.wordIndexCore,NaturalScope.index,wordCons,wordType,stateType,natType,wordsType,
      Step.lifted,Step.stepState,optionType,equalValues,someValue,scalarValue,bodyValue,applications,
      InputsTyped.args,List.cons_append,List.nil_append,VExpr.inst,VExpr.instVar_lower,VExpr.instVar_zero,
      VExpr.instVar_succ,← VExpr.lift_instN_lo,VExpr.inst_lift,Nat.reduceAdd,width_closed.instN_eq (Nat.zero_le _)] using final


open StructuralBody StructuralLoop

def Kind.mode : Kind → Mode
  | .forIn => .step | .fold => .body

def Kind.parameters (kind : Kind) (p : Inputs) : Inputs := match kind with
  | .forIn => NaturalScope.forInParameters p
  | .fold => NaturalScope.foldParameters p

def Kind.context (kind : Kind) (ctx : List VExpr) : List VExpr :=
  .const kind.second [] :: .const kind.first [] :: ctx

def Kind.nextInputs (kind : Kind) (inputs : InputsTyped env ctx p)
    (closed : ClosedConstantTypes env) (arithmetic : Arithmetic.Signatures env)
    (library : Signatures env) (consDeclared : env.constants ``List.cons = some consSignature) :
    InputsTyped env (kind.context ctx) (kind.parameters p) := match kind with
  | .forIn => NaturalScope.forInInputs inputs closed arithmetic library.ofNat consDeclared
  | .fold => NaturalScope.foldInputs inputs closed arithmetic library.ofNat consDeclared

def Kind.nextLocals (kind : Kind) (scope : ScalarSyntax.Locals env ctx p)
    (closed : ClosedConstantTypes env) (arithmetic : Arithmetic.Signatures env)
    (library : Signatures env) :
    ScalarSyntax.Locals env (kind.context ctx) (kind.parameters p) := match kind with
  | .forIn => NaturalScope.forInLocals scope closed arithmetic library.ofNat
  | .fold => NaturalScope.foldLocals scope closed arithmetic library.ofNat

/-- The existing body and ForInStep invariants, selected by the native iterator. -/
def ChildCasts (kind : Kind) (inputs : InputsTyped env ctx p)
    (piece : Piece env ctx p original kind.mode.expected) (casts proofCasts : TypeCasts) : Type :=
  match kind with
  | .forIn => StepCasts inputs piece casts proofCasts
  | .fold => BodyCasts inputs piece casts proofCasts

def ChildCasts.sourceCore {kind : Kind} {b : Piece env ctx p original kind.mode.expected}
    (typed : ChildCasts kind inputs b casts proofCasts) : {core // Represents original core} := by
  cases kind with
  | forIn => exact StepCasts.sourceCore typed
  | fold => exact BodyCasts.sourceCore typed

theorem ChildCasts.value {kind : Kind} {b : Piece env ctx p original kind.mode.expected}
    (typed : ChildCasts kind inputs b casts proofCasts) :
    CastTyping env 0 casts ctx typed.sourceCore.val (optionType kind.result) := by
  cases kind with
  | forIn => exact StepCasts.value typed
  | fold => exact BodyCasts.value typed

theorem ChildCasts.target {kind : Kind} {b : Piece env ctx p original kind.mode.expected}
    (typed : ChildCasts kind inputs b casts proofCasts) :
    CastTyping env 0 casts ctx b.represented.val cmdType := by
  cases kind with
  | forIn => exact StepCasts.target typed
  | fold => exact BodyCasts.target typed

theorem ChildCasts.proof {kind : Kind} {b : Piece env ctx p original kind.mode.expected}
    (typed : ChildCasts kind inputs b casts proofCasts) :
    CastTyping env 0 proofCasts ctx b.checked.proofCore.val b.checked.core.val := by
  cases kind with
  | forIn => exact StepCasts.proof typed
  | fold => exact BodyCasts.proof typed

theorem ChildCasts.equality [Arithmetic.Includes casts] [Arithmetic.Includes proofCasts] {kind : Kind} {b : Piece env ctx p original kind.mode.expected}
    (typed : ChildCasts kind inputs b casts proofCasts) :
    CastTyping env 0 proofCasts ctx b.checked.proofCore.val
      (kind.equation (bodyValue inputs.i.val inputs.x.val inputs.y.val b.represented.val
        inputs.s.val inputs.ls.val) typed.sourceCore.val) := by
  cases kind with
  | forIn => exact StepCasts.equality typed
  | fold => exact BodyCasts.equality typed

def Kind.actualPremise (kind : Kind) (inputs : InputsTyped env ctx p) (code original : VExpr) : VExpr :=
  .forallE (.const kind.first []) (.forallE (.const kind.second [])
    (kind.equation (bodyValue inputs.i.val.lift.lift inputs.x.val.lift.lift inputs.y.val.lift.lift
      code kind.state (wordCons (NaturalScope.index kind.index) inputs.ls.val.lift.lift)) original))

theorem next_typed [Arithmetic.Includes casts] [Arithmetic.Includes proofCasts] (inputs : InputsTyped env ctx p) (kind : Kind)
    (closed : ClosedConstantTypes env) (stable : ClosedCasts casts)
    (arithmetic : Arithmetic.Signatures env) (library : Signatures env)
    (stateDeclared : env.constants ``HybridWord.State = some ⟨0,.sort (.succ .zero)⟩)
    (consDeclared : env.constants ``List.cons = some consSignature)
    {b : Piece env (kind.context ctx) (kind.parameters p) original kind.mode.expected}
    (typed : ChildCasts kind (kind.nextInputs inputs closed arithmetic library consDeclared) b casts proofCasts) :
    CastTyping env 0 casts ctx b.represented.val cmdType ∧
    CastTyping env 0 casts ctx (.lam (.const kind.first []) (.lam (.const kind.second []) typed.sourceCore.val)) kind.functionType ∧
    CastTyping env 0 proofCasts ctx (.lam (.const kind.first []) (.lam (.const kind.second []) b.checked.proofCore.val))
      (kind.actualPremise inputs b.represented.val typed.sourceCore.val) := by
  have firstDeclared : env.constants kind.first = some ⟨0,.sort (.succ .zero)⟩ := by
    cases kind with | forIn => exact arithmetic.natural | fold => exact stateDeclared
  have secondDeclared : env.constants kind.second = some ⟨0,.sort (.succ .zero)⟩ := by
    cases kind with | forIn => exact stateDeclared | fold => exact arithmetic.natural
  have firstTyped : DirectTyping env 0 ctx (.const kind.first []) (.sort (.succ .zero)) :=
    .constant firstDeclared (by simp) rfl
  have secondTyped : DirectTyping env 0 (.const kind.first []::ctx) (.const kind.second []) (.sort (.succ .zero)) :=
    .constant secondDeclared (by simp) rfl
  refine ⟨typed.target.closed_context stable (b.represented.property.closed 0 b.closed) ctx,
    .lambda (firstTyped.withCasts _) (.lambda (secondTyped.withCasts _) typed.value),?_⟩
  have abstracted := CastTyping.lambda (firstTyped.withCasts proofCasts)
    (CastTyping.lambda (secondTyped.withCasts proofCasts) typed.equality)
  cases kind <;>
    simpa only [Kind.actualPremise,Kind.nextInputs,Kind.first,Kind.second,Kind.state,Kind.index,
      NaturalScope.forInInputs,NaturalScope.foldInputs,NaturalScope.retain,InputsTyped.withLocal,
      InputsTyped.nextState,InputsTyped.lift,VExpr.lift,VExpr.liftN,applications,natType,stateType,
      NaturalScope.index,wordCons] using abstracted


def Kind.nativeLambda (kind : Kind) (kn tn : Lean.Name) (ki ti : Lean.BinderInfo) (body : Lean.Expr) : Lean.Expr :=
  .lam kn (.const kind.first []) (.lam tn (.const kind.second []) body ti) ki

theorem Kind.lambda_represents (kind : Kind) {source : Lean.Expr} (represented : Represents source core) :
    Represents (kind.nativeLambda kn tn ki ti source)
      (.lam (.const kind.first []) (.lam (.const kind.second []) core)) :=
  .lam (.constant rfl) (.lam (.constant rfl) represented)

theorem finish_complete [Arithmetic.Includes casts] [Arithmetic.Includes proofCasts]
    (inputs : InputsTyped env ctx p) (kind : Kind)
    (closed : ClosedConstantTypes env) (stable : ClosedCasts casts)
    (embeds : ∀ scope a b, casts scope a b → proofCasts scope a b)
    (arithmetic : Arithmetic.Signatures env) (library : Signatures env)
    (stateDeclared : env.constants ``HybridWord.State = some ⟨0,.sort (.succ .zero)⟩)
    (consDeclared : env.constants ``List.cons = some consSignature)
    {count : Piece env ctx p n scalarExpected} (countTyped : ScalarCasts inputs count casts proofCasts)
    {b : Piece env (kind.context ctx) (kind.parameters p) original kind.mode.expected}
    (typed : ChildCasts kind (kind.nextInputs inputs closed arithmetic library consDeclared) b casts proofCasts)
    (beta : proofCasts ctx (kind.actualPremise inputs b.represented.val typed.sourceCore.val)
      (kind.continuationType inputs b.represented.val
        (.lam (.const kind.first []) (.lam (.const kind.second []) typed.sourceCore.val))))
    (coverage : Conversion.Covers conv 0 proofCasts) (exposure : Exposure env)
    (kn tn : Lean.Name) (ki ti : Lean.BinderInfo) :
    ∃ result, finish env conv exposure ctx
      (bodyExpected p (app ``HybridWord.Cmd.forRange [count.code,b.code])
        (kind.source n p.s (kind.nativeLambda kn tn ki ti original)))
      (app ``HybridWord.Cmd.forRange [count.code,b.code])
      (app kind.fact ([count.code,b.code] ++ p.args ++
        [n,kind.nativeLambda kn tn ki ti original,count.checked.proof,
          kind.nativeLambda kn tn ki ti b.checked.proof]))
      (count.checked.known.orElse b.checked.known) = some result ∧
      CastTyping env 0 proofCasts ctx result.proofCore.val result.core.val := by
  obtain ⟨target,next,proofTyped⟩ := next_typed inputs kind closed stable arithmetic library
    stateDeclared consDeclared typed
  have fact := fact_typed inputs kind (countTyped.inProofCasts embeds) (target.mono embeds)
    (next.mono embeds) proofTyped beta (library.fact kind)
  have codeRep := app_represents (Represents.constant (name := ``HybridWord.Cmd.forRange) (us := []) rfl)
    (.cons count.represented.property (.cons b.represented.property .nil))
  have fnRep := kind.lambda_represents (kn := kn) (tn := tn) (ki := ki) (ti := ti) typed.sourceCore.property
  have proofRep := kind.lambda_represents (kn := kn) (tn := tn) (ki := ki) (ti := ti) b.checked.proofCore.property
  have certificateRep := app_represents (Represents.constant (name := kind.fact) (us := []) rfl)
    (.cons count.represented.property (.cons b.represented.property
      (.cons inputs.i.property (.cons inputs.x.property (.cons inputs.y.property
        (.cons inputs.s.property (.cons inputs.ls.property (.cons countTyped.sourceCore.property
          (.cons fnRep (.cons count.checked.proofCore.property (.cons proofRep .nil)))))))))))
  obtain ⟨result,checked,proofTyped,_,_⟩ := finish_cast_complete
    (bodyExpected_represents inputs codeRep
      (kind.source_represents countTyped.sourceCore.property inputs.s.property fnRep))
    certificateRep fact ((known_casts count.checked countTyped.proof).orElse
      (known_casts b.checked typed.proof)) coverage exposure (app ``HybridWord.Cmd.forRange [count.code,b.code])
  exact ⟨result,checked,proofTyped⟩


theorem Kind.substitute_source (kind : Kind) (σ : Substitution) :
    σ.apply (kind.source n st (kind.nativeLambda kn tn ki ti original)) =
      kind.source (σ.apply n) (σ.apply st) (kind.nativeLambda kn tn ki ti ((under (under σ)).apply original)) := by
  cases kind <;> cases σ <;> rfl

theorem mapped_forRange_complete_code [Arithmetic.Includes proofCasts]
    (inputs : InputsTyped env ctx p) (kind : Kind)
    (closed : ClosedConstantTypes env)
    (embeds : ∀ scope a b, SourceCasts env scope a b → proofCasts scope a b)
    (arithmetic : Arithmetic.Signatures env) (library : Signatures env)
    (iterator : For.Header.Signatures env) (reads : Read.Signatures env)
    (stateDeclared : env.constants ``HybridWord.State = some ⟨0,.sort (.succ .zero)⟩)
    (consDeclared : env.constants ``List.cons = some consSignature)
    {count : Piece env ctx p (σ.apply n) scalarExpected} (countTyped : ScalarCasts inputs count (SourceCasts env) proofCasts)
    {b : Piece env (kind.context ctx) (kind.parameters p) ((under (under σ)).apply original) kind.mode.expected}
    (typed : ChildCasts kind (kind.nextInputs inputs closed arithmetic library consDeclared) b (SourceCasts env) proofCasts)
    (beta : proofCasts ctx (kind.actualPremise inputs b.represented.val typed.sourceCore.val)
      (kind.continuationType inputs b.represented.val
        (.lam (.const kind.first []) (.lam (.const kind.second []) typed.sourceCore.val))))
    (coverage : Conversion.Covers conv 0 proofCasts) (exposure : Exposure env)
    (kn tn : Lean.Name) (ki ti : Lean.BinderInfo)
    (current : σ.apply st = p.s)
    (countParsed : ScalarEnvironment.parse env conv exposure ctx p (σ.apply n) = some count)
    (bodyParsed : visit env conv exposure original (kind.context ctx) (kind.parameters p)
      kind.mode (under (under σ)) (underFunctions (underFunctions fs)) = some b) :
    ∃ piece, visit env conv exposure
      (kind.source n st (kind.nativeLambda kn tn ki ti original)) ctx p .body σ fs = some piece ∧
      Nonempty (BodyCasts inputs piece (SourceCasts env) proofCasts) ∧
      piece.code = app ``HybridWord.Cmd.forRange [count.code,b.code] := by
  have assembled := finish_complete inputs kind closed SourceCasts.closed embeds
    arithmetic library stateDeclared consDeclared countTyped typed beta coverage exposure kn tn ki ti
  have sourceSame := kind.substitute_source (n := n) (st := st) (original := original)
    (kn := kn) (tn := tn) (ki := ki) (ti := ti) σ
  rw [current] at sourceSame
  rw [← sourceSame] at assembled
  obtain ⟨artifact,checked,proofTyped⟩ := assembled
  let code := ClosedTerm.app ``HybridWord.Cmd.forRange [count.closedTerm,b.closedTerm]
  let piece : Piece env ctx p (σ.apply (kind.source n st (kind.nativeLambda kn tn ki ti original))) bodyExpected :=
    ⟨code.val,artifact,code.closed,code.represented⟩
  obtain ⟨target,next,_⟩ := next_typed inputs kind closed SourceCasts.closed arithmetic library
    stateDeclared consDeclared typed
  have constructor : CastTyping env 0 (SourceCasts env) ctx (.const ``HybridWord.Cmd.forRange []) constructorSignature :=
    .constant library.constructor (by simp) rfl
  have targetTyped := CastTyping.application constructor countTyped.target
  simp only [constructorSignature,exprType,cmdType,VExpr.inst] at targetTyped
  have finalTarget := CastTyping.application targetTyped target
  have represented : Represents (σ.apply (kind.source n st (kind.nativeLambda kn tn ki ti original)))
      (kind.loop countTyped.sourceCore.val inputs.s.val
        (.lam (.const kind.first []) (.lam (.const kind.second []) typed.sourceCore.val))) := by
    rw [sourceSame]
    exact kind.source_represents countTyped.sourceCore.property inputs.s.property (kind.lambda_represents typed.sourceCore.property)
  refine ⟨piece,?_,⟨⟨⟨_,represented⟩,
    source_typed library arithmetic iterator reads inputs kind countTyped.value next,finalTarget,proofTyped⟩⟩,rfl⟩
  have same := sameTerm_complete inputs.s.property inputs.s.property
  have stateSame : sameTerm state state = true := sameTerm_complete
    (Represents.constant rfl) (Represents.constant rfl)
  have natSame : sameTerm (.const ``Nat []) (.const ``Nat []) = true := sameTerm_complete
    (Represents.constant rfl) (Represents.constant rfl)
  have stateCompatible : compatible env conv ctx state state = true := by simp only [compatible,stateSame]; rfl
  have empty : underFunctions (fun _ => (none : Option (Continuation env))) = (fun _ => none) := by
    funext n; cases n <;> rfl
  have rangeArgs : ((Lean.Expr.const ``List.range []).app (Read.wordIndex n)).getAppArgs.toList = [Read.wordIndex n] := rfl
  have countArgs : (Read.wordIndex n).getAppArgs.toList = [nativeWidth,n] := rfl
  have stateCompat : compatible env conv ctx (.const ``HybridWord.State []) state = true := stateCompatible
  have stateTranslated : translate (.const ``HybridWord.State []) = some ⟨stateType,Represents.constant rfl⟩ := rfl
  have natTranslated : translate (.const ``Nat []) = some ⟨natType,Represents.constant rfl⟩ := rfl
  have bodyValue : (Mode.body == Mode.value) = false := rfl
  have bodyBody : (Mode.body != Mode.body) = false := rfl
  rw [visit]
  cases kind <;> cases σ <;>
    try simp [-heq_eq_eq,node,bodyValue,bodyBody,letParts,applicationHead,makeContinuation,continuationParts,lambdaChain,
      Substitution.apply,LeanBindings.substitute,ScalarEnvironment.arguments,ScalarEnvironment.below,lambdaParts,under,
      Kind.source,Kind.nativeHeader,Kind.nativeLambda,Kind.first,Kind.second,Kind.fact,Kind.mode,
      Kind.context,Kind.parameters,nativeRange,Read.wordIndex,For.Header.At.nativeHeader,
      nativeFoldHeader,Lean.mkApp3,Lean.mkAppB,Lean.Expr.getAppFn,Lean.Expr.constName?,Lean.mkApp5,Lean.mkApp4,
      Lean.mkApp2,Lean.mkApp,Lean.mkAppN,app,List.map_cons,List.map_nil,empty,
      stateCompatible,stateSame,natSame,same,current,finishBody,Mode.expected,code,piece,
      ClosedTerm.app,Piece.closedTerm,NaturalScope.forInParameters,NaturalScope.foldParameters,
      NaturalScope.nativeIndex,Arithmetic.nativeWidth,
      countParsed,bodyParsed] at current checked countParsed bodyParsed ⊢
  all_goals
    try simp only [List.getElem?_cons, Nat.reduceEqDiff, ↓reduceIte, Nat.reduceSub,
      List.getElem?_cons_zero,Option.unattach_some,Option.bind_some]
    dsimp only [GetElem?.getElem?,List.instGetElem?NatLtLength,List.get?Internal,Option.bind,Option.unattach,Option.map]
    try simp only [List.getElem?_cons, Nat.reduceEqDiff, ↓reduceIte, Nat.reduceSub,
      List.getElem?_cons_zero,Option.unattach_some,Option.bind_some]
    try simp [-heq_eq_eq,Lean.Expr.getAppFn,Lean.Expr.constName?,same,current,
      stateCompatible,stateSame,natSame,ScalarEnvironment.arguments,arguments,
      countParsed,bodyParsed]
    simp only [Read.wordIndex,app,List.foldl_cons,List.foldl_nil,Arithmetic.nativeWidth,Lean.mkApp3,Lean.mkApp2,Lean.mkAppB,Lean.mkApp] at rangeArgs countArgs
    try dsimp only [Option.unattach,Option.map,Option.bind]
    try simp [-heq_eq_eq,rangeArgs,countArgs,stateCompat,stateTranslated,natTranslated,
      Lean.Expr.getAppFn,Lean.Expr.constName?,countParsed,
      LeanBindings.rename,bodyParsed]
    dsimp! only [Lean.Expr.getAppArgs,Lean.Expr.getAppNumArgs]
    try simp [-heq_eq_eq,countParsed,bodyParsed]
    try simp only [Kind.context,Kind.parameters,Kind.first,Kind.second,Kind.mode,
      NaturalScope.forInParameters,NaturalScope.foldParameters,NaturalScope.nativeIndex,
      nativeWidth,Lean.mkApp3,Lean.mkApp2,Lean.mkAppB,Lean.mkApp,app,List.foldl_cons,List.foldl_nil] at bodyParsed
    try simp only [stateType,natType]
    try refine ⟨(.lam kn state (.lam tn (.const ``Nat []) original ti) ki), ?_, rfl, ?_⟩
    all_goals try (simp [syntaxSize, state]; omega)
    all_goals first
      | refine ⟨p.s, ⟨?_, rfl⟩, same, ?_⟩
      | refine ⟨st, ⟨?_, rfl⟩, by simpa [current] using same, ?_⟩
    all_goals try (simp [syntaxSize, state]; omega)
    all_goals try simp [-heq_eq_eq,Substitution.apply,LeanBindings.substitute,lambdaParts,
      state,stateCompat,stateCompatible,stateSame,natSame,stateTranslated,natTranslated,
      current,bodyParsed] at checked ⊢
    all_goals try simpa only [state,natType,stateType] using stateCompatible
    all_goals try simp only [stateType,natType] at bodyParsed ⊢
    all_goals try rw [bodyParsed]
    all_goals try dsimp only
    all_goals try rw [checked]
    all_goals first | rfl | exact ⟨stateCompatible, rfl⟩




theorem body_forRange_complete_code [Arithmetic.Includes proofCasts]
    (inputs : InputsTyped env ctx p) (kind : Kind)
    (closed : ClosedConstantTypes env)
    (embeds : ∀ scope a b, SourceCasts env scope a b → proofCasts scope a b)
    (arithmetic : Arithmetic.Signatures env) (library : Signatures env)
    (iterator : For.Header.Signatures env) (reads : Read.Signatures env)
    (stateDeclared : env.constants ``HybridWord.State = some ⟨0,.sort (.succ .zero)⟩)
    (consDeclared : env.constants ``List.cons = some consSignature)
    {count : Piece env ctx p n scalarExpected} (countTyped : ScalarCasts inputs count (SourceCasts env) proofCasts)
    {b : Piece env (kind.context ctx) (kind.parameters p) original kind.mode.expected}
    (typed : ChildCasts kind (kind.nextInputs inputs closed arithmetic library consDeclared) b (SourceCasts env) proofCasts)
    (beta : proofCasts ctx (kind.actualPremise inputs b.represented.val typed.sourceCore.val)
      (kind.continuationType inputs b.represented.val
        (.lam (.const kind.first []) (.lam (.const kind.second []) typed.sourceCore.val))))
    (coverage : Conversion.Covers conv 0 proofCasts) (exposure : Exposure env)
    (kn tn : Lean.Name) (ki ti : Lean.BinderInfo)
    (countParsed : ScalarEnvironment.parse env conv exposure ctx p n = some count)
    (bodyParsed : visit env conv exposure original (kind.context ctx) (kind.parameters p)
      kind.mode .identity (fun _ => none) = some b) :
    ∃ piece, StructuralBody.bodyRetained env conv exposure ctx p
      (kind.source n p.s (kind.nativeLambda kn tn ki ti original)) = some piece ∧
      Nonempty (BodyCasts inputs piece (SourceCasts env) proofCasts) ∧
      piece.code = app ``HybridWord.Cmd.forRange [count.code,b.code] := by
  have empty : underFunctions (fun _ => (none : Option (Continuation env))) = (fun _ => none) := by
    funext n; cases n <;> rfl
  exact mapped_forRange_complete_code (σ := .identity) (fs := fun _ => none) (st := p.s) (n := n) inputs kind
    closed embeds arithmetic library iterator reads stateDeclared consDeclared countTyped typed beta coverage exposure
    kn tn ki ti rfl countParsed (by simpa only [under,empty] using bodyParsed)

theorem body_forRange_complete [Arithmetic.Includes proofCasts]
    (inputs : InputsTyped env ctx p) (kind : Kind)
    (closed : ClosedConstantTypes env)
    (embeds : ∀ scope a b, SourceCasts env scope a b → proofCasts scope a b)
    (arithmetic : Arithmetic.Signatures env) (library : Signatures env)
    (iterator : For.Header.Signatures env) (reads : Read.Signatures env)
    (stateDeclared : env.constants ``HybridWord.State = some ⟨0,.sort (.succ .zero)⟩)
    (consDeclared : env.constants ``List.cons = some consSignature)
    {count : Piece env ctx p n scalarExpected} (countTyped : ScalarCasts inputs count (SourceCasts env) proofCasts)
    {b : Piece env (kind.context ctx) (kind.parameters p) original kind.mode.expected}
    (typed : ChildCasts kind (kind.nextInputs inputs closed arithmetic library consDeclared) b (SourceCasts env) proofCasts)
    (beta : proofCasts ctx (kind.actualPremise inputs b.represented.val typed.sourceCore.val)
      (kind.continuationType inputs b.represented.val
        (.lam (.const kind.first []) (.lam (.const kind.second []) typed.sourceCore.val))))
    (coverage : Conversion.Covers conv 0 proofCasts) (exposure : Exposure env)
    (kn tn : Lean.Name) (ki ti : Lean.BinderInfo)
    (countParsed : ScalarEnvironment.parse env conv exposure ctx p n = some count)
    (bodyParsed : visit env conv exposure original (kind.context ctx) (kind.parameters p)
      kind.mode .identity (fun _ => none) = some b) :
    ∃ piece, StructuralBody.bodyRetained env conv exposure ctx p
      (kind.source n p.s (kind.nativeLambda kn tn ki ti original)) = some piece ∧
      Nonempty (BodyCasts inputs piece (SourceCasts env) proofCasts) := by
  obtain ⟨piece,success,typed,_⟩ := body_forRange_complete_code inputs kind closed embeds arithmetic library iterator reads stateDeclared consDeclared countTyped typed beta coverage exposure kn tn ki ti countParsed bodyParsed
  exact ⟨piece,success,typed⟩

theorem continuation_cast (setup : Arithmetic.AliasSetup env)
    (inputs : InputsTyped env ctx p) (kind : Kind)
    (closed : ClosedConstantTypes env) (arithmetic : Arithmetic.Signatures env)
    (library : Signatures env) (steps : Step.Signatures env)
    (consDeclared : env.constants ``List.cons = some consSignature)
    (evalDeclared : env.constants ``HybridWord.Cmd.eval = some ⟨0,evalSignature⟩)
    (natFresh : ∀ r ∈ setup.rules, ``Nat ≠ r.name)
    (stateFresh : ∀ r ∈ setup.rules, ``HybridWord.State ≠ r.name)
    {b : Piece env (kind.context ctx) (kind.parameters p) original kind.mode.expected}
    (typed : ChildCasts kind (kind.nextInputs inputs closed arithmetic library consDeclared)
      b (SourceCasts env) (For.Casts setup))
    (form : ValueForm setup (kind.context ctx) typed.sourceCore.val (optionType kind.result)) :
    For.Casts setup ctx (kind.actualPremise inputs b.represented.val typed.sourceCore.val)
      (kind.continuationType inputs b.represented.val
        (.lam (.const kind.first []) (.lam (.const kind.second []) typed.sourceCore.val))) := by
  let next := kind.nextInputs inputs closed arithmetic library consDeclared
  have evaluation := eval_cast_typed next evalDeclared typed.target
  have firstDeclared : env.constants kind.first = some ⟨0,.sort (.succ .zero)⟩ := by
    cases kind with | forIn => exact arithmetic.natural | fold => exact steps.state
  have secondDeclared : env.constants kind.second = some ⟨0,.sort (.succ .zero)⟩ := by
    cases kind with | forIn => exact steps.state | fold => exact arithmetic.natural
  have firstFresh : ∀ r ∈ setup.rules, kind.first ≠ r.name := by
    cases kind with | forIn => exact natFresh | fold => exact stateFresh
  have secondFresh : ∀ r ∈ setup.rules, kind.second ≠ r.name := by
    cases kind with | forIn => exact stateFresh | fold => exact natFresh
  have resultTyped : DirectTyping env 0 (kind.context ctx) (optionType kind.result) (.sort (.succ .zero)) := by
    have optionHead : DirectTyping env 0 (kind.context ctx) (.const ``Option [.zero])
        (.forallE (.sort (.succ .zero)) (.sort (.succ .zero))) :=
      .constant steps.option (by simp [VLevel.WF]) rfl
    apply DirectTyping.application optionHead
    cases kind with
    | forIn => exact steps.step_typed
    | fold => exact .constant steps.state (by simp) rfl
  have leftTyped : CastTyping env 0 (SourceCasts env) (kind.context ctx)
      (kind.lhs (bodyValue next.i.val next.x.val next.y.val b.represented.val next.s.val next.ls.val))
      (optionType kind.result) := by
    cases kind with
    | fold => exact evaluation
    | forIn =>
      have liftTyped : CastTyping env 0 (SourceCasts env) (Kind.forIn.context ctx)
          (.const ``WordLoopFacts.lift []) Step.liftSignature :=
        .constant steps.liftDecl (by simp) rfl
      exact .application liftTyped evaluation
  have pair := For.Casts.pair (setup := setup) kind.first kind.second
    firstDeclared secondDeclared firstFresh secondFresh resultTyped
    (by cases kind <;> trivial) (by intro u; simp [optionType]) leftTyped typed.value form
  have codeClosed := b.represented.property.closed 0 b.closed
  cases kind <;>
    simpa only [Kind.actualPremise,Kind.continuationType,Kind.context,Kind.first,Kind.second,
      Kind.lhs,Kind.equation,Kind.result,Kind.state,Kind.index,Kind.nextInputs,next,
      NaturalScope.forInInputs,NaturalScope.foldInputs,NaturalScope.retain,InputsTyped.withLocal,
      InputsTyped.nextState,InputsTyped.lift,Pair.actual,Pair.required,continuation2Value,
      VExpr.lift,VExpr.liftN,VExpr.liftN'_liftN_hi,natType,stateType,applications,wordCons,
      codeClosed.liftN_eq (Nat.zero_le _)] using pair

end IRComparison.WordFrontend.NaturalLoop
