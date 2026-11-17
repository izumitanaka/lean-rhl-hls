import IRComparison.Frontend.LeanNamedBody
import IRComparison.Core.VersionFacts

namespace IRComparison.LeanVersionBody
open Lean4Lean LeanTyped LeanIRQuotation LeanIREvaluation LeanBodyQuotation LeanTypeInference
variable {env : VEnv} {U : Nat} {context : List VExpr}

def stateList : VExpr := .app (.const ``List [.zero]) stateType
def statesCode (states : List VExpr) : VExpr := states.foldr
  (fun s rest => applications (.const ``List.cons [.zero]) [stateType,s,rest])
  (.app (.const ``List.nil [.zero]) stateType)
def evaluate (body : Functional.Term) (inputs : LeanIREvaluationCompiler.Inputs env U context)
    (states : List VExpr) : VExpr := applications (.const ``Functional.Term.eval [])
  [inputs.i,inputs.x,inputs.y,functionalCode body,statesCode states,inputs.locals]

structure Artifact (inputs : LeanIREvaluationCompiler.Inputs env U context) (states : List VExpr) (source : Lean.Expr) where
  emitted : Functional.Term
  sourceCore : {v // Represents source v}
  sourceTyped : env.HasType U context sourceCore.val optionState
  proof : VExpr
  correct : env.HasType U context proof (eqState (evaluate emitted inputs states) sourceCore.val)

def typed (conversion : Conversion env) (exposure : Exposure env) (e ty : VExpr) :
    Option (LeanProofApplication.Typed env U context) := do
  let h ← checkWith env conversion U context e ty exposure
  return ⟨e,ty,h.down⟩


def lookup (native : Lean.Environment) (conversion : Conversion env) (exposure : Exposure env) :
    (states : List VExpr) → (v : Nat) → Option (LeanProofApplication.Typed env U context)
  | [],_ => none
  | s::ss,0 => do
    LeanLoopNormalization.args native ``VersionFacts.lookupZero
      [← typed conversion exposure s stateType,← typed conversion exposure (statesCode ss) stateList]
  | s::ss,n+1 => do
    let proof ← lookup native conversion exposure ss n
    let t ← ss[n]?
    LeanLoopNormalization.args native ``VersionFacts.lookupSucc
      [← typed conversion exposure (numeral n) (.const ``Nat []),
       ← typed conversion exposure s stateType,← typed conversion exposure t stateType,
       ← typed conversion exposure (statesCode ss) stateList,proof]

def select (inputs : LeanIREvaluationCompiler.Inputs env U context)
    (conversion : Conversion env) (exposure : Exposure env) (state : VExpr) :
    Option (LeanIREvaluationCompiler.Inputs env U context) := do
  let hs ← checkWith env conversion U context state stateType exposure
  return { inputs with state := state, stateTyped := hs.down }

def findState (states : List VExpr) (source : Lean.Expr) : Option Nat := do
  let core ← translate source
  states.findIdx? (· == core.val)

def common (inputs : LeanIREvaluationCompiler.Inputs env U context) (states : List VExpr)
    (conversion : Conversion env) (exposure : Exposure env) :
    Option (List (LeanProofApplication.Typed env U context)) := do
  return [⟨inputs.i,intType,inputs.indexTyped⟩,⟨inputs.x,intType,inputs.leftTyped⟩,
    ⟨inputs.y,intType,inputs.rightTyped⟩,← typed conversion exposure (statesCode states) stateList,
    ← typed conversion exposure inputs.locals intList]

def finish (inputs : LeanIREvaluationCompiler.Inputs env U context) (states : List VExpr)
    (conversion : Conversion env) (exposure : Exposure env) (source : Lean.Expr) (body : Functional.Term)
    (proof : LeanProofApplication.Typed env U context) : Option (Artifact inputs states source) := do
  let core ← translate source
  let hs ← checkWith env conversion U context core.val optionState exposure
  let p ← LeanLoopNormalization.cast conversion proof (eqState (evaluate body inputs states) core.val)
  return ⟨body,core,hs.down,p.val,p.property⟩

def valueProof (native : Lean.Environment) (inputs : LeanIREvaluationCompiler.Inputs env U context)
    (conversion : Conversion env) (exposure : Exposure env)
    (a : LeanSourceToIR.Artifact inputs source) : Option (LeanProofApplication.Typed env U context × LeanProofApplication.Typed env U context) := do
  let bridge ← LeanIRTransport.connect native inputs conversion exposure a.sourceCore a.sourceTyped a.target a.sourceProof a.sourceEquality
  have same := a.sourceCore.property.unique bridge.sourceCore.property
  return (⟨bridge.sourceCore.val,intType,by simpa only [same] using a.sourceTyped⟩,
    ⟨bridge.proof,_,bridge.correct⟩)

def continuation (conversion : Conversion env) (exposure : Exposure env) (domain : VExpr)
    (inputs : LeanIREvaluationCompiler.Inputs env U (domain::context))
    (a : Artifact inputs states body) : Option (LeanProofApplication.Typed env U context) := do
  let hd ← check env U context domain (.sort (.succ .zero))
  let f := VExpr.lam domain a.sourceCore.val
  let expected := eqState (evaluate a.emitted inputs states) (.app f.lift (.bvar 0))
  let proof ← LeanLoopNormalization.cast conversion ⟨a.proof,_,a.correct⟩ expected
  return ⟨.lam domain proof.val,.forallE domain expected,.lamDF hd.down proof.property⟩


def loop (native : Lean.Environment) (inputs : LeanIREvaluationCompiler.Inputs env U context)
    (states : List VExpr) (v : Nat)
    (conversion : Conversion env) (exposure : Exposure env) (source callback : Lean.Expr)
    (chosen : LeanIREvaluationCompiler.Inputs env U context)
    (count : LeanSourceToIR.Artifact chosen countSource)
    (inner : LeanIREvaluationCompiler.Inputs env U (stateType :: natType :: context))
    (normal : LeanLoopNormalization.Artifact (env := env) (U := U) (context := stateType :: natType :: context) originalBody)
    (body : Artifact inner (.bvar 0 :: states.map (VExpr.liftN 2)) normal.plain) :
    Option (Artifact inputs states source) := do
  let cb ← translate callback
  let callbackType := VExpr.forallE natType (.forallE stateType LeanLoopNormalization.optionStep)
  let hc ← typed conversion exposure cb.val callbackType
  let (n,hn) ← valueProof native chosen conversion exposure count
  let hNat ← check env U context natType (.sort (.succ .zero))
  let hState ← check env U (natType :: context) stateType (.sort (.succ .zero))
  let result := evaluate body.emitted inner (.bvar 0 :: states.map (VExpr.liftN 2))
  let hr ← typed conversion exposure result optionState
  have same := body.sourceCore.property.unique normal.plainCore.property
  let composed ← LeanLoopNormalization.args native ``LoopFacts.compose
    [hr,⟨normal.plainCore.val,optionState,normal.plainTyped⟩,
     ⟨normal.sourceCore.val,LeanLoopNormalization.optionStep,normal.sourceTyped⟩,
     ⟨body.proof,eqState result normal.plainCore.val,by simpa only [same] using body.correct⟩,
     ⟨normal.proof,_,normal.correct⟩]
  let expected := LeanLoopNormalization.stepEq (LeanLoopNormalization.liftValue result)
    (applications (cb.val.liftN 2) [.bvar 1,.bvar 0])
  let q ← LeanLoopNormalization.cast conversion composed expected
  let closed : LeanProofApplication.Typed env U context :=
    ⟨.lam natType (.lam stateType q.val),.forallE natType (.forallE stateType expected),
      .lamDF hNat.down (.lamDF hState.down q.property)⟩
  let proof ← LeanLoopNormalization.args native ``VersionFacts.capturedLoop
    ([← typed conversion exposure (numeral v) natType,
      ← typed conversion exposure (code count.emitted) expressionType,
      ← typed conversion exposure (functionalCode body.emitted) (.const ``Functional.Term [])] ++
     (← common inputs states conversion exposure) ++
     [⟨chosen.state,stateType,chosen.stateTyped⟩,n,hc,
      ← lookup native conversion exposure states v,hn,closed])
  finish inputs states conversion exposure source (.forRangeCaptured v count.emitted body.emitted (.yield 0)) proof

def loopInitial : Lean.Expr → Option Lean.Expr
  | .app (.app _ initial) _ => some initial
  | _ => none

def compile (native : Lean.Environment) {context : List VExpr}
    (inputs : LeanIREvaluationCompiler.Inputs env U context) (states : List VExpr)
    (conversion : Conversion env) (exposure : Exposure env) :
    Nat → (source : Lean.Expr) → Option (Artifact inputs states source)
  | 0,_ => none
  | fuel+1,source => do
    if let some (count,callback,originalBody) := LeanSourceBody.loopParts source then
      let initial ← loopInitial source
      let v ← findState states initial
      let chosen ← select inputs conversion exposure (← states[v]?)
      let c ← LeanSourceToIR.compile native chosen conversion exposure fuel count
      let inner ← LeanSourceBody.loopInputs inputs
      let normal ← LeanLoopNormalization.compile native conversion exposure fuel originalBody
      let b ← compile native inner (.bvar 0 :: states.map (VExpr.liftN 2)) conversion exposure fuel normal.plain
      return ← loop native inputs states v conversion exposure source callback chosen c inner normal b
    match source with
    | .letE name ty value body flag =>
      let next ← compile native inputs states conversion exposure fuel (LeanBindings.instantiate value body)
      finish inputs states conversion exposure (.letE name ty value body flag) next.emitted ⟨next.proof,_,next.correct⟩
    | .app (.lam name ty body binder) value =>
      let next ← compile native inputs states conversion exposure fuel (LeanBindings.instantiate value body)
      finish inputs states conversion exposure (.app (.lam name ty body binder) value) next.emitted ⟨next.proof,_,next.correct⟩
    | .app (.app LeanSourceBody.bindHead first) (.lam name (.const ``State []) body binder) =>
      let a ← compile native inputs states conversion exposure fuel first
      let later ← LeanSourceBody.nextInputs inputs
      let laterStates := .bvar 0 :: states.map VExpr.lift
      let b ← compile native later laterStates conversion exposure fuel body
      let fn := VExpr.lam stateType b.sourceCore.val
      let hf ← typed conversion exposure fn (.forallE stateType optionState)
      let hn ← continuation conversion exposure stateType later b
      let q ← LeanLoopNormalization.args native ``VersionFacts.bind
        ([← typed conversion exposure (functionalCode a.emitted) (.const ``Functional.Term []),
          ← typed conversion exposure (functionalCode b.emitted) (.const ``Functional.Term [])] ++
         (← common inputs states conversion exposure) ++
         [⟨a.sourceCore.val,optionState,a.sourceTyped⟩,hf,⟨a.proof,_,a.correct⟩,hn])
      finish inputs states conversion exposure
        (.app (.app LeanSourceBody.bindHead first) (.lam name (.const ``State []) body binder))
        (.bindResult a.emitted b.emitted) q
    | .app (.app LeanSourceBody.readBindHead first) (.lam name (.const ``Int []) body binder) =>
      let .app (.app readHead (.app (.app (.const ``State.arrays []) state) array)) index := first | none
      let first := Lean.Expr.app (.app readHead (.app (.app (.const ``State.arrays []) state) array)) index
      let v ← findState states state
      let selected ← states[v]?
      let chosen ← select inputs conversion exposure selected
      let a ← LeanSourceBody.read native chosen conversion exposure fuel first
      let later ← LeanSourceBody.readInputs inputs
      let b ← compile native later (states.map VExpr.lift) conversion exposure fuel body
      let fn := VExpr.lam intType b.sourceCore.val
      let hf ← typed conversion exposure fn (.forallE intType optionState)
      let hn ← continuation conversion exposure intType later b
      let q ← LeanLoopNormalization.args native ``VersionFacts.capture
        ([← typed conversion exposure (numeral v) (.const ``Nat []),
          ← typed conversion exposure (code a.emitted) expressionType,
          ← typed conversion exposure (functionalCode b.emitted) (.const ``Functional.Term [])] ++
          (← common inputs states conversion exposure) ++
          [← typed conversion exposure selected stateType,⟨a.sourceCore.val,optionInt,a.sourceTyped⟩,hf,
           ← lookup native conversion exposure states v,⟨a.proof,_,a.correct⟩,hn])
      finish inputs states conversion exposure
        (.app (.app LeanSourceBody.readBindHead first) (.lam name (.const ``Int []) body binder))
        (.letValue v a.emitted b.emitted) q
    | .app (.app (.app (.app (.const ``State.write []) state) array) address) value =>
      let v ← findState states state
      let selected ← states[v]?
      let chosen ← select inputs conversion exposure selected
      let (a,literal) ← LeanSourceBody.arrayIdentifier array
      let ja ← LeanSourceToIR.compile native chosen conversion exposure fuel address
      let ea ← LeanSourceToIR.compile native chosen conversion exposure fuel value
      let (j,hj) ← valueProof native chosen conversion exposure ja
      let (e,he) ← valueProof native chosen conversion exposure ea
      let q ← LeanLoopNormalization.args native (if literal then ``VersionFacts.storeLiteral else ``VersionFacts.store)
        ([← typed conversion exposure (numeral v) (.const ``Nat []),
          ← typed conversion exposure (numeral a) (.const ``Nat []),
          ← typed conversion exposure (code ja.emitted) expressionType,
          ← typed conversion exposure (code ea.emitted) expressionType] ++
         (← common inputs states conversion exposure) ++
         [← typed conversion exposure selected stateType,j,e,← lookup native conversion exposure states v,hj,he])
      finish inputs states conversion exposure
        (.app (.app (.app (.app (.const ``State.write []) state) array) address) value)
        (.letWrite v a ja.emitted ea.emitted (.yield 0)) q
    | LeanSourceBody.conditional test decision yes no =>
      let selected ← states[0]?
      let chosen ← select inputs conversion exposure selected
      let e ← LeanSourceToIR.compile native chosen conversion exposure fuel test
      let a ← compile native inputs states conversion exposure fuel yes
      let b ← compile native inputs states conversion exposure fuel no
      let (z,hz) ← valueProof native chosen conversion exposure e
      let dec ← translate decision
      let q ← LeanLoopNormalization.args native ``VersionFacts.branch
        ([← typed conversion exposure (numeral 0) (.const ``Nat []),
          ← typed conversion exposure (code e.emitted) expressionType,
          ← typed conversion exposure (functionalCode a.emitted) (.const ``Functional.Term []),
          ← typed conversion exposure (functionalCode b.emitted) (.const ``Functional.Term [])] ++
         (← common inputs states conversion exposure) ++
         [← typed conversion exposure selected stateType,z,
          ← typed conversion exposure dec.val (LeanSelectBridge.decisionType z.term),
          ⟨a.sourceCore.val,optionState,a.sourceTyped⟩,⟨b.sourceCore.val,optionState,b.sourceTyped⟩,
          ← lookup native conversion exposure states 0,hz,⟨a.proof,_,a.correct⟩,⟨b.proof,_,b.correct⟩])
      finish inputs states conversion exposure (LeanSourceBody.conditional test decision yes no)
        (.branch 0 e.emitted a.emitted b.emitted) q
    | .app head state =>
      let v ← findState states state
      let selected ← states[v]?
      let fact := if head.getAppFn.constName? = some ``Option.some then ``VersionFacts.yieldSome else ``VersionFacts.yieldPure
      let q ← LeanLoopNormalization.args native fact
        ([← typed conversion exposure (numeral v) (.const ``Nat [])] ++
         (← common inputs states conversion exposure) ++
         [← typed conversion exposure selected stateType,← lookup native conversion exposure states v])
      finish inputs states conversion exposure (.app head state) (.yield v) q
    | _ => none

end IRComparison.LeanVersionBody
