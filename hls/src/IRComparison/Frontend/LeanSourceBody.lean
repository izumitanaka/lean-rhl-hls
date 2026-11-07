import IRComparison.Frontend.LeanSourceToIR
import IRComparison.Frontend.LeanBodyQuotation
import IRComparison.Frontend.LeanProofApplication
import IRComparison.Core.BodyFacts
import IRComparison.Core.ReadFacts
import IRComparison.Frontend.LeanLoopNormalization
import IRComparison.Frontend.LeanReadHoisting

namespace IRComparison.LeanSourceBody
open Lean4Lean LeanTyped LeanIRQuotation LeanIREvaluation LeanBodyQuotation LeanTypeInference
variable {env : VEnv} {U : Nat} {context : List VExpr}

structure Artifact (inputs : LeanIREvaluationCompiler.Inputs env U context) (source : Lean.Expr) where
  imperative : Imperative.Cmd
  functional : Functional.Term
  sourceCore : {v // Represents source v}
  sourceTyped : env.HasType U context sourceCore.val optionState
  imperativeProof : VExpr
  functionalProof : VExpr
  imperativeCorrect : env.HasType U context imperativeProof
    (eqState (imperativeEval (imperativeCode imperative) inputs.i inputs.x inputs.y inputs.state inputs.locals) sourceCore.val)
  functionalCorrect : env.HasType U context functionalProof
    (eqState (functionalEval (functionalCode functional) inputs.i inputs.x inputs.y inputs.state inputs.locals) sourceCore.val)

/-- Literal array identifiers are decoded without assuming any array size or
    index bound. The final proof type is checked against the exact source. -/
def arrayIdentifier : Lean.Expr → Option (Nat × Bool)
  | .lit (.natVal n) => some (n,false)
  | .app (.app (.app (.const ``OfNat.ofNat [.zero]) (.const ``Nat [])) (.lit (.natVal n)))
      (.app (.const ``instOfNatNat []) (.lit (.natVal m))) =>
      if n = m then some (n,true) else none
  | _ => none

private def applyArguments (f : LeanProofApplication.Typed env U context)
    (args : List (LeanProofApplication.Typed env U context)) :
    Option (LeanProofApplication.Typed env U context) :=
  args.foldlM LeanProofApplication.apply f

/-- Extend the context with the updated state, preserving all captured input
    values. The old state remains in scope but is not substituted for the new. -/
def nextInputs (inputs : LeanIREvaluationCompiler.Inputs env U context) :
    Option (LeanIREvaluationCompiler.Inputs env U (stateType :: context)) := do
  let hi ← check env U (stateType :: context) (inputs.i.liftN 1) intType
  let hx ← check env U (stateType :: context) (inputs.x.liftN 1) intType
  let hy ← check env U (stateType :: context) (inputs.y.liftN 1) intType
  let hs ← check env U (stateType :: context) (.bvar 0) stateType
  return ⟨inputs.i.liftN 1,inputs.x.liftN 1,inputs.y.liftN 1,.bvar 0,hi.down,hx.down,hy.down,hs.down,inputs.locals.liftN 1⟩

private def valueProof (native : Lean.Environment) (inputs : LeanIREvaluationCompiler.Inputs env U context)
    (conversion : Conversion env) (exposure : Exposure env)
    (a : LeanSourceToIR.Artifact inputs source) :
    Option (LeanProofApplication.Typed env U context × LeanProofApplication.Typed env U context) := do
  let bridge ← LeanIRTransport.connect native inputs conversion exposure a.sourceCore a.sourceTyped a.target a.sourceProof a.sourceEquality
  have same := a.sourceCore.property.unique bridge.sourceCore.property
  return (⟨bridge.sourceCore.val,intType,by simpa only [same] using a.sourceTyped⟩,
    ⟨bridge.proof,eqResult (eval (code a.emitted) inputs.i inputs.x inputs.y inputs.state inputs.locals)
      (someInt bridge.sourceCore.val),bridge.correct⟩)

def store (native : Lean.Environment) (inputs : LeanIREvaluationCompiler.Inputs env U context)
    (conversion : Conversion env) (exposure : Exposure env)
    (state array : Lean.Expr) (address : LeanSourceToIR.Artifact inputs addressSource)
    (value : LeanSourceToIR.Artifact inputs valueSource) :
    Option (Artifact inputs (.app (.app (.app (.app (.const ``State.write []) state) array) addressSource) valueSource)) := do
  let (a,elaborated) ← arrayIdentifier array
  let source ← translate (.app (.app (.app (.app (.const ``State.write []) state) array) addressSource) valueSource)
  let sourceTyped ← checkWith env conversion U context source.val optionState exposure
  let ha ← check env U context (numeral a) LeanLiteralNormalization.natType
  let (j,hj) ← valueProof native inputs conversion exposure address
  let (v,hv) ← valueProof native inputs conversion exposure value
  let hl ← check env U context inputs.locals intList
  let args : List (LeanProofApplication.Typed env U context) :=
    [⟨numeral a,LeanLiteralNormalization.natType,ha.down⟩,
     ⟨code address.emitted,expressionType,address.target.codeTyped⟩,
     ⟨code value.emitted,expressionType,value.target.codeTyped⟩,
     ⟨inputs.i,intType,inputs.indexTyped⟩,⟨inputs.x,intType,inputs.leftTyped⟩,
     ⟨inputs.y,intType,inputs.rightTyped⟩,⟨inputs.state,stateType,inputs.stateTyped⟩,⟨inputs.locals,intList,hl.down⟩,
     j,v,hj,hv]
  let imperative := Imperative.Cmd.store a address.emitted value.emitted
  let functional := Functional.Term.letWrite 0 a address.emitted value.emitted (.yield 0)
  let hi ← LeanProofApplication.constant native env U context
    (if elaborated then ``BodyFacts.storeImperativeLiteral else ``BodyFacts.storeImperative)
  let hf ← LeanProofApplication.constant native env U context
    (if elaborated then ``BodyFacts.storeFunctionalLiteral else ``BodyFacts.storeFunctional)
  let pi ← applyArguments hi args
  let pf ← applyArguments hf args
  if si : pi.type = eqState (imperativeEval (imperativeCode imperative)
      inputs.i inputs.x inputs.y inputs.state inputs.locals) source.val then
    if sf : pf.type = eqState (functionalEval (functionalCode functional)
        inputs.i inputs.x inputs.y inputs.state inputs.locals) source.val then
      return ⟨imperative,functional,source,sourceTyped.down,pi.term,pf.term,
        si ▸ pi.correct,sf ▸ pf.correct⟩
    else none
  else none

@[match_pattern] def conditional (test decision yes no : Lean.Expr) : Lean.Expr :=
  .app (.app (.app (.app (.app (.const ``ite [.succ .zero])
    (.app (.const ``Option [.zero]) (.const ``State [])))
      (NativeRHL.ExprAnalysis.nonzeroCond test)) decision) yes) no

def branch (native : Lean.Environment) (inputs : LeanIREvaluationCompiler.Inputs env U context)
    (conversion : Conversion env) (exposure : Exposure env)
    (test : LeanSourceToIR.Artifact inputs testSource) (decision : Lean.Expr)
    (yes : Artifact inputs yesSource) (no : Artifact inputs noSource) :
    Option (Artifact inputs (conditional testSource decision yesSource noSource)) := do
  let source ← translate (conditional testSource decision yesSource noSource)
  let sourceTyped ← checkWith env conversion U context source.val optionState exposure
  let (v,hv) ← valueProof native inputs conversion exposure test
  let d ← translate decision
  let hd ← checkWith env conversion U context d.val (LeanSelectBridge.decisionType v.term) exposure
  let imperative := Imperative.Cmd.branch test.emitted yes.imperative no.imperative
  let functional := Functional.Term.branch 0 test.emitted yes.functional no.functional
  let ci ← check env U context (imperativeCode yes.imperative) (.const ``Imperative.Cmd [])
  let di ← check env U context (imperativeCode no.imperative) (.const ``Imperative.Cmd [])
  let cf ← check env U context (functionalCode yes.functional) (.const ``Functional.Term [])
  let df ← check env U context (functionalCode no.functional) (.const ``Functional.Term [])
  let leadingArgs : List (LeanProofApplication.Typed env U context) :=
    [⟨code test.emitted,expressionType,test.target.codeTyped⟩]
  let hl ← check env U context inputs.locals intList
  let common : List (LeanProofApplication.Typed env U context) :=
    [⟨inputs.i,intType,inputs.indexTyped⟩,⟨inputs.x,intType,inputs.leftTyped⟩,
     ⟨inputs.y,intType,inputs.rightTyped⟩,⟨inputs.state,stateType,inputs.stateTyped⟩,⟨inputs.locals,intList,hl.down⟩,
     v,⟨d.val,LeanSelectBridge.decisionType v.term,hd.down⟩,
     ⟨yes.sourceCore.val,optionState,yes.sourceTyped⟩,⟨no.sourceCore.val,optionState,no.sourceTyped⟩,hv]
  let hi ← LeanProofApplication.constant native env U context ``BodyFacts.branchImperative
  let hf ← LeanProofApplication.constant native env U context ``BodyFacts.branchFunctional
  let pi ← applyArguments hi (leadingArgs ++
    [⟨imperativeCode yes.imperative,.const ``Imperative.Cmd [],ci.down⟩,
     ⟨imperativeCode no.imperative,.const ``Imperative.Cmd [],di.down⟩] ++ common ++
    [⟨yes.imperativeProof,_,yes.imperativeCorrect⟩,⟨no.imperativeProof,_,no.imperativeCorrect⟩])
  let pf ← applyArguments hf (leadingArgs ++
    [⟨functionalCode yes.functional,.const ``Functional.Term [],cf.down⟩,
     ⟨functionalCode no.functional,.const ``Functional.Term [],df.down⟩] ++ common ++
    [⟨yes.functionalProof,_,yes.functionalCorrect⟩,⟨no.functionalProof,_,no.functionalCorrect⟩])
  if si : pi.type = eqState (imperativeEval (imperativeCode imperative)
      inputs.i inputs.x inputs.y inputs.state inputs.locals) source.val then
    if sf : pf.type = eqState (functionalEval (functionalCode functional)
        inputs.i inputs.x inputs.y inputs.state inputs.locals) source.val then
      return ⟨imperative,functional,source,sourceTyped.down,pi.term,pf.term,
        si ▸ pi.correct,sf ▸ pf.correct⟩
    else none
  else none

/-- One typed Lean beta step handles ordinary lets and the local continuation
    functions introduced by do elaboration. No naming convention is assumed. -/
def letValue (inputs : LeanIREvaluationCompiler.Inputs env U context)
    (conversion : Conversion env) (exposure : Exposure env) (source : Lean.Expr)
    (next : Artifact inputs nextSource) : Option (Artifact inputs source) := do
  let core ← translate source
  let reduced ← LeanTypeReduction.step [] conversion U context exposure core.val
  if same : reduced.val.1 = next.sourceCore.val then
    if resultType : reduced.val.2 = optionState then
      let hs ← checkWith env conversion U context core.val optionState exposure
      let heq ← check env U context eqHead (.forallE optionState (.forallE optionState (.sort .zero)))
      let hi ← checkWith env conversion U context (imperativeEval (imperativeCode next.imperative)
        inputs.i inputs.x inputs.y inputs.state inputs.locals) optionState exposure
      let hf ← checkWith env conversion U context (functionalEval (functionalCode next.functional)
        inputs.i inputs.x inputs.y inputs.state inputs.locals) optionState exposure
      have beta : env.IsDefEq U context core.val next.sourceCore.val optionState :=
        by simpa only [same,resultType] using reduced.property
      return {
        imperative := next.imperative, functional := next.functional
        sourceCore := core, sourceTyped := hs.down
        imperativeProof := next.imperativeProof, functionalProof := next.functionalProof
        imperativeCorrect := .defeq (result_congr heq.down hi.down beta).symm next.imperativeCorrect
        functionalCorrect := .defeq (result_congr heq.down hf.down beta).symm next.functionalCorrect }
    else none
  else none

@[match_pattern] def bindHead : Lean.Expr :=
  .app (.app (.app (.app (.const ``Bind.bind [.zero,.zero]) (.const ``Option [.zero]))
    (.app (.app (.const ``Monad.toBind [.zero,.zero]) (.const ``Option [.zero]))
      (.const ``instMonadOption [.zero]))) (.const ``State [])) (.const ``State [])

/-- Convert a child's open-body proof into the universally quantified
    continuation premise used by the general sequencing lemma. -/
private def continuationProof (domain : VExpr) (conversion : Conversion env) (exposure : Exposure env)
    (nextInputs : LeanIREvaluationCompiler.Inputs env U (domain :: context))
    (next : Artifact nextInputs body) (functional : Bool) :
    Option (LeanProofApplication.Typed env U context) := do
  let continuation := VExpr.lam domain next.sourceCore.val
  let applied := VExpr.app (continuation.liftN 1) (.bvar 0)
  let reduced ← LeanTypeReduction.step [] conversion U (domain :: context) exposure applied
  if same : reduced.val.1 = next.sourceCore.val then
    if resultType : reduced.val.2 = optionState then
      let heq ← check env U (domain :: context) eqHead (.forallE optionState (.forallE optionState (.sort .zero)))
      let domaind ← check env U context domain (.sort (.succ .zero))
      have sourceEq : env.IsDefEq U (domain :: context) applied next.sourceCore.val optionState :=
        by simpa only [same,resultType] using reduced.property
      let target := if functional then
          functionalEval (functionalCode next.functional) nextInputs.i nextInputs.x nextInputs.y nextInputs.state nextInputs.locals
        else imperativeEval (imperativeCode next.imperative) nextInputs.i nextInputs.x nextInputs.y nextInputs.state nextInputs.locals
      let targetTyped ← checkWith env conversion U (domain :: context) target optionState exposure
      let proof := if functional then next.functionalProof else next.imperativeProof
      have bodyProof : env.HasType U (domain :: context) proof (eqState target next.sourceCore.val) := by
        cases functional <;> first | exact next.imperativeCorrect | exact next.functionalCorrect
      have converted := VEnv.IsDefEq.defeq (result_congr heq.down targetTyped.down sourceEq).symm bodyProof
      return ⟨.lam domain proof,.forallE domain (eqState target applied),.lamDF domaind.down converted⟩
    else none
  else none

def sequence (native : Lean.Environment) (inputs : LeanIREvaluationCompiler.Inputs env U context)
    (conversion : Conversion env) (exposure : Exposure env)
    (first : Artifact inputs firstSource)
    (laterInputs : LeanIREvaluationCompiler.Inputs env U (stateType :: context))
    (next : Artifact laterInputs nextSource) :
    Option (Artifact inputs (.app (.app bindHead firstSource) (.lam name (.const ``State []) nextSource binder))) := do
  let source ← translate (.app (.app bindHead firstSource) (.lam name (.const ``State []) nextSource binder))
  let sourceTyped ← checkWith env conversion U context source.val optionState exposure
  let continuation := VExpr.lam stateType next.sourceCore.val
  let hc ← checkWith env conversion U context continuation (.forallE stateType optionState) exposure
  let ci ← check env U context (imperativeCode first.imperative) (.const ``Imperative.Cmd [])
  let di ← check env U context (imperativeCode next.imperative) (.const ``Imperative.Cmd [])
  let cf ← check env U context (functionalCode first.functional) (.const ``Functional.Term [])
  let df ← check env U context (functionalCode next.functional) (.const ``Functional.Term [])
  let qi ← continuationProof stateType conversion exposure laterInputs next false
  let qf ← continuationProof stateType conversion exposure laterInputs next true
  let hi ← LeanProofApplication.constant native env U context ``BodyFacts.seqImperative
  let hf ← LeanProofApplication.constant native env U context ``BodyFacts.seqFunctional
  let hl ← check env U context inputs.locals intList
  let common : List (LeanProofApplication.Typed env U context) :=
    [⟨inputs.i,intType,inputs.indexTyped⟩,⟨inputs.x,intType,inputs.leftTyped⟩,
     ⟨inputs.y,intType,inputs.rightTyped⟩,⟨inputs.state,stateType,inputs.stateTyped⟩,⟨inputs.locals,intList,hl.down⟩,
     ⟨first.sourceCore.val,optionState,first.sourceTyped⟩,
     ⟨continuation,.forallE stateType optionState,hc.down⟩]
  let pi ← applyArguments hi
    ([⟨imperativeCode first.imperative,.const ``Imperative.Cmd [],ci.down⟩,
      ⟨imperativeCode next.imperative,.const ``Imperative.Cmd [],di.down⟩] ++ common ++
     [⟨first.imperativeProof,_,first.imperativeCorrect⟩,qi])
  let pf ← applyArguments hf
    ([⟨functionalCode first.functional,.const ``Functional.Term [],cf.down⟩,
      ⟨functionalCode next.functional,.const ``Functional.Term [],df.down⟩] ++ common ++
     [⟨first.functionalProof,_,first.functionalCorrect⟩,qf])
  let imperative := Imperative.Cmd.seq first.imperative next.imperative
  let functional := Functional.Term.letResult 0 first.functional (.letResult 0 next.functional (.yield 0))
  if si : pi.type = eqState (imperativeEval (imperativeCode imperative)
      inputs.i inputs.x inputs.y inputs.state inputs.locals) source.val then
    if sf : pf.type = eqState (functionalEval (functionalCode functional)
        inputs.i inputs.x inputs.y inputs.state inputs.locals) source.val then
      return ⟨imperative,functional,source,sourceTyped.down,pi.term,pf.term,si ▸ pi.correct,sf ▸ pf.correct⟩
    else none
  else none

/-- Only the exact theorem conclusion is accepted; this is not a fallback
    assigning skip semantics to an unsupported source computation. -/
def returnState (native : Lean.Environment) (inputs : LeanIREvaluationCompiler.Inputs env U context)
    (conversion : Conversion env) (exposure : Exposure env) (source : Lean.Expr) :
    Option (Artifact inputs source) := do
  let core ← translate source
  let sourceTyped ← checkWith env conversion U context core.val optionState exposure
  let hl ← check env U context inputs.locals intList
  let args : List (LeanProofApplication.Typed env U context) :=
    [⟨inputs.i,intType,inputs.indexTyped⟩,⟨inputs.x,intType,inputs.leftTyped⟩,
     ⟨inputs.y,intType,inputs.rightTyped⟩,⟨inputs.state,stateType,inputs.stateTyped⟩,⟨inputs.locals,intList,hl.down⟩]
  for (fi,ff) in [(``BodyFacts.skipImperative,``BodyFacts.skipFunctional),
      (``BodyFacts.returnImperative,``BodyFacts.returnFunctional)] do
    let hi ← LeanProofApplication.constant native env U context fi
    let hf ← LeanProofApplication.constant native env U context ff
    let pi ← applyArguments hi args
    let pf ← applyArguments hf args
    if si : pi.type = eqState (imperativeEval (imperativeCode .skip)
        inputs.i inputs.x inputs.y inputs.state inputs.locals) core.val then
      if sf : pf.type = eqState (functionalEval (functionalCode (.yield 0))
          inputs.i inputs.x inputs.y inputs.state inputs.locals) core.val then
        return ⟨.skip,.yield 0,core,sourceTyped.down,pi.term,pf.term,si ▸ pi.correct,sf ▸ pf.correct⟩
  none

/-- Extend the private value environment without changing the selected state. -/
def readInputs (inputs : LeanIREvaluationCompiler.Inputs env U context) :
    Option (LeanIREvaluationCompiler.Inputs env U (intType :: context)) := do
  let hi ← check env U (intType :: context) (inputs.i.liftN 1) intType
  let hx ← check env U (intType :: context) (inputs.x.liftN 1) intType
  let hy ← check env U (intType :: context) (inputs.y.liftN 1) intType
  let hs ← check env U (intType :: context) (inputs.state.liftN 1) stateType
  return ⟨inputs.i.liftN 1,inputs.x.liftN 1,inputs.y.liftN 1,inputs.state.liftN 1,
    hi.down,hx.down,hy.down,hs.down,consInts (.bvar 0) (inputs.locals.liftN 1)⟩

structure ReadArtifact (inputs : LeanIREvaluationCompiler.Inputs env U context) (source : Lean.Expr) where
  emitted : Expr
  sourceCore : {v // Represents source v}
  sourceTyped : env.HasType U context sourceCore.val optionInt
  proof : VExpr
  correct : env.HasType U context proof
    (eqResult (eval (code emitted) inputs.i inputs.x inputs.y inputs.state inputs.locals) sourceCore.val)

private def readParts : Lean.Expr → Option (Lean.Expr × Lean.Expr)
  | .app (.app head (.app (.app (.const ``State.arrays []) _) array)) index =>
      if head.getAppFn.constName? = some ``GetElem?.getElem? then some (array,index) else none
  | _ => none

private def naturalAddress : Lean.Expr → Option Lean.Expr
  | .app (.const ``Int.toNat []) address => some address
  | _ => none

/-- The exact native read theorem validates the instance, state and index.
    Matching an apparent getElem head alone is never sufficient. -/
def read (native : Lean.Environment) (inputs : LeanIREvaluationCompiler.Inputs env U context)
    (conversion : Conversion env) (exposure : Exposure env) (fuel : Nat) (source : Lean.Expr) :
    Option (ReadArtifact inputs source) := do
  let (array,index) ← readParts source
  let (a,al) ← arrayIdentifier array
  let core ← translate source
  let hs ← checkWith env conversion U context core.val optionInt exposure
  let ha ← check env U context (numeral a) LeanLiteralNormalization.natType
  let hl ← check env U context inputs.locals intList
  let common : List (LeanProofApplication.Typed env U context) :=
    [⟨inputs.i,intType,inputs.indexTyped⟩,⟨inputs.x,intType,inputs.leftTyped⟩,
     ⟨inputs.y,intType,inputs.rightTyped⟩,⟨inputs.state,stateType,inputs.stateTyped⟩,
     ⟨inputs.locals,intList,hl.down⟩]
  let arrayArg : LeanProofApplication.Typed env U context := ⟨numeral a,LeanLiteralNormalization.natType,ha.down⟩
  let (emitted, fact, args) ← match arrayIdentifier index with
    | some (n,nl) => do
        let hn ← check env U context (numeral n) LeanLiteralNormalization.natType
        let fact := if al then (if nl then ``ReadFacts.literalAN else ``ReadFacts.literalA)
          else (if nl then ``ReadFacts.literalN else ``ReadFacts.literal)
        pure (Expr.read a (.lit (Int.ofNat n)), fact,
          [arrayArg,⟨numeral n,LeanLiteralNormalization.natType,hn.down⟩] ++ common)
    | none => do
        if let some signed := naturalAddress index then
          let address ← LeanSourceToIR.compile native inputs conversion exposure fuel signed
          let (j,hj) ← valueProof native inputs conversion exposure address
          pure (Expr.read a (.natIndex address.emitted),
            (if al then ``ReadFacts.dynamicA else ``ReadFacts.dynamic),
            [arrayArg,⟨code address.emitted,expressionType,address.target.codeTyped⟩] ++ common ++ [j,hj])
        else
          let castIndex := Lean.mkAppN (.const ``Nat.cast [.zero])
            #[.const ``Int [],.const ``instNatCastInt [],index]
          let address ← LeanSourceToIR.compile native inputs conversion exposure fuel castIndex
          let (_,hj) ← valueProof native inputs conversion exposure address
          let j ← translate index
          let hjt ← check env U context j.val LeanLiteralNormalization.natType
          pure (Expr.read a address.emitted, (if al then ``ReadFacts.naturalA else ``ReadFacts.natural),
            [arrayArg,⟨code address.emitted,expressionType,address.target.codeTyped⟩] ++ common ++
              [⟨j.val,LeanLiteralNormalization.natType,hjt.down⟩,hj])
  let fixedFact ← LeanProofApplication.constant native env U context fact
  let proof ← applyArguments fixedFact args
  if same : proof.type = eqResult (eval (code emitted) inputs.i inputs.x inputs.y inputs.state inputs.locals) core.val then
    return ⟨emitted,core,hs.down,proof.term,same ▸ proof.correct⟩
  else none

@[match_pattern] def readBindHead : Lean.Expr :=
  .app (.app (.app (.app (.const ``Bind.bind [.zero,.zero]) (.const ``Option [.zero]))
    (.app (.app (.const ``Monad.toBind [.zero,.zero]) (.const ``Option [.zero]))
      (.const ``instMonadOption [.zero]))) (.const ``Int [])) (.const ``State [])

def readBinding (native : Lean.Environment) (inputs : LeanIREvaluationCompiler.Inputs env U context)
    (conversion : Conversion env) (exposure : Exposure env)
    (first : ReadArtifact inputs firstSource)
    (later : LeanIREvaluationCompiler.Inputs env U (intType :: context))
    (next : Artifact later nextSource) :
    Option (Artifact inputs (.app (.app readBindHead firstSource) (.lam name (.const ``Int []) nextSource binder))) := do
  let source ← translate (.app (.app readBindHead firstSource) (.lam name (.const ``Int []) nextSource binder))
  let hs ← checkWith env conversion U context source.val optionState exposure
  let continuation := VExpr.lam intType next.sourceCore.val
  let hc ← checkWith env conversion U context continuation (.forallE intType optionState) exposure
  let he ← check env U context (code first.emitted) expressionType
  let di ← check env U context (imperativeCode next.imperative) (.const ``Imperative.Cmd [])
  let df ← check env U context (functionalCode next.functional) (.const ``Functional.Term [])
  let qi ← continuationProof intType conversion exposure later next false
  let qf ← continuationProof intType conversion exposure later next true
  let hi ← LeanProofApplication.constant native env U context ``BodyFacts.letImperative
  let hf ← LeanProofApplication.constant native env U context ``BodyFacts.letFunctional
  let hl ← check env U context inputs.locals intList
  let common : List (LeanProofApplication.Typed env U context) :=
    [⟨inputs.i,intType,inputs.indexTyped⟩,⟨inputs.x,intType,inputs.leftTyped⟩,
     ⟨inputs.y,intType,inputs.rightTyped⟩,⟨inputs.state,stateType,inputs.stateTyped⟩,⟨inputs.locals,intList,hl.down⟩,
     ⟨first.sourceCore.val,optionInt,first.sourceTyped⟩,
     ⟨continuation,.forallE intType optionState,hc.down⟩,⟨first.proof,_,first.correct⟩]
  let pi ← applyArguments hi
    ([⟨code first.emitted,expressionType,he.down⟩,
      ⟨imperativeCode next.imperative,.const ``Imperative.Cmd [],di.down⟩] ++ common ++ [qi])
  let pf ← applyArguments hf
    ([⟨code first.emitted,expressionType,he.down⟩,
      ⟨functionalCode next.functional,.const ``Functional.Term [],df.down⟩] ++ common ++ [qf])
  let imperative := Imperative.Cmd.letValue first.emitted next.imperative
  let functional := Functional.Term.letValue 0 first.emitted next.functional
  if si : pi.type = eqState (imperativeEval (imperativeCode imperative)
      inputs.i inputs.x inputs.y inputs.state inputs.locals) source.val then
    if sf : pf.type = eqState (functionalEval (functionalCode functional)
        inputs.i inputs.x inputs.y inputs.state inputs.locals) source.val then
      return ⟨imperative,functional,source,hs.down,pi.term,pf.term,si ▸ pi.correct,sf ▸ pf.correct⟩
    else none
  else none

def natType : VExpr := .const ``Nat []
def loopIndex (n : VExpr) : VExpr := applications (.const ``Nat.cast [.zero])
  [intType,.const ``instNatCastInt [],n]

def loopInputs (inputs : LeanIREvaluationCompiler.Inputs env U context) :
    Option (LeanIREvaluationCompiler.Inputs env U (stateType :: natType :: context)) := do
  let hi ← check env U (stateType :: natType :: context) (inputs.i.liftN 2) intType
  let hx ← check env U (stateType :: natType :: context) (inputs.x.liftN 2) intType
  let hy ← check env U (stateType :: natType :: context) (inputs.y.liftN 2) intType
  let hs ← check env U (stateType :: natType :: context) (.bvar 0) stateType
  return ⟨inputs.i.liftN 2,inputs.x.liftN 2,inputs.y.liftN 2,.bvar 0,
    hi.down,hx.down,hy.down,hs.down,consInts (loopIndex (.bvar 1)) (inputs.locals.liftN 2)⟩

/-- This extracts only the standard range/callback shell. The fixed theorem's
    full type subsequently checks the actual instance, state and callback. -/
def loopParts : Lean.Expr → Option (Lean.Expr × Lean.Expr × Lean.Expr)
  | .app (.app (.app _ (.app (.const ``List.range []) (.app (.const ``Int.toNat []) count))) _)
      callback@(.lam _ (.const ``Nat []) (.lam _ (.const ``State []) body _) _) => some (count,callback,body)
  | _ => none

def loop (native : Lean.Environment) (inputs : LeanIREvaluationCompiler.Inputs env U context)
    (conversion : Conversion env) (exposure : Exposure env) (source callback : Lean.Expr)
    (count : LeanSourceToIR.Artifact inputs countSource)
    (inner : LeanIREvaluationCompiler.Inputs env U (stateType :: natType :: context))
    (normal : LeanLoopNormalization.Artifact (env := env) (U := U) (context := stateType :: natType :: context) originalBody)
    (body : Artifact inner normal.plain) : Option (Artifact inputs source) := do
  let sc ← translate source
  let hs ← checkWith env conversion U context sc.val optionState exposure
  let cb ← translate callback
  let callbackType := VExpr.forallE natType (.forallE stateType LeanLoopNormalization.optionStep)
  let hc ← checkWith env conversion U context cb.val callbackType exposure
  let (n,hn) ← valueProof native inputs conversion exposure count
  let he ← check env U context (code count.emitted) expressionType
  let hl ← check env U context inputs.locals intList
  let hNat ← check env U context natType (.sort (.succ .zero))
  let hState ← check env U (natType :: context) stateType (.sort (.succ .zero))
  let one (functional : Bool) : Option (LeanProofApplication.Typed env U context) := do
    let c := if functional then functionalCode body.functional else imperativeCode body.imperative
    let ct := if functional then VExpr.const ``Functional.Term [] else .const ``Imperative.Cmd []
    let hct ← check env U context c ct
    let result := if functional then functionalEval c inner.i inner.x inner.y inner.state inner.locals
      else imperativeEval c inner.i inner.x inner.y inner.state inner.locals
    let hr ← checkWith env conversion U (stateType :: natType :: context) result optionState exposure
    let proof := if functional then body.functionalProof else body.imperativeProof
    have correct : env.HasType U (stateType :: natType :: context) proof (eqState result body.sourceCore.val) := by
      cases functional <;> first | exact body.imperativeCorrect | exact body.functionalCorrect
    have same := body.sourceCore.property.unique normal.plainCore.property
    let composed ← LeanLoopNormalization.args native ``LoopFacts.compose
      [⟨result,optionState,hr.down⟩,⟨normal.plainCore.val,optionState,normal.plainTyped⟩,
       ⟨normal.sourceCore.val,LeanLoopNormalization.optionStep,normal.sourceTyped⟩,
       ⟨proof,eqState result normal.plainCore.val,by simpa only [same] using correct⟩,
       ⟨normal.proof,_,normal.correct⟩]
    let expected := LeanLoopNormalization.stepEq (LeanLoopNormalization.liftValue result)
      (applications (cb.val.liftN 2) [.bvar 1,.bvar 0])
    let q ← LeanLoopNormalization.cast conversion composed expected
    let closed : LeanProofApplication.Typed env U context :=
      ⟨.lam natType (.lam stateType q.val),.forallE natType (.forallE stateType expected),
        .lamDF hNat.down (.lamDF hState.down q.property)⟩
    LeanLoopNormalization.args native (if functional then ``LoopFacts.functional else ``LoopFacts.imperative)
      [⟨code count.emitted,expressionType,he.down⟩,⟨c,ct,hct.down⟩,
       ⟨inputs.i,intType,inputs.indexTyped⟩,⟨inputs.x,intType,inputs.leftTyped⟩,
       ⟨inputs.y,intType,inputs.rightTyped⟩,⟨inputs.state,stateType,inputs.stateTyped⟩,
       ⟨inputs.locals,intList,hl.down⟩,n,⟨cb.val,callbackType,hc.down⟩,hn,closed]
  let pi ← one false
  let pf ← one true
  let imperative := Imperative.Cmd.forRange count.emitted body.imperative
  let functional := Functional.Term.forRange 0 count.emitted body.functional (.yield 0)
  if si : pi.type = eqState (imperativeEval (imperativeCode imperative)
      inputs.i inputs.x inputs.y inputs.state inputs.locals) sc.val then
    if sf : pf.type = eqState (functionalEval (functionalCode functional)
        inputs.i inputs.x inputs.y inputs.state inputs.locals) sc.val then
      return ⟨imperative,functional,sc,hs.down,pi.term,pf.term,si ▸ pi.correct,sf ▸ pf.correct⟩
    else none
  else none


def hoisted (native : Lean.Environment) (inputs : LeanIREvaluationCompiler.Inputs env U context)
    (conversion : Conversion env) (exposure : Exposure env)
    (normal : LeanReadHoisting.Artifact (env := env) (U := U) (context := context) source)
    (body : Artifact inputs normal.plain) : Option (Artifact inputs source) := do
  have same := body.sourceCore.property.unique normal.plainCore.property
  let one (functional : Bool) : Option (LeanProofApplication.Typed env U context) := do
    let result := if functional then functionalEval (functionalCode body.functional)
        inputs.i inputs.x inputs.y inputs.state inputs.locals
      else imperativeEval (imperativeCode body.imperative) inputs.i inputs.x inputs.y inputs.state inputs.locals
    let hr ← checkWith env conversion U context result optionState exposure
    let proof := if functional then body.functionalProof else body.imperativeProof
    have correct : env.HasType U context proof (eqState result normal.plainCore.val) := by
      cases functional
      · simpa only [same] using body.imperativeCorrect
      · simpa only [same] using body.functionalCorrect
    LeanLoopNormalization.args native ``ReadHoistingFacts.transport
      [⟨result,optionState,hr.down⟩,⟨normal.plainCore.val,optionState,normal.plainTyped⟩,
       ⟨normal.sourceCore.val,optionState,normal.sourceTyped⟩,
       ⟨proof,_,correct⟩,⟨normal.proof,_,normal.correct⟩]
  let pi ← one false
  let pf ← one true
  let hi ← LeanLoopNormalization.cast conversion pi (eqState
    (imperativeEval (imperativeCode body.imperative) inputs.i inputs.x inputs.y inputs.state inputs.locals) normal.sourceCore.val)
  let hf ← LeanLoopNormalization.cast conversion pf (eqState
    (functionalEval (functionalCode body.functional) inputs.i inputs.x inputs.y inputs.state inputs.locals) normal.sourceCore.val)
  return ⟨body.imperative,body.functional,normal.sourceCore,normal.sourceTyped,hi.val,hf.val,hi.property,hf.property⟩

/-- First effectful entry: genuine finite-array updates. Both failed writes
    and successful writes are preserved, without assuming valid indices. -/
def compile (native : Lean.Environment) {context : List VExpr} (inputs : LeanIREvaluationCompiler.Inputs env U context)
    (conversion : Conversion env) (exposure : Exposure env) :
    Nat → (source : Lean.Expr) → Option (Artifact inputs source)
  | 0, _ => none
  | fuel+1, .app (.app readBindHead first) (.lam _ (.const ``Int []) body _) => do
      let a ← read native inputs conversion exposure fuel first
      let later ← readInputs inputs
      let b ← compile (context := intType :: context) native later conversion exposure fuel body
      readBinding native inputs conversion exposure a later b
  | fuel+1, .app (.app bindHead first) (.lam name (.const ``State []) body binder) => do
      let source := Lean.Expr.app (.app bindHead first) (.lam name (.const ``State []) body binder)
      if let some normal := LeanReadHoisting.compile (context := context) native conversion exposure source then
        if let some compiled := compile native inputs conversion exposure fuel normal.plain then
          if let some result := hoisted native inputs conversion exposure normal compiled then
            return result
      let a ← compile native inputs conversion exposure fuel first
      let laterInputs ← nextInputs inputs
      let b ← compile (context := stateType :: context) native laterInputs conversion exposure fuel body
      sequence native inputs conversion exposure a laterInputs b
  | fuel+1, (.letE name type value body flag) => do
      let next ← compile native inputs conversion exposure fuel (LeanBindings.instantiate value body)
      letValue inputs conversion exposure (.letE name type value body flag) next
  | fuel+1, (.app (.lam name type body binder) value) => do
      let next ← compile native inputs conversion exposure fuel (LeanBindings.instantiate value body)
      letValue inputs conversion exposure (.app (.lam name type body binder) value) next
  | fuel+1, conditional test decision yes no => do
      let c ← LeanSourceToIR.compile native inputs conversion exposure fuel test
      let a ← compile native inputs conversion exposure fuel yes
      let b ← compile native inputs conversion exposure fuel no
      branch native inputs conversion exposure c decision a b
  | fuel+1, .app (.app (.app (.app (.const ``State.write []) state) array) address) value => do
      let address ← LeanSourceToIR.compile native inputs conversion exposure fuel address
      let value ← LeanSourceToIR.compile native inputs conversion exposure fuel value
      store native inputs conversion exposure state array address value
  | fuel+1, .mdata _ source => do
      let a ← compile native inputs conversion exposure fuel source
      return { a with sourceCore := ⟨a.sourceCore.val,.metadata a.sourceCore.property⟩ }
  | fuel+1, source => do
      if let some (count,callback,originalBody) := loopParts source then
        let count ← LeanSourceToIR.compile native inputs conversion exposure fuel count
        let inner ← loopInputs inputs
        let normal ← LeanLoopNormalization.compile (context := stateType :: natType :: context) native conversion exposure fuel originalBody
        let body ← compile (context := stateType :: natType :: context) native inner conversion exposure fuel normal.plain
        loop native inputs conversion exposure source callback count inner normal body
      else returnState native inputs conversion exposure source

end IRComparison.LeanSourceBody
