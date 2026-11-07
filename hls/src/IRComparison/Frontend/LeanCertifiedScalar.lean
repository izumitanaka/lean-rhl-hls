import IRComparison.Frontend.LeanSourceToIR
import IRComparison.Frontend.LeanSourceEntry

namespace IRComparison.LeanCertifiedScalar
open Lean4Lean LeanTyped LeanTypeInference LeanIRQuotation LeanIREvaluation

def context : List VExpr := [intType,intType,intType,stateType]

def Canonical (inputs : LeanIREvaluationCompiler.Inputs env 0 context) : Prop :=
  inputs.i = .bvar 2 ∧ inputs.x = .bvar 1 ∧ inputs.y = .bvar 0 ∧ inputs.state = .bvar 3 ∧ inputs.locals = nilInts

def parameters (env : VEnv) : Option {inputs : LeanIREvaluationCompiler.Inputs env 0 context // Canonical inputs} := do
  let hi ← check env 0 context (.bvar 2) intType
  let hx ← check env 0 context (.bvar 1) intType
  let hy ← check env 0 context (.bvar 0) intType
  let hs ← check env 0 context (.bvar 3) stateType
  return ⟨⟨.bvar 2,.bvar 1,.bvar 0,.bvar 3,hi.down,hx.down,hy.down,hs.down,nilInts⟩, rfl, rfl, rfl, rfl, rfl⟩

structure Result (nativeEnv : Lean.Environment) (env : VEnv) (name : Lean.Name) where
  original : LeanSourceEntry.Header nativeEnv name
  inputs : LeanIREvaluationCompiler.Inputs env 0 context
  canonical : Canonical inputs
  body : LeanSourceToIR.Artifact inputs original.body
  bridge : LeanIRTransport.Result inputs original.body body.emitted

/-- All source and evaluator equalities are constructed recursively by proved
    procedures. No proposed source/IR equivalence is sent to a checker. -/
def compile (nativeEnv : Lean.Environment) (env : VEnv)
    (conversion : Conversion env) (exposure : Exposure env) (name : Lean.Name)
    (letFuel : Nat := 32) : Option (Result nativeEnv env name) := do
  let original ← LeanSourceEntry.load nativeEnv name
  let ⟨inputs,canonical⟩ ← parameters env
  let body ← LeanSourceToIR.compile nativeEnv inputs conversion exposure letFuel original.body
  let bridge ← LeanIRTransport.connect nativeEnv inputs conversion exposure body.sourceCore body.sourceTyped
    body.target body.sourceProof body.sourceEquality
  return ⟨original,inputs,canonical,body,bridge⟩

theorem Result.correct (r : Result nativeEnv env name) :
    Represents r.original.declaration.value (intLambdas 3 r.bridge.sourceCore.val) ∧
    env.HasType 0 context r.bridge.proof
      (eqResult (eval (code r.body.emitted) r.inputs.i r.inputs.x r.inputs.y r.inputs.state r.inputs.locals)
        (someInt r.bridge.sourceCore.val)) :=
  ⟨r.original.represents_function r.bridge.sourceCore.property, r.bridge.correct⟩

end IRComparison.LeanCertifiedScalar
