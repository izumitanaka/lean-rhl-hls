import IRComparison.Frontend.LeanNamedScalar
import IRComparison.Frontend.LeanProofApplication

namespace IRComparison.LeanScalarPipeline
open Lean4Lean LeanTyped LeanIRQuotation LeanIREvaluation

inductive Backend where
  | imperative | functional

def Backend.program : Backend → Lean.Name
  | .imperative => ``ScalarBackends.imperative
  | .functional => ``ScalarBackends.functional

def Backend.evaluator : Backend → Lean.Name
  | .imperative => ``Imperative.Program.eval
  | .functional => ``Functional.Program.eval

def Backend.fact : Backend → Lean.Name
  | .imperative => ``ScalarBackends.imperative_correct
  | .functional => ``ScalarBackends.functional_correct

/-- Explicit final statement: for all loop parameters, inputs and states,
    this backend's generated program equals the ordinary named source loop. -/
def specification (backend : Backend) (name : Lean.Name) (emitted : Expr) : VExpr :=
  let parameters := [.bvar 7,.bvar 6,.bvar 5,.bvar 4,.bvar 3,.bvar 2]
  let program := applications (.const backend.program []) (code emitted :: parameters)
  let result := applications (.const backend.evaluator []) [.bvar 1,program,.bvar 0]
  let source := applications (.const ``ScalarBackends.runSource [])
    ((.const name []) :: parameters ++ [.bvar 1,.bvar 0])
  let statement := applications (.const ``Eq [.succ .zero])
    [.app (.const ``Option [.zero]) stateType,result,source]
  [(.const ``Nat []),intType,intType,(.const ``Nat []),intType,intType,
    (.const ``Input []),stateType].foldr VExpr.forallE statement

structure Proof (source : LeanNamedScalar.Result native name) (backend : Backend) where
  term : VExpr
  correct : source.entry.library.model.HasType 0 [] term
    (specification backend name source.entry.compiled.body.emitted)

/-- Both proofs refer to the same original declaration and emitted expression. -/
structure Result (native : Lean.Environment) (name : Lean.Name) where
  source : LeanNamedScalar.Result native name
  imperativeProof : Proof source .imperative
  functionalProof : Proof source .functional

private def specialize (native : Lean.Environment) (name : Lean.Name)
    (source : LeanNamedScalar.Result native name) (backend : Backend)
    (premise : LeanProofApplication.Typed source.entry.library.model 0 []) :
    Option (Proof source backend) := do
  let model := source.entry.library.model
  let emitted := source.entry.compiled.body.emitted
  let fact ← LeanProofApplication.constant native model 0 [] backend.fact
  let typedCode ← LeanTypeInference.check model 0 [] (code emitted) expressionType
  let typedSource ← LeanTypeInference.check model 0 [] (.const name []) scalarType
  let a ← LeanProofApplication.apply fact ⟨code emitted,expressionType,typedCode.down⟩
  let b ← LeanProofApplication.apply a ⟨.const name [],scalarType,typedSource.down⟩
  let result ← LeanProofApplication.apply b premise
  if shape : result.type = specification backend name emitted then
    return ⟨result.term, shape ▸ result.correct⟩
  else none

def compile (native : Lean.Environment) (name : Lean.Name) (fuel : Nat := 32) :
    Option (Result native name) := do
  let source ← LeanNamedScalar.compile native name fuel
  let model := source.entry.library.model
  if hs : model.constants ``State = some ⟨0,.sort (.succ .zero)⟩ then
    if hi : model.constants ``Int = some ⟨0,.sort (.succ .zero)⟩ then
      let premise : LeanProofApplication.Typed model 0 [] :=
        ⟨source.closedProof, LeanNamedScalar.specification name source.entry.compiled.body.emitted,
          source.closed_correct hs hi⟩
      let imperativeProof ← specialize native name source .imperative premise
      let functionalProof ← specialize native name source .functional premise
      return ⟨source,imperativeProof,functionalProof⟩
    else none
  else none

def Result.imperative (r : Result native name) (reg : Nat)
    (start stride : Int) (count : Nat) (l right : Int) : Imperative.Program :=
  ScalarBackends.imperative r.source.entry.compiled.body.emitted reg start stride count l right

def Result.functional (r : Result native name) (reg : Nat)
    (start stride : Int) (count : Nat) (l right : Int) : Functional.Program :=
  ScalarBackends.functional r.source.entry.compiled.body.emitted reg start stride count l right

/-- Uniform guarantee of a successful compiler result. All model declarations
    have native provenance and both final theorem statements mention the exact
    source name and the exact emitted expression used by the executable targets. -/
theorem Result.correct (r : Result native name) :
    LeanEnvironmentProvenance.Faithful native r.source.entry.library.model ∧
    r.source.entry.library.model.HasType 0 [] r.imperativeProof.term
      (specification .imperative name r.source.entry.compiled.body.emitted) ∧
    r.source.entry.library.model.HasType 0 [] r.functionalProof.term
      (specification .functional name r.source.entry.compiled.body.emitted) :=
  ⟨r.source.entry.library.faithful,r.imperativeProof.correct,r.functionalProof.correct⟩

end IRComparison.LeanScalarPipeline
