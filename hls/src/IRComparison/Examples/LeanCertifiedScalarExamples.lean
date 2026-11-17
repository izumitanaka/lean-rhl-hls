import IRComparison.Frontend.LeanCertificate
import IRComparison.Examples.LeanScalarExamples

namespace IRComparison.LeanCertifiedScalarExamples
open Lean Elab Command Lean4Lean LeanTyped LeanIRQuotation

def nested (i x y : Int) : Int :=
  -(if x != 0 then
      let z := y + i
      z * z
    else Int.ediv (Int.add i y) 2)

def naturalLiteral (i x y : Int) : Int := i + x * y + Int.ofNat 2

run_cmd do
  let native ← getEnv
  for name in [``LeanScalarExamples.shadow, ``LeanScalarExamples.mean, ``LeanScalarExamples.signed,
      ``LeanScalarExamples.choose, ``nested, ``naturalLiteral] do
    let some result := LeanScalarPipeline.compile native name
      | throwError "named source-to-actual-IR proof construction failed for {name}"
    for (suffix,backend) in [("certifiedImperative", LeanScalarPipeline.Backend.imperative),
        ("certifiedFunctional", LeanScalarPipeline.Backend.functional)] do
      let proofName := Lean.Name.str name suffix
      liftCoreM <| Lean.addDecl (LeanCertificate.declaration proofName result backend)
      for assumption in (← collectAxioms proofName) do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains assumption do
          throwError "unexpected certificate assumption {assumption}"
    logInfo "ordinary Lean source: constructed closed proofs for both optimized IR backends"

run_cmd do
  let native ← getEnv
  for name in [``LeanScalarExamples.helperCall, ``LeanScalarExamples.unsafeMean, ``LeanScalarExamples.opaqueMean] do
    if (LeanScalarPipeline.compile native name).isSome then
      throwError "unsupported source was silently accepted: {name}"

end IRComparison.LeanCertifiedScalarExamples
