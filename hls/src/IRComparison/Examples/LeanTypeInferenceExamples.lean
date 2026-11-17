import IRComparison.Frontend.LeanLetNormalization
import IRComparison.Examples.LeanScalarExamples

namespace IRComparison.LeanTypeInferenceExamples
open Lean Elab Command LeanTyped

private def constants : Lean.Expr → List Lean.Name
  | .const name _ => [name]
  | .app f x => constants f ++ constants x
  | .lam _ ty b _ | .forallE _ ty b _ => constants ty ++ constants b
  | .letE _ ty value body _ => constants ty ++ constants value ++ constants body
  | .mdata _ b | .proj _ _ b => constants b
  | _ => []

/- Exercise the proved entry with real declarations and proved type reduction. -/
def primitiveMean (_i x y : Int) : Int := Int.ediv (Int.add x y) (Int.ofNat 2)

def anotherIdentity (α : Sort u) : Sort u := α

run_cmd do
  let native ← getEnv
  let some _ := LeanTypeAliases.load native ``anotherIdentity
    | throwError "identity alias recognition incorrectly depended on the name outParam"
  if (LeanTypeAliases.load native ``Int.add).isSome then
    throwError "non-identity definition was accepted as an identity alias"
  for name in [``primitiveMean, ``LeanScalarExamples.mean,
      ``LeanScalarExamples.shadow, ``LeanScalarExamples.signed, ``LeanScalarExamples.choose] do
    let some source := LeanDefinition.compile native name | throwError "source extraction failed"
    let names := (constants source.declaration.value ++ [``Nat.zero, ``Nat.succ, ``Int.ofNat, ``outParam, ``Decidable, ``DecidableEq, ``Eq,
      ``Int.add, ``Int.sub, ``Int.mul, ``Int.ediv,
      ``Standard.add, ``Standard.sub, ``Standard.mul, ``Standard.div, ``Standard.literal, ``LeanNegNormalization.coreFact, ``LeanNegNormalization.surfaceFact,
      ``Standard.intRefl, ``Standard.intTrans, ``Standard.intCongr]).eraseDups
    let some env := LeanLibrary.installTypes native Lean4Lean.VEnv.empty names
      | throwError "standard type import failed for {name}"
    let some entry := LeanTypeAliases.load native ``outParam
      | throwError "outParam definition did not match the checked identity-alias shape"
    let withAliases := entry.install env
    let some defn := LeanTypeReduction.load native ``DecidableEq
      | throwError "DecidableEq definition import failed"
    let expanded := defn.install withAliases
    let conversion := LeanUniverseConversion.orElse
      (entry.conversion (env := expanded) (Or.inr (Or.inl rfl)))
      (LeanUniverseConversion.conversion expanded)
    let rules : List (LeanTypeReduction.Rule expanded) :=
      [⟨native, ``DecidableEq, defn, Or.inl rfl⟩]
    let exposure : LeanTypeInference.Exposure expanded := fun U ctx e =>
      LeanTypeReduction.expose rules conversion U ctx e
    let context := List.replicate 3 intType
    let result := LeanTypeInference.normalize native expanded 0 context source.function.body conversion exposure
    for fuel in [0,1,8] do
      let some rewritten := LeanLetNormalization.leading native expanded 0 context conversion exposure
        fuel source.function.body | throwError "proved let normalization failed at fuel {fuel}"
      if name == ``LeanScalarExamples.shadow && fuel == 8 then
        if let .letE .. := rewritten.expression then
          throwError "leading lets were not eliminated"
      let some code := LeanScalar.compile LeanScalar.initialLayout rewritten.expression
        | throwError "let result was rejected by scalar compiler"
      for (i,x,y) in ([(0,2,4), (3,-4,0), (-2,7,-3)] : List (Int × Int × Int)) do
        let state : State := ⟨fun _ => 0, fun _ => #[]⟩
        unless code.native i x y state == source.function.scalar.native i x y state do
          throwError "let normalization changed scalar result"
    unless result.isSome do
      throwError "unexpected type-inference result for {name}"
    logInfo m!"{name}: normalization entry constructed its typing obligations"


end IRComparison.LeanTypeInferenceExamples
