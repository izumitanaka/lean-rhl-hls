import IRComparison.Frontend.LeanStructuralConversion
import IRComparison.Frontend.LeanCertifiedScalar
import IRComparison.Core.ScalarBackends
import IRComparison.Frontend.LeanEnvironmentProvenance

namespace IRComparison.LeanEntryEnvironment
open Lean4Lean LeanTyped LeanIRQuotation

/-- Collect declarations structurally; this does not evaluate the input. -/
def constants : Lean.Expr → List Lean.Name
  | .const name _ => [name]
  | .app f x => constants f ++ constants x
  | .lam _ ty b _ | .forallE _ ty b _ => constants ty ++ constants b
  | .letE _ ty value body _ => constants ty ++ constants value ++ constants body
  | .mdata _ b | .proj _ _ b => constants b
  | _ => []

/-- Imported signatures and reduction equations retain their native provenance.
    This record does not assert Ordered for the whole imported environment. -/
structure Loaded (native : Lean.Environment) (name : Lean.Name) where
  model : VEnv
  faithful : LeanEnvironmentProvenance.Faithful native model
  conversion : LeanTypeInference.Conversion model
  exposure : LeanTypeInference.Exposure model
  source : LeanTypeReduction.Definition native name
  registered : model.defeqs source.equation

def load (native : Lean.Environment) (name : Lean.Name) (extra : List Lean.Name := []) : Option (Loaded native name) := do
  let source ← LeanTypeReduction.load native name
  let names := (name :: constants source.declaration.value ++ extra ++
      [``List, ``List.nil, ``List.cons, ``Int.toNat, ``IRComparison.Expr.local, ``IRComparison.Expr.natIndex,
        ``ScopedFacts.literal, ``ScopedFacts.index, ``ScopedFacts.left, ``ScopedFacts.right,
        ``ScopedFacts.add, ``ScopedFacts.sub, ``ScopedFacts.mul, ``ScopedFacts.div, ``ScopedFacts.select,
        ``ScopedFacts.localZero, ``ScopedFacts.localSucc, ``ScopedFacts.natIndex,
        ``ScalarBackends.imperative_correct, ``ScalarBackends.functional_correct,
        ``ScalarBackends.imperative, ``ScalarBackends.functional, ``Nat.zero, ``Nat.succ, ``Int.ofNat, ``Int, ``Int.ofNat, ``Int.neg, ``Int.add, ``Int.sub, ``Int.mul, ``Int.ediv,
        ``IRComparison.Expr, ``IRComparison.Expr.lit, ``IRComparison.Expr.index,
        ``IRComparison.Expr.left, ``IRComparison.Expr.right, ``IRComparison.Expr.add, ``IRComparison.Expr.sub,
        ``IRComparison.Expr.mul, ``IRComparison.Expr.div, ``IRComparison.Expr.select, ``State, ``Option, ``Option.some, ``IRComparison.Expr.eval,
        ``Facts.literal, ``Facts.index, ``Facts.left, ``Facts.right,
        ``Facts.add, ``Facts.sub, ``Facts.mul, ``Facts.div, ``Facts.select, ``selectValue,
        ``Standard.add, ``Standard.sub, ``Standard.mul, ``Standard.div, ``Standard.literal, ``LeanLiteralNormalization.elaboratedFact, ``LeanNegNormalization.coreFact, ``LeanNegNormalization.surfaceFact,
        ``Standard.intRefl, ``Standard.intTrans, ``Standard.intCongr,
        ``LeanIRTransport.transport, ``LeanSelectBridge.fact, ``Eq, ``optParam, ``outParam, ``Decidable, ``DecidableEq]).eraseDups
  let base ← match installed : LeanLibrary.installTypes native VEnv.empty names with
    | none => none
    | some env => some (⟨env,LeanEnvironmentProvenance.install_types names installed⟩ :
        {env // LeanEnvironmentProvenance.Faithful native env})
  let identity ← LeanTypeAliases.load native ``outParam
  let aliases := identity.install base.val
  let decEq ← LeanTypeReduction.load native ``DecidableEq
  let optional ← LeanTypeReduction.load native ``optParam
  let sourceDef := source
  let model := sourceDef.install (optional.install (decEq.install aliases))
  let baseConversion := LeanUniverseConversion.orElse
    (identity.conversion (env := model) (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (LeanUniverseConversion.conversion model))
    (LeanUniverseConversion.conversion model)
  let optionalRules : List (LeanTypeReduction.Rule model) :=
    [⟨native,``optParam,optional,Or.inr (Or.inl rfl)⟩]
  let rules : List (LeanTypeReduction.Rule model) :=
    ⟨native,``DecidableEq,decEq,Or.inr (Or.inr (Or.inl rfl))⟩ :: optionalRules
  let simpleConversion := LeanTypeReduction.conversion optionalRules baseConversion
  let simpleExposure : LeanTypeInference.Exposure model := fun U ctx e =>
    LeanTypeReduction.expose rules simpleConversion U ctx e
  let conversion := LeanStructuralConversion.conversion model simpleConversion simpleExposure
  let exposure : LeanTypeInference.Exposure model := fun U ctx e =>
    LeanTypeReduction.expose rules conversion U ctx e
  have faithful := LeanEnvironmentProvenance.install_definition
    (LeanEnvironmentProvenance.install_definition
      (LeanEnvironmentProvenance.install_definition
        (LeanEnvironmentProvenance.install_alias base.property identity) decEq) optional) sourceDef
  return ⟨model,faithful,conversion,exposure,sourceDef,Or.inl rfl⟩

structure Result (native : Lean.Environment) (name : Lean.Name) where
  library : Loaded native name
  compiled : LeanCertifiedScalar.Result native library.model name

def compile (native : Lean.Environment) (name : Lean.Name) (fuel : Nat := 32) :
    Option (Result native name) := do
  let library ← load native name
  let compiled ← LeanCertifiedScalar.compile native library.model library.conversion library.exposure name fuel
  return ⟨library,compiled⟩

end IRComparison.LeanEntryEnvironment
