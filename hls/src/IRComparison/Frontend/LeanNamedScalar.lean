import IRComparison.Frontend.LeanEntryEnvironment

namespace IRComparison.LeanNamedScalar
open Lean4Lean LeanTyped LeanIRQuotation LeanIREvaluation

variable {env : VEnv} {U : Nat} {context : List VExpr}

def someHead : VExpr := .app (.const ``Option.some [.zero]) intType
def eqHead : VExpr := .app (.const ``Eq [.succ .zero]) optionInt

theorem result_congr
    (someTyped : env.HasType U context someHead (.forallE intType optionInt))
    (eqTyped : env.HasType U context eqHead (.forallE optionInt (.forallE optionInt (.sort .zero))))
    (resultTyped : env.HasType U context result optionInt)
    (sourceEq : env.IsDefEq U context source body intType) :
    env.IsDefEq U context (eqResult result (someInt source))
      (eqResult result (someInt body)) (.sort .zero) := by
  have someEq := VEnv.IsDefEq.appDF someTyped sourceEq
  simp only [optionInt, VExpr.inst, List.map_cons, List.map_nil] at someEq
  have head := VEnv.IsDefEq.appDF eqTyped resultTyped
  simp only [optionInt, VExpr.inst, List.map_cons, List.map_nil] at head
  exact VEnv.IsDefEq.appDF head someEq

structure Result (native : Lean.Environment) (name : Lean.Name) where
  entry : LeanEntryEnvironment.Result native name
  proof : VExpr
  correct : entry.library.model.HasType 0 LeanCertifiedScalar.context proof
    (eqResult
      (eval (code entry.compiled.body.emitted) entry.compiled.inputs.i entry.compiled.inputs.x
        entry.compiled.inputs.y entry.compiled.inputs.state entry.compiled.inputs.locals)
      (someInt (applications (.const name [])
        [entry.compiled.inputs.i, entry.compiled.inputs.x, entry.compiled.inputs.y])))

/-- Delta and beta computations connect the already constructed IR proof to
    the original named definition. No candidate source/target equality is
    submitted to a general-purpose equality checker. -/
def compile (native : Lean.Environment) (name : Lean.Name) (fuel : Nat := 32) :
    Option (Result native name) := do
  let entry ← LeanEntryEnvironment.compile native name fuel
  let r := entry.compiled
  let library := entry.library
  let args := [r.inputs.i,r.inputs.x,r.inputs.y]
  let source := applications (.const name []) args
  let rules : List (LeanTypeReduction.Rule library.model) :=
    [⟨native,name,library.source,library.registered⟩]
  let reduced ← LeanTypeReduction.step rules library.conversion 0 LeanCertifiedScalar.context
    library.exposure source
  if same : reduced.val.1 = r.bridge.sourceCore.val then
    if typeSame : reduced.val.2 = intType then
      let someTyped ← LeanTypeInference.check library.model 0 LeanCertifiedScalar.context someHead
        (.forallE intType optionInt)
      let eqTyped ← LeanTypeInference.check library.model 0 LeanCertifiedScalar.context eqHead
        (.forallE optionInt (.forallE optionInt (.sort .zero)))
      let resultTyped ← LeanTypeInference.checkWith library.model library.conversion 0 LeanCertifiedScalar.context
        (eval (code r.body.emitted) r.inputs.i r.inputs.x r.inputs.y r.inputs.state r.inputs.locals) optionInt library.exposure
      have sourceEq : library.model.IsDefEq 0 LeanCertifiedScalar.context source r.bridge.sourceCore.val intType :=
        by simpa only [same,typeSame] using reduced.property
      let conversion := result_congr someTyped.down eqTyped.down resultTyped.down sourceEq
      return ⟨entry,r.bridge.proof,.defeq conversion.symm r.bridge.correct⟩
    else none
  else none

/-- The entry proof quantifies all runtime states and all three input values. -/
def specification (name : Lean.Name) (emitted : Expr) : VExpr :=
  .forallE stateType (.forallE intType (.forallE intType (.forallE intType
    (eqResult (eval (code emitted) (.bvar 2) (.bvar 1) (.bvar 0) (.bvar 3))
      (someInt (applications (.const name []) [.bvar 2,.bvar 1,.bvar 0]))))))

def Result.closedProof (r : Result native name) : VExpr :=
  .lam stateType (intLambdas 3 r.proof)

theorem Result.closed_correct (r : Result native name)
    (stateDeclared : r.entry.library.model.constants ``State = some ⟨0,.sort (.succ .zero)⟩)
    (intDeclared : r.entry.library.model.constants ``Int = some ⟨0,.sort (.succ .zero)⟩) :
    r.entry.library.model.HasType 0 [] r.closedProof
      (specification name r.entry.compiled.body.emitted) := by
  have h := r.correct
  obtain ⟨hi,hx,hy,hs,hl⟩ := r.entry.compiled.canonical
  rw [hi,hx,hy,hs,hl] at h
  have stateTyped : r.entry.library.model.HasType 0 [] stateType (.sort (.succ .zero)) :=
    .constDF stateDeclared (by simp) (by simp) rfl .nil
  exact .lamDF stateTyped (.lamDF (int_hasType intDeclared _)
    (.lamDF (int_hasType intDeclared _) (.lamDF (int_hasType intDeclared _) h)))

end IRComparison.LeanNamedScalar
