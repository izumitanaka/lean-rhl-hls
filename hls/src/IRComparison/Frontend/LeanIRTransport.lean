import IRComparison.Frontend.LeanIREvaluationCompiler

namespace IRComparison.LeanIRTransport
open Lean4Lean LeanTyped LeanIRQuotation

theorem transport (result : Option Int) (source value : Int)
    (hs : source = value) (he : result = some value) : result = some source := by
  rw [hs]
  exact he

def signature : VExpr :=
  .forallE optionInt (.forallE intType (.forallE intType
    (.forallE (eqInt (.bvar 1) (.bvar 0))
      (.forallE (eqResult (.bvar 3) (someInt (.bvar 1)))
        (eqResult (.bvar 4) (someInt (.bvar 3)))))))

variable {env : VEnv} {U : Nat} {context : List VExpr}

theorem apply_transport
    (registered : env.constants ``transport = some ⟨0, signature⟩)
    (hr : env.HasType U context result optionInt)
    (hs : env.HasType U context source intType) (hv : env.HasType U context value intType)
    (hp : env.HasType U context p (eqInt source value))
    (hq : env.HasType U context q (eqResult result (someInt value))) :
    env.HasType U context (applications (.const ``transport []) [result,source,value,p,q])
      (eqResult result (someInt source)) := by
  have fact := VEnv.HasType.const (U := U) (Γ := context) (ls := []) registered (by simp) rfl
  simp only [signature, intType, optionInt, eqInt, eqResult, someInt,
    VExpr.instL, VLevel.inst, List.map_cons, List.map_nil] at fact
  have a := VEnv.HasType.app fact hr
  simp only [Nat.reduceAdd, ← VExpr.lift_instN_lo, VExpr.inst_lift, VExpr.inst,
    VExpr.instVar_lower, VExpr.instVar_succ, VExpr.instVar_zero] at a
  have b := VEnv.HasType.app a hs
  simp only [Nat.reduceAdd, ← VExpr.lift_instN_lo, VExpr.inst_lift, VExpr.inst,
    VExpr.instVar_lower, VExpr.instVar_succ, VExpr.instVar_zero] at b
  have c := VEnv.HasType.app b hv
  simp only [Nat.reduceAdd, ← VExpr.lift_instN_lo, VExpr.inst_lift, VExpr.inst,
    VExpr.instVar_lower, VExpr.instVar_succ, VExpr.instVar_zero] at c
  have d := VEnv.HasType.app c hp
  simp only [Nat.reduceAdd, ← VExpr.lift_instN_lo, VExpr.inst_lift, VExpr.inst,
    VExpr.instVar_lower, VExpr.instVar_succ, VExpr.instVar_zero] at d
  have e := VEnv.HasType.app d hq
  simpa only [applications, eqResult, optionInt, someInt, intType, VExpr.inst,
    VExpr.inst_lift, VExpr.instVar_zero] using e

/-- A source equality and the actual target evaluator proof meet here. The
    result states Expr.eval(emitted code) = some(original source computation). -/
structure Result (inputs : LeanIREvaluationCompiler.Inputs env U context) (source : Lean.Expr) (emitted : Expr) where
  sourceCore : {v // Represents source v}
  proof : VExpr
  correct : env.HasType U context proof
    (eqResult (eval (code emitted) inputs.i inputs.x inputs.y inputs.state inputs.locals) (someInt sourceCore.val))

def connect (nativeEnv : Lean.Environment) (inputs : LeanIREvaluationCompiler.Inputs env U context)
    (conversion : LeanTypeInference.Conversion env) (exposure : LeanTypeInference.Exposure env)
    (sourceCore : {v // Represents source v})
    (sourceTyped : env.HasType U context sourceCore.val intType)
    (target : LeanIREvaluationCompiler.Artifact inputs emitted)
    (sourceProof : VExpr)
    (sourceEquality : env.HasType U context sourceProof (eqInt sourceCore.val target.value)) :
    Option (Result inputs source emitted) := do
  let _ ← loadFixedFact nativeEnv ``transport signature
  if registered : env.constants ``transport = some ⟨0, signature⟩ then
    let result := eval (code emitted) inputs.i inputs.x inputs.y inputs.state inputs.locals
    let resultTyped ← LeanTypeInference.checkWith env conversion U context result optionInt exposure
    return {
      sourceCore := sourceCore
      proof := applications (.const ``transport []) [result,sourceCore.val,target.value,sourceProof,target.proof]
      correct := apply_transport registered resultTyped.down sourceTyped target.valueTyped sourceEquality target.correct }
  else none

end IRComparison.LeanIRTransport
