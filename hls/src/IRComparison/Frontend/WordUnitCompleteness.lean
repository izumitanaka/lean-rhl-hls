import IRComparison.Frontend.WordStateLetCompleteness

namespace IRComparison.WordFrontend.Certificate.UnitStep
open Lean4Lean LeanTyped LeanTypeInference
variable {casts proofCasts : TypeCasts} [Arithmetic.Includes casts] [Arithmetic.Includes proofCasts]
open Arithmetic (SourceCasts)
set_option maxHeartbeats 1200000

def pureUnit : VExpr := .app (Return.Form.pure.headerFor unitType) unitValue
def nativePureUnit : Lean.Expr := Lean.mkApp4 (.const ``Pure.pure [.zero,.zero])
  (.const ``Option [.zero]) Return.nativePureInstance nativeUnitType nativeUnitValue

def source (binder : Lean.Name) (nextBody : Lean.Expr) (info : Lean.BinderInfo) : Lean.Expr :=
  Lean.mkApp2 (bindHead nativeUnitType stepType) nativePureUnit (.lam binder nativeUnitType nextBody info)

def signature : VExpr := .forallE (optionType stateType)
  (.forallE (.forallE unitType (optionType Step.stepState))
    (.forallE (Step.expected (.bvar 1) (.app (.bvar 0) unitValue))
      (Step.expected (.bvar 2) (applications (optionBindHeader unitType Step.stepState) [pureUnit,.bvar 1]))))

theorem pure_represents : Represents nativePureUnit pureUnit :=
  .app (.app (.app (.app (.constant rfl) (.constant rfl))
    (.app (.app (.constant rfl) (.constant rfl))
      (.app (.app (.constant rfl) (.constant rfl)) (.constant rfl)))) (.constant rfl)) (.constant rfl)

theorem pure_typed (steps : Step.Signatures env) (units : Signatures env) :
    DirectTyping env 0 ctx pureUnit (optionType unitType) := by
  have header := steps.headerFor_typed (ctx := ctx) Return.Form.pure units.type_typed (by trivial)
  exact DirectTyping.application header units.value_typed

theorem fact_typed (plainTyped : CastTyping env 0 casts ctx plain (optionType stateType))
    (nextTyped : CastTyping env 0 casts ctx next (.forallE unitType (optionType Step.stepState)))
    (proofTyped : CastTyping env 0 casts ctx proof actual)
    (beta : casts ctx actual (Step.expected plain (.app next unitValue)))
    (registered : env.constants ``WordLoopFacts.bindUnit = some ⟨0,signature⟩) :
    CastTyping env 0 casts ctx (applications (.const ``WordLoopFacts.bindUnit []) [plain,next,proof])
      (Step.expected plain (applications (optionBindHeader unitType Step.stepState) [pureUnit,next])) := by
  have h : CastTyping env 0 casts ctx (.const ``WordLoopFacts.bindUnit []) signature :=
    .constant registered (by simp) rfl
  have a1 := CastTyping.application h plainTyped
  simp only [signature,Step.expected,Step.lifted,equalValues,applications,optionType,stateType,
    Step.stepState,unitType,unitValue,pureUnit,Return.Form.headerFor,Return.pureInstance,
    optionBindHeader,VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower,Nat.reduceAdd] at a1
  have a2 := CastTyping.application a1 nextTyped
  simp only [VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower,Nat.reduceAdd,
    ← VExpr.lift_instN_lo,VExpr.inst_lift] at a2
  have cast := beta
  simp only [Step.expected,Step.lifted,equalValues,applications,optionType,stateType,Step.stepState,unitValue] at cast
  simpa only [Step.expected,Step.lifted,equalValues,applications,optionType,stateType,Step.stepState,
    unitType,unitValue,pureUnit,Return.Form.headerFor,Return.pureInstance,optionBindHeader,
    VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower,Nat.reduceAdd,
    ← VExpr.lift_instN_lo,VExpr.inst_lift] using CastTyping.convertedApplication a2 proofTyped cast

end IRComparison.WordFrontend.Certificate.UnitStep
