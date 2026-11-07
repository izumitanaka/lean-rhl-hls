import IRComparison.Frontend.LeanIRQuotation

namespace IRComparison.LeanIREvaluation
open Lean4Lean LeanTyped LeanIRQuotation

def expressionType : VExpr := .const ``Expr []
def stateType : VExpr := .const ``State []

def binaryType (constructor primitive : Lean.Name) : VExpr :=
  .forallE expressionType (.forallE expressionType
    (.forallE intType (.forallE intType (.forallE intType (.forallE stateType
      (.forallE intType (.forallE intType
        (.forallE (eqResult (eval (.bvar 7) (.bvar 5) (.bvar 4) (.bvar 3) (.bvar 2)) (someInt (.bvar 1)))
          (.forallE (eqResult (eval (.bvar 7) (.bvar 6) (.bvar 5) (.bvar 4) (.bvar 3)) (someInt (.bvar 1)))
            (eqResult
              (eval (.app (.app (.const constructor []) (.bvar 9)) (.bvar 8))
                (.bvar 7) (.bvar 6) (.bvar 5) (.bvar 4))
              (someInt (.app (.app (.const primitive []) (.bvar 3)) (.bvar 2)))))))))))))

variable {env : VEnv} {U : Nat} {context : List VExpr}

def literalType : VExpr :=
  .forallE intType (.forallE intType (.forallE intType (.forallE intType (.forallE stateType
    (eqResult (eval (.app (.const ``Expr.lit []) (.bvar 4)) (.bvar 3) (.bvar 2) (.bvar 1) (.bvar 0))
      (someInt (.bvar 4)))))))

theorem apply_literal
    (registered : env.constants ``Facts.literal = some ⟨0, literalType⟩)
    (hn : env.HasType U context n intType)
    (hi : env.HasType U context i intType) (hx : env.HasType U context x intType)
    (hy : env.HasType U context y intType) (hs : env.HasType U context s stateType) :
    env.HasType U context (applications (.const ``Facts.literal []) [n,i,x,y,s])
      (eqResult (eval (.app (.const ``Expr.lit []) n) i x y s) (someInt n)) := by
  have fact := VEnv.HasType.const (U := U) (Γ := context) (ls := []) registered (by simp) rfl
  simp only [literalType, intType, stateType, eqResult, optionInt, someInt, eval, nilInts, applications,
    VExpr.instL, VLevel.inst, List.map_cons, List.map_nil] at fact
  have a := VEnv.HasType.app fact hn
  simp only [Nat.reduceAdd, ← VExpr.lift_instN_lo, VExpr.inst_lift, VExpr.inst,
    VExpr.instVar_lower, VExpr.instVar_succ, VExpr.instVar_zero] at a
  have b := VEnv.HasType.app a hi
  simp only [Nat.reduceAdd, ← VExpr.lift_instN_lo, VExpr.inst_lift, VExpr.inst,
    VExpr.instVar_lower, VExpr.instVar_succ, VExpr.instVar_zero] at b
  have c := VEnv.HasType.app b hx
  simp only [Nat.reduceAdd, ← VExpr.lift_instN_lo, VExpr.inst_lift, VExpr.inst,
    VExpr.instVar_lower, VExpr.instVar_succ, VExpr.instVar_zero] at c
  have d := VEnv.HasType.app c hy
  simp only [Nat.reduceAdd, ← VExpr.lift_instN_lo, VExpr.inst_lift, VExpr.inst,
    VExpr.instVar_lower, VExpr.instVar_succ, VExpr.instVar_zero] at d
  have e := VEnv.HasType.app d hs
  simpa only [applications, eqResult, optionInt, someInt, intType, eval, nilInts, VExpr.inst,
    VExpr.inst_lift, VExpr.instVar_zero] using e

inductive Slot where
  | index | left | right

def Slot.constructor : Slot → Lean.Name
  | .index => ``Expr.index
  | .left => ``Expr.left
  | .right => ``Expr.right

def Slot.fact : Slot → Lean.Name
  | .index => ``Facts.index
  | .left => ``Facts.left
  | .right => ``Facts.right

def Slot.value (slot : Slot) (i x y : VExpr) : VExpr :=
  match slot with | .index => i | .left => x | .right => y

def Slot.type (slot : Slot) : VExpr :=
  .forallE intType (.forallE intType (.forallE intType (.forallE stateType
    (eqResult (eval (.const slot.constructor []) (.bvar 3) (.bvar 2) (.bvar 1) (.bvar 0))
      (someInt (slot.value (.bvar 3) (.bvar 2) (.bvar 1)))))))

theorem apply_slot (slot : Slot)
    (registered : env.constants slot.fact = some ⟨0, slot.type⟩)
    (hi : env.HasType U context i intType) (hx : env.HasType U context x intType)
    (hy : env.HasType U context y intType) (hs : env.HasType U context s stateType) :
    env.HasType U context (applications (.const slot.fact []) [i,x,y,s])
      (eqResult (eval (.const slot.constructor []) i x y s) (someInt (slot.value i x y))) := by
  have fact := VEnv.HasType.const (U := U) (Γ := context) (ls := []) registered (by simp) rfl
  cases slot <;>
    simp only [Slot.type, Slot.constructor, Slot.fact, Slot.value, intType, stateType,
      eqResult, optionInt, someInt, eval, nilInts, applications, VExpr.instL, VLevel.inst,
      List.map_cons, List.map_nil] at fact ⊢
  all_goals
    have a := VEnv.HasType.app fact hi
    simp only [Nat.reduceAdd, ← VExpr.lift_instN_lo, VExpr.inst_lift, VExpr.inst,
      VExpr.instVar_lower, VExpr.instVar_succ, VExpr.instVar_zero] at a
    have b := VEnv.HasType.app a hx
    simp only [Nat.reduceAdd, ← VExpr.lift_instN_lo, VExpr.inst_lift, VExpr.inst,
      VExpr.instVar_lower, VExpr.instVar_succ, VExpr.instVar_zero] at b
    have c := VEnv.HasType.app b hy
    simp only [Nat.reduceAdd, ← VExpr.lift_instN_lo, VExpr.inst_lift, VExpr.inst,
      VExpr.instVar_lower, VExpr.instVar_succ, VExpr.instVar_zero] at c
    have d := VEnv.HasType.app c hs
    simpa only [VExpr.inst, VExpr.inst_lift, VExpr.instVar_zero] using d

/-- Instantiate a fixed theorem of the actual IR evaluator. The two child
    equalities are inputs to this constructor, to be supplied recursively. -/
theorem apply_binary
    (registered : env.constants theoremName = some ⟨0, binaryType constructor primitive⟩)
    (ha : env.HasType U context a expressionType) (hb : env.HasType U context b expressionType)
    (hi : env.HasType U context i intType) (hx : env.HasType U context x intType)
    (hy : env.HasType U context y intType) (hs : env.HasType U context s stateType)
    (hv : env.HasType U context v intType) (hw : env.HasType U context w intType)
    (hp : env.HasType U context p (eqResult (eval a i x y s) (someInt v)))
    (hq : env.HasType U context q (eqResult (eval b i x y s) (someInt w))) :
    env.HasType U context
      (applications (.const theoremName []) [a,b,i,x,y,s,v,w,p,q])
      (eqResult (eval (.app (.app (.const constructor []) a) b) i x y s)
        (someInt (.app (.app (.const primitive []) v) w))) := by
  have fact := VEnv.HasType.const (U := U) (Γ := context) (ls := []) registered (by simp) rfl
  simp only [binaryType, expressionType, stateType, intType, eqResult, optionInt, someInt,
    eval, nilInts, applications, VExpr.instL, VLevel.inst, List.map_cons, List.map_nil] at fact
  have a1 := VEnv.HasType.app fact ha
  simp only [Nat.reduceAdd, ← VExpr.lift_instN_lo, VExpr.inst_lift, VExpr.inst,
    VExpr.instVar_lower, VExpr.instVar_succ, VExpr.instVar_zero] at a1
  have a2 := VEnv.HasType.app a1 hb
  simp only [Nat.reduceAdd, ← VExpr.lift_instN_lo, VExpr.inst_lift, VExpr.inst,
    VExpr.instVar_lower, VExpr.instVar_succ, VExpr.instVar_zero] at a2
  have a3 := VEnv.HasType.app a2 hi
  simp only [Nat.reduceAdd, ← VExpr.lift_instN_lo, VExpr.inst_lift, VExpr.inst,
    VExpr.instVar_lower, VExpr.instVar_succ, VExpr.instVar_zero] at a3
  have a4 := VEnv.HasType.app a3 hx
  simp only [Nat.reduceAdd, ← VExpr.lift_instN_lo, VExpr.inst_lift, VExpr.inst,
    VExpr.instVar_lower, VExpr.instVar_succ, VExpr.instVar_zero] at a4
  have a5 := VEnv.HasType.app a4 hy
  simp only [Nat.reduceAdd, ← VExpr.lift_instN_lo, VExpr.inst_lift, VExpr.inst,
    VExpr.instVar_lower, VExpr.instVar_succ, VExpr.instVar_zero] at a5
  have a6 := VEnv.HasType.app a5 hs
  simp only [Nat.reduceAdd, ← VExpr.lift_instN_lo, VExpr.inst_lift, VExpr.inst,
    VExpr.instVar_lower, VExpr.instVar_succ, VExpr.instVar_zero] at a6
  have a7 := VEnv.HasType.app a6 hv
  simp only [Nat.reduceAdd, ← VExpr.lift_instN_lo, VExpr.inst_lift, VExpr.inst,
    VExpr.instVar_lower, VExpr.instVar_succ, VExpr.instVar_zero] at a7
  have a8 := VEnv.HasType.app a7 hw
  simp only [Nat.reduceAdd, ← VExpr.lift_instN_lo, VExpr.inst_lift, VExpr.inst,
    VExpr.instVar_lower, VExpr.instVar_succ, VExpr.instVar_zero] at a8
  have a9 := VEnv.HasType.app a8 hp
  simp only [Nat.reduceAdd, ← VExpr.lift_instN_lo, VExpr.inst_lift, VExpr.inst,
    VExpr.instVar_lower, VExpr.instVar_succ, VExpr.instVar_zero] at a9
  have a10 := VEnv.HasType.app a9 hq
  simpa only [applications, eqResult, optionInt, someInt, intType, eval, nilInts, VExpr.inst,
    VExpr.inst_lift, VExpr.instVar_zero] using a10

end IRComparison.LeanIREvaluation
