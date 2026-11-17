import IRComparison.Frontend.LeanIREvaluation

namespace IRComparison.LeanIRSelect
open Lean4Lean LeanTyped LeanIRQuotation LeanIREvaluation

def value (c a b : VExpr) : VExpr := applications (.const ``selectValue []) [c,a,b]

def signature : VExpr :=
  [expressionType, expressionType, expressionType, intType, intType, intType, stateType,
    intType, intType, intType,
    eqResult (eval (.bvar 9) (.bvar 6) (.bvar 5) (.bvar 4) (.bvar 3)) (someInt (.bvar 2)),
    eqResult (eval (.bvar 9) (.bvar 7) (.bvar 6) (.bvar 5) (.bvar 4)) (someInt (.bvar 2)),
    eqResult (eval (.bvar 9) (.bvar 8) (.bvar 7) (.bvar 6) (.bvar 5)) (someInt (.bvar 2))].foldr VExpr.forallE
      (eqResult
        (eval (applications (.const ``Expr.select []) [.bvar 12,.bvar 11,.bvar 10])
          (.bvar 9) (.bvar 8) (.bvar 7) (.bvar 6))
        (someInt (value (.bvar 5) (.bvar 4) (.bvar 3))))

variable {env : VEnv} {U : Nat} {context : List VExpr}

theorem apply_select
    (registered : env.constants ``Facts.select = some ⟨0, signature⟩)
    (hc : env.HasType U context c expressionType)
    (ha : env.HasType U context a expressionType) (hb : env.HasType U context b expressionType)
    (hi : env.HasType U context i intType) (hx : env.HasType U context x intType)
    (hy : env.HasType U context y intType) (hs : env.HasType U context s stateType)
    (hv : env.HasType U context v intType) (ht : env.HasType U context t intType)
    (hf : env.HasType U context f intType)
    (hp : env.HasType U context p (eqResult (eval c i x y s) (someInt v)))
    (hq : env.HasType U context q (eqResult (eval a i x y s) (someInt t)))
    (hr : env.HasType U context r (eqResult (eval b i x y s) (someInt f))) :
    env.HasType U context (applications (.const ``Facts.select []) [c,a,b,i,x,y,s,v,t,f,p,q,r])
      (eqResult (eval (applications (.const ``Expr.select []) [c,a,b]) i x y s)
        (someInt (value v t f))) := by
  have fact := VEnv.HasType.const (U := U) (Γ := context) (ls := []) registered (by simp) rfl
  simp only [signature, List.foldr_cons, List.foldr_nil, expressionType, intType, stateType,
    eqResult, optionInt, someInt, eval, value, applications, VExpr.instL, VLevel.inst,
    List.map_cons, List.map_nil] at fact
  have a1 := VEnv.HasType.app fact hc
  simp only [Nat.reduceAdd, ← VExpr.lift_instN_lo, VExpr.inst_lift, VExpr.inst,
    VExpr.instVar_lower, VExpr.instVar_succ, VExpr.instVar_zero] at a1
  have a2 := VEnv.HasType.app a1 ha
  simp only [Nat.reduceAdd, ← VExpr.lift_instN_lo, VExpr.inst_lift, VExpr.inst,
    VExpr.instVar_lower, VExpr.instVar_succ, VExpr.instVar_zero] at a2
  have a3 := VEnv.HasType.app a2 hb
  simp only [Nat.reduceAdd, ← VExpr.lift_instN_lo, VExpr.inst_lift, VExpr.inst,
    VExpr.instVar_lower, VExpr.instVar_succ, VExpr.instVar_zero] at a3
  have a4 := VEnv.HasType.app a3 hi
  simp only [Nat.reduceAdd, ← VExpr.lift_instN_lo, VExpr.inst_lift, VExpr.inst,
    VExpr.instVar_lower, VExpr.instVar_succ, VExpr.instVar_zero] at a4
  have a5 := VEnv.HasType.app a4 hx
  simp only [Nat.reduceAdd, ← VExpr.lift_instN_lo, VExpr.inst_lift, VExpr.inst,
    VExpr.instVar_lower, VExpr.instVar_succ, VExpr.instVar_zero] at a5
  have a6 := VEnv.HasType.app a5 hy
  simp only [Nat.reduceAdd, ← VExpr.lift_instN_lo, VExpr.inst_lift, VExpr.inst,
    VExpr.instVar_lower, VExpr.instVar_succ, VExpr.instVar_zero] at a6
  have a7 := VEnv.HasType.app a6 hs
  simp only [Nat.reduceAdd, ← VExpr.lift_instN_lo, VExpr.inst_lift, VExpr.inst,
    VExpr.instVar_lower, VExpr.instVar_succ, VExpr.instVar_zero] at a7
  have a8 := VEnv.HasType.app a7 hv
  simp only [Nat.reduceAdd, ← VExpr.lift_instN_lo, VExpr.inst_lift, VExpr.inst,
    VExpr.instVar_lower, VExpr.instVar_succ, VExpr.instVar_zero] at a8
  have a9 := VEnv.HasType.app a8 ht
  simp only [Nat.reduceAdd, ← VExpr.lift_instN_lo, VExpr.inst_lift, VExpr.inst,
    VExpr.instVar_lower, VExpr.instVar_succ, VExpr.instVar_zero] at a9
  have a10 := VEnv.HasType.app a9 hf
  simp only [Nat.reduceAdd, ← VExpr.lift_instN_lo, VExpr.inst_lift, VExpr.inst,
    VExpr.instVar_lower, VExpr.instVar_succ, VExpr.instVar_zero] at a10
  have a11 := VEnv.HasType.app a10 hp
  simp only [Nat.reduceAdd, ← VExpr.lift_instN_lo, VExpr.inst_lift, VExpr.inst,
    VExpr.instVar_lower, VExpr.instVar_succ, VExpr.instVar_zero] at a11
  have a12 := VEnv.HasType.app a11 hq
  simp only [Nat.reduceAdd, ← VExpr.lift_instN_lo, VExpr.inst_lift, VExpr.inst,
    VExpr.instVar_lower, VExpr.instVar_succ, VExpr.instVar_zero] at a12
  have a13 := VEnv.HasType.app a12 hr
  simpa only [applications, eqResult, optionInt, someInt, intType, eval, nilInts, value, VExpr.inst,
    VExpr.inst_lift, VExpr.instVar_zero] using a13

end IRComparison.LeanIRSelect
