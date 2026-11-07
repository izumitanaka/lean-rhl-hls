import IRComparison.Frontend.LeanLiteralNormalization
import IRComparison.Frontend.LeanSelectValue

namespace IRComparison.LeanSelectBridge
open Lean4Lean LeanTyped

theorem fact (c c' yes yes' no no' : Int) (decision : Decidable ((c != 0) = true))
    (hc : c = c') (hy : yes = yes') (hn : no = no') :
    @ite Int ((c != 0) = true) decision yes no = LeanIRQuotation.selectValue c' yes' no' := by
  subst c'
  subst yes'
  subst no'
  by_cases h : c = 0 <;> simp [LeanIRQuotation.selectValue, h]

def condition (c : VExpr) : VExpr :=
  .app (.app (.app (.const ``Eq [.succ .zero]) (.const ``Bool []))
    (.app (.app (.app (.app (.const ``bne [.zero]) intType)
      (.app (.app (.const ``instBEqOfDecidableEq [.zero]) intType)
        (.const ``Int.instDecidableEq []))) c)
      (LeanLiteralNormalization.core (numeral 0)))) (.const ``Bool.true [])

def decisionType (c : VExpr) : VExpr := .app (.const ``Decidable []) (condition c)
def source (c d a b : VExpr) : VExpr :=
  applications (.const ``ite [.succ .zero]) [intType,condition c,d,a,b]
def target (c a b : VExpr) : VExpr :=
  applications (.const ``LeanIRQuotation.selectValue []) [c,a,b]

def signature : VExpr :=
  [intType,intType,intType,intType,intType,intType,decisionType (.bvar 5),
    eqInt (.bvar 6) (.bvar 5),eqInt (.bvar 5) (.bvar 4),eqInt (.bvar 4) (.bvar 3)].foldr VExpr.forallE
    (eqInt (source (.bvar 9) (.bvar 3) (.bvar 7) (.bvar 5))
      (target (.bvar 8) (.bvar 6) (.bvar 4)))

variable {env : VEnv} {U : Nat} {context : List VExpr}

theorem apply_fact (registered : env.constants ``fact = some ⟨0,signature⟩)
    (hc : env.HasType U context c intType) (hc' : env.HasType U context c' intType)
    (hy : env.HasType U context y intType) (hy' : env.HasType U context y' intType)
    (hn : env.HasType U context n intType) (hn' : env.HasType U context n' intType)
    (hd : env.HasType U context d (decisionType c))
    (hp : env.HasType U context p (eqInt c c'))
    (hq : env.HasType U context q (eqInt y y'))
    (hr : env.HasType U context r (eqInt n n')) :
    env.HasType U context (applications (.const ``fact []) [c,c',y,y',n,n',d,p,q,r])
      (eqInt (source c d y n) (target c' y' n')) := by
  have theoremTyped := VEnv.HasType.const (U := U) (Γ := context) (ls := []) registered (by simp) rfl
  simp only [signature, List.foldr_cons, List.foldr_nil, condition, decisionType, source, target,
    intType, eqInt, LeanLiteralNormalization.core, numeral, applications, VExpr.instL,
    VLevel.inst, List.map_cons, List.map_nil] at theoremTyped
  have a1 := VEnv.HasType.app theoremTyped hc
  simp only [Nat.reduceAdd, ← VExpr.lift_instN_lo, VExpr.inst_lift, VExpr.inst,
    VExpr.instVar_lower, VExpr.instVar_succ, VExpr.instVar_zero] at a1
  have a2 := VEnv.HasType.app a1 hc'
  simp only [Nat.reduceAdd, ← VExpr.lift_instN_lo, VExpr.inst_lift, VExpr.inst,
    VExpr.instVar_lower, VExpr.instVar_succ, VExpr.instVar_zero] at a2
  have a3 := VEnv.HasType.app a2 hy
  simp only [Nat.reduceAdd, ← VExpr.lift_instN_lo, VExpr.inst_lift, VExpr.inst,
    VExpr.instVar_lower, VExpr.instVar_succ, VExpr.instVar_zero] at a3
  have a4 := VEnv.HasType.app a3 hy'
  simp only [Nat.reduceAdd, ← VExpr.lift_instN_lo, VExpr.inst_lift, VExpr.inst,
    VExpr.instVar_lower, VExpr.instVar_succ, VExpr.instVar_zero] at a4
  have a5 := VEnv.HasType.app a4 hn
  simp only [Nat.reduceAdd, ← VExpr.lift_instN_lo, VExpr.inst_lift, VExpr.inst,
    VExpr.instVar_lower, VExpr.instVar_succ, VExpr.instVar_zero] at a5
  have a6 := VEnv.HasType.app a5 hn'
  simp only [Nat.reduceAdd, ← VExpr.lift_instN_lo, VExpr.inst_lift, VExpr.inst,
    VExpr.instVar_lower, VExpr.instVar_succ, VExpr.instVar_zero] at a6
  have a7 := VEnv.HasType.app a6 hd
  simp only [Nat.reduceAdd, ← VExpr.lift_instN_lo, VExpr.inst_lift, VExpr.inst,
    VExpr.instVar_lower, VExpr.instVar_succ, VExpr.instVar_zero] at a7
  have a8 := VEnv.HasType.app a7 hp
  simp only [Nat.reduceAdd, ← VExpr.lift_instN_lo, VExpr.inst_lift, VExpr.inst,
    VExpr.instVar_lower, VExpr.instVar_succ, VExpr.instVar_zero] at a8
  have a9 := VEnv.HasType.app a8 hq
  simp only [Nat.reduceAdd, ← VExpr.lift_instN_lo, VExpr.inst_lift, VExpr.inst,
    VExpr.instVar_lower, VExpr.instVar_succ, VExpr.instVar_zero] at a9
  have a10 := VEnv.HasType.app a9 hr
  simpa only [applications, eqInt, condition, decisionType, source, target, intType,
    LeanLiteralNormalization.core, numeral, VExpr.inst, VExpr.inst_lift, VExpr.instVar_zero] using a10

theorem represents (hc : Represents c c') (hd : Represents d d')
    (ha : Represents a a') (hb : Represents b b') :
    Represents (NativeRHL.ExprAnalysis.conditional c d a b) (source c' d' a' b') := by
  unfold NativeRHL.ExprAnalysis.conditional NativeRHL.ExprAnalysis.nonzeroCond source condition
    applications intType LeanLiteralNormalization.core numeral
  repeat first | assumption | exact Represents.constant rfl | exact Represents.natural | apply Represents.app

end IRComparison.LeanSelectBridge
