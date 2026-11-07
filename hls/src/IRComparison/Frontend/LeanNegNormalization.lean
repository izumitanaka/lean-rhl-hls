import IRComparison.Frontend.LeanLiteralNormalization

namespace IRComparison.LeanNegNormalization
open Lean4Lean LeanTyped

theorem coreFact (x y : Int) (h : x = y) : Int.neg x = Int.sub (Int.ofNat Nat.zero) y := by
  cases h
  exact (Int.zero_sub x).symm
theorem surfaceFact (x y : Int) (h : x = y) : @Neg.neg Int Int.instNegInt x = Int.sub (Int.ofNat Nat.zero) y :=
  coreFact x y h

inductive Flavor where
  | core | surface

def Flavor.head : Flavor → Lean.Expr
  | .core => .const ``Int.neg []
  | .surface => .app (.app (.const ``Neg.neg [.zero]) (.const ``Int [])) (.const ``Int.instNegInt [])
def Flavor.coreHead : Flavor → VExpr
  | .core => .const ``Int.neg []
  | .surface => .app (.app (.const ``Neg.neg [.zero]) intType) (.const ``Int.instNegInt [])
def Flavor.fact : Flavor → Lean.Name
  | .core => ``coreFact
  | .surface => ``surfaceFact
def target (x : VExpr) : VExpr := .app (.app (.const ``Int.sub []) (integer 0)) x
def Flavor.signature (f : Flavor) : VExpr :=
  .forallE intType (.forallE intType (.forallE (eqInt (.bvar 1) (.bvar 0))
    (eqInt (.app f.coreHead (.bvar 2)) (target (.bvar 1)))))

theorem Flavor.represents (f : Flavor) : Represents f.head f.coreHead := by
  cases f
  · exact .constant rfl
  · exact .app (.app (.constant rfl) (.constant rfl)) (.constant rfl)

variable {env : VEnv} {U : Nat} {context : List VExpr}
theorem apply_neg (f : Flavor)
    (registered : env.constants f.fact = some ⟨0,f.signature⟩)
    (hx : env.HasType U context x intType) (hy : env.HasType U context y intType)
    (hp : env.HasType U context p (eqInt x y)) :
    env.HasType U context (applications (.const f.fact []) [x,y,p])
      (eqInt (.app f.coreHead x) (target y)) := by
  have fact := VEnv.HasType.const (U := U) (Γ := context) (ls := []) registered (by simp) rfl
  cases f <;>
    simp only [Flavor.signature, Flavor.coreHead, Flavor.fact, target, integer, numeral,
      intType, eqInt, applications, VExpr.instL, VLevel.inst, List.map_cons, List.map_nil] at fact ⊢
  all_goals
    have a := VEnv.HasType.app fact hx
    simp only [Nat.reduceAdd, ← VExpr.lift_instN_lo, VExpr.inst_lift, VExpr.inst,
      VExpr.instVar_lower, VExpr.instVar_succ, VExpr.instVar_zero] at a
    have b := VEnv.HasType.app a hy
    simp only [Nat.reduceAdd, ← VExpr.lift_instN_lo, VExpr.inst_lift, VExpr.inst,
      VExpr.instVar_lower, VExpr.instVar_succ, VExpr.instVar_zero] at b
    have c := VEnv.HasType.app b hp
    simpa only [VExpr.inst, VExpr.inst_lift] using c

end IRComparison.LeanNegNormalization
