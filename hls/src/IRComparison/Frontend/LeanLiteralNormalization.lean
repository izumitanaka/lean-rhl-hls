import IRComparison.Frontend.LeanEquality

namespace IRComparison.LeanLiteralNormalization
open Lean4Lean LeanTyped

def source (n : Nat) : Lean.Expr :=
  .app (.app (.app (.const ``OfNat.ofNat [.zero]) (.const ``Int [])) (.lit (.natVal n)))
    (.app (.const ``instOfNat []) (.lit (.natVal n)))

def core (n : VExpr) : VExpr :=
  .app (.app (.app (.const ``OfNat.ofNat [.zero]) intType) n) (.app (.const ``instOfNat []) n)

def target (n : VExpr) : VExpr := .app (.const ``Int.ofNat []) n
def natType : VExpr := .const ``Nat []
def signature : VExpr := .forallE natType (eqInt (core (.bvar 0)) (target (.bvar 0)))

theorem elaboratedFact (n : Nat) : Int.ofNat (@OfNat.ofNat Nat n (@instOfNatNat n)) = Int.ofNat n := rfl

def elaboratedSource (n : Nat) : Lean.Expr :=
  .app (.const ``Int.ofNat [])
    (.app (.app (.app (.const ``OfNat.ofNat [.zero]) (.const ``Nat [])) (.lit (.natVal n)))
      (.app (.const ``instOfNatNat []) (.lit (.natVal n))))
def elaboratedCore (n : VExpr) : VExpr :=
  .app (.const ``Int.ofNat [])
    (.app (.app (.app (.const ``OfNat.ofNat [.zero]) natType) n) (.app (.const ``instOfNatNat []) n))
def elaboratedSignature : VExpr := .forallE natType (eqInt (elaboratedCore (.bvar 0)) (target (.bvar 0)))

theorem elaborated_represents (n : Nat) : Represents (elaboratedSource n) (elaboratedCore (numeral n)) :=
  .app (.constant rfl)
    (.app (.app (.app (.constant rfl) (.constant rfl)) .natural) (.app (.constant rfl) .natural))

theorem represents (n : Nat) : Represents (source n) (core (numeral n)) :=
  .app (.app (.app (.constant rfl) (.constant rfl)) .natural) (.app (.constant rfl) .natural)

variable {env : VEnv} {U : Nat} {context : List VExpr}

theorem apply_literal (registered : env.constants ``Standard.literal = some ⟨0, signature⟩)
    (typed : env.HasType U context n natType) :
    env.HasType U context (.app (.const ``Standard.literal []) n)
      (eqInt (core n) (target n)) := by
  have fact := VEnv.HasType.const (U := U) (Γ := context) (ls := []) registered (by simp) rfl
  simp only [signature, natType, eqInt, core, target, intType, VExpr.instL,
    List.map_cons, List.map_nil, VLevel.inst] at fact
  simpa only [eqInt, core, target, intType, VExpr.inst, VExpr.instVar_zero] using VEnv.HasType.app fact typed

theorem apply_elaborated (registered : env.constants ``elaboratedFact = some ⟨0, elaboratedSignature⟩)
    (typed : env.HasType U context n natType) :
    env.HasType U context (.app (.const ``elaboratedFact []) n)
      (eqInt (elaboratedCore n) (target n)) := by
  have fact := VEnv.HasType.const (U := U) (Γ := context) (ls := []) registered (by simp) rfl
  simp only [elaboratedSignature, natType, eqInt, elaboratedCore, target, intType, VExpr.instL,
    List.map_cons, List.map_nil, VLevel.inst] at fact
  simpa only [eqInt, elaboratedCore, natType, target, intType, VExpr.inst, VExpr.instVar_zero] using VEnv.HasType.app fact typed

end IRComparison.LeanLiteralNormalization
