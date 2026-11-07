import IRComparison.Core.Common

namespace IRComparison.ReadFacts

theorem literal (a n : Nat) (i x y : Int) (s : State) (locals : List Int) :
    (Expr.read a (.lit (Int.ofNat n))).eval i x y s locals = (s.arrays a)[n]? := by
  rfl

theorem literalN (a n : Nat) (i x y : Int) (s : State) (locals : List Int) :
    (Expr.read a (.lit (Int.ofNat n))).eval i x y s locals = (s.arrays a)[(@OfNat.ofNat Nat n (instOfNatNat n))]? := by
  rfl

theorem literalA (a n : Nat) (i x y : Int) (s : State) (locals : List Int) :
    (Expr.read a (.lit (Int.ofNat n))).eval i x y s locals = (s.arrays (@OfNat.ofNat Nat a (instOfNatNat a)))[n]? := by
  rfl

theorem literalAN (a n : Nat) (i x y : Int) (s : State) (locals : List Int) :
    (Expr.read a (.lit (Int.ofNat n))).eval i x y s locals = (s.arrays (@OfNat.ofNat Nat a (instOfNatNat a)))[(@OfNat.ofNat Nat n (instOfNatNat n))]? := by
  rfl

theorem dynamic (a : Nat) (address : Expr) (i x y : Int) (s : State) (locals : List Int)
    (j : Int) (h : address.eval i x y s locals = some j) :
    (Expr.read a (.natIndex address)).eval i x y s locals = (s.arrays a)[j.toNat]? := by
  simp only [Expr.eval, h]
  rfl

theorem dynamicA (a : Nat) (address : Expr) (i x y : Int) (s : State) (locals : List Int)
    (j : Int) (h : address.eval i x y s locals = some j) :
    (Expr.read a (.natIndex address)).eval i x y s locals = (s.arrays (@OfNat.ofNat Nat a (instOfNatNat a)))[j.toNat]? := by
  simp only [Expr.eval, h]
  rfl

theorem natural (a : Nat) (address : Expr) (i x y : Int) (s : State) (locals : List Int)
    (j : Nat) (h : address.eval i x y s locals = some (j : Int)) :
    (Expr.read a address).eval i x y s locals = (s.arrays a)[j]? := by
  have nonneg : ¬ (j : Int) < 0 := by omega
  simp [Expr.eval,h,nonneg] 

theorem naturalA (a : Nat) (address : Expr) (i x y : Int) (s : State) (locals : List Int)
    (j : Nat) (h : address.eval i x y s locals = some (j : Int)) :
    (Expr.read a address).eval i x y s locals = (s.arrays (@OfNat.ofNat Nat a (instOfNatNat a)))[j]? := by
  exact natural a address i x y s locals j h

end IRComparison.ReadFacts
