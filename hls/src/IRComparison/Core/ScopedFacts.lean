import IRComparison.Frontend.LeanSelectValue
import IRComparison.Core.Common

namespace IRComparison.ScopedFacts

theorem literal (n i x y : Int) (s : State) (locals : List Int) :
    (Expr.lit n).eval i x y s locals = some n := rfl
theorem index (i x y : Int) (s : State) (locals : List Int) : Expr.index.eval i x y s locals = some i := rfl
theorem left (i x y : Int) (s : State) (locals : List Int) : Expr.left.eval i x y s locals = some x := rfl
theorem right (i x y : Int) (s : State) (locals : List Int) : Expr.right.eval i x y s locals = some y := rfl

theorem localZero (v : Int) (tail : List Int) (i x y : Int) (s : State) :
    (Expr.local Nat.zero).eval i x y s (v :: tail) = some v := rfl
theorem localSucc (n : Nat) (head : Int) (tail : List Int) (i x y : Int) (s : State) (v : Int)
    (h : (Expr.local n).eval i x y s tail = some v) :
    (Expr.local (Nat.succ n)).eval i x y s (head :: tail) = some v := h

theorem natIndex (e : Expr) (i x y : Int) (s : State) (locals : List Int) (v : Int)
    (h : e.eval i x y s locals = some v) :
    (Expr.natIndex e).eval i x y s locals = some (Int.ofNat v.toNat) := by simp [Expr.eval,h]

theorem add (a b : Expr) (i x y : Int) (s : State) (locals : List Int) (v w : Int)
    (ha : a.eval i x y s locals = some v) (hb : b.eval i x y s locals = some w) :
    (Expr.add a b).eval i x y s locals = some (Int.add v w) := by simp [Expr.eval,ha,hb] <;> rfl
theorem sub (a b : Expr) (i x y : Int) (s : State) (locals : List Int) (v w : Int)
    (ha : a.eval i x y s locals = some v) (hb : b.eval i x y s locals = some w) :
    (Expr.sub a b).eval i x y s locals = some (Int.sub v w) := by simp [Expr.eval,ha,hb] <;> rfl
theorem mul (a b : Expr) (i x y : Int) (s : State) (locals : List Int) (v w : Int)
    (ha : a.eval i x y s locals = some v) (hb : b.eval i x y s locals = some w) :
    (Expr.mul a b).eval i x y s locals = some (Int.mul v w) := by simp [Expr.eval,ha,hb] <;> rfl
theorem div (a b : Expr) (i x y : Int) (s : State) (locals : List Int) (v w : Int)
    (ha : a.eval i x y s locals = some v) (hb : b.eval i x y s locals = some w) :
    (Expr.div a b).eval i x y s locals = some (Int.ediv v w) := by simp [Expr.eval,ha,hb] <;> rfl
theorem select (c a b : Expr) (i x y : Int) (s : State) (locals : List Int) (v yes no : Int)
    (hc : c.eval i x y s locals = some v) (ha : a.eval i x y s locals = some yes)
    (hb : b.eval i x y s locals = some no) :
    (Expr.select c a b).eval i x y s locals = some (LeanIRQuotation.selectValue v yes no) := by
  by_cases h : v = 0 <;> simp [Expr.eval,LeanIRQuotation.selectValue,hc,ha,hb,h]

end IRComparison.ScopedFacts
