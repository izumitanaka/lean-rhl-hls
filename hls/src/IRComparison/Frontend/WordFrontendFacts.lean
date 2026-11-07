import IRComparison.Hybrid.HybridWordGlobal

namespace IRComparison.WordFrontendFacts
open HybridWord

theorem literal (v i x y : Word) (s : HybridWord.State) (ls : List Word) :
    HybridWord.Expr.eval i x y s ls (.lit v) = some v := rfl
theorem index (i x y : Word) (s : HybridWord.State) (ls : List Word) :
    HybridWord.Expr.eval i x y s ls .index = some i := rfl
theorem left (i x y : Word) (s : HybridWord.State) (ls : List Word) :
    HybridWord.Expr.eval i x y s ls .left = some x := rfl
theorem right (i x y : Word) (s : HybridWord.State) (ls : List Word) :
    HybridWord.Expr.eval i x y s ls .right = some y := rfl
theorem localZero (i x y : Word) (s : HybridWord.State) (v : Word) (ls : List Word) :
    HybridWord.Expr.eval i x y s (v::ls) (.local Nat.zero) = some v := rfl
theorem localSucc (n : Nat) (i x y : Word) (s : HybridWord.State) (v w : Word) (ls : List Word)
    (h : HybridWord.Expr.eval i x y s ls (.local n) = some w) :
    HybridWord.Expr.eval i x y s (v::ls) (.local (Nat.succ n)) = some w := h
theorem register (r : Nat) (i x y : Word) (s : HybridWord.State) (ls : List Word) :
    HybridWord.Expr.eval i x y s ls (.reg r) = some (s.regs r) := rfl

theorem add (a b : HybridWord.Expr) (i x y : Word) (s : HybridWord.State) (ls : List Word)
    (u v : Word) (ha : a.eval i x y s ls = some u) (hb : b.eval i x y s ls = some v) :
    HybridWord.Expr.eval i x y s ls (.add a b) = some (u+v) := by simp [HybridWord.Expr.eval,ha,hb]
theorem sub (a b : HybridWord.Expr) (i x y : Word) (s : HybridWord.State) (ls : List Word)
    (u v : Word) (ha : a.eval i x y s ls = some u) (hb : b.eval i x y s ls = some v) :
    HybridWord.Expr.eval i x y s ls (.sub a b) = some (u-v) := by simp [HybridWord.Expr.eval,ha,hb]
theorem mul (a b : HybridWord.Expr) (i x y : Word) (s : HybridWord.State) (ls : List Word)
    (u v : Word) (ha : a.eval i x y s ls = some u) (hb : b.eval i x y s ls = some v) :
    HybridWord.Expr.eval i x y s ls (.mul a b) = some (u*v) := by simp [HybridWord.Expr.eval,ha,hb]
theorem div (a b : HybridWord.Expr) (i x y : Word) (s : HybridWord.State) (ls : List Word)
    (u v : Word) (ha : a.eval i x y s ls = some u) (hb : b.eval i x y s ls = some v) :
    HybridWord.Expr.eval i x y s ls (.div a b) = some (u/v) := by simp [HybridWord.Expr.eval,ha,hb]
theorem neg (a : HybridWord.Expr) (i x y : Word) (s : HybridWord.State) (ls : List Word)
    (v : Word) (ha : a.eval i x y s ls = some v) :
    HybridWord.Expr.eval i x y s ls (.neg a) = some (-v) := by
  simp [HybridWord.Expr.neg,HybridWord.Expr.eval,ha,BitVec.zero_sub]

theorem read (a : Nat) (j : HybridWord.Expr) (i x y : Word) (s : HybridWord.State) (ls : List Word)
    (k : Word) (h : j.eval i x y s ls = some k) :
    HybridWord.Expr.eval i x y s ls (.read a j) = (s.arrays a)[k.toNat]? := by
  simp [HybridWord.Expr.eval,h]
theorem readNat (a n : Nat) (i x y : Word) (s : HybridWord.State) (ls : List Word) :
    HybridWord.Expr.eval i x y s ls (.readNat a n) = (s.arrays a)[n]? := rfl

theorem skip (i x y : Word) (s : HybridWord.State) (ls : List Word) :
    HybridWord.Cmd.eval i x y .skip s ls = some s := rfl
theorem assign (r : Nat) (e : HybridWord.Expr) (i x y : Word) (s : HybridWord.State) (ls : List Word)
    (v : Word) (h : e.eval i x y s ls = some v) :
    HybridWord.Cmd.eval i x y (.assign r e) s ls = some (s.set r v) := by simp [HybridWord.Cmd.eval,h]
theorem store (a : Nat) (j e : HybridWord.Expr) (i x y : Word) (s : HybridWord.State) (ls : List Word)
    (k v : Word) (hj : j.eval i x y s ls = some k) (hv : e.eval i x y s ls = some v) :
    HybridWord.Cmd.eval i x y (.store a j e) s ls = s.write a k v := by simp [HybridWord.Cmd.eval,hj,hv]
theorem bindValue (e : HybridWord.Expr) (b : HybridWord.Cmd) (i x y : Word) (s : HybridWord.State)
    (ls : List Word) (value : Option Word) (next : Word → Option HybridWord.State)
    (he : e.eval i x y s ls = value) (hb : ∀ v, b.eval i x y s (v::ls) = next v) :
    HybridWord.Cmd.eval i x y (.letValue e b) s ls = (do let v ← value; next v) := by
  simp only [HybridWord.Cmd.eval,he,hb]
theorem sequence (a b : HybridWord.Cmd) (i x y : Word) (s : HybridWord.State) (ls : List Word)
    (first : Option HybridWord.State) (next : HybridWord.State → Option HybridWord.State)
    (ha : a.eval i x y s ls = first) (hb : ∀ t, b.eval i x y t ls = next t) :
    HybridWord.Cmd.eval i x y (.seq a b) s ls = (do let t ← first; next t) := by
  simp only [HybridWord.Cmd.eval,ha,hb]
theorem skipPure (i x y : Word) (s : HybridWord.State) (ls : List Word) :
    HybridWord.Cmd.eval i x y .skip s ls = (pure s : Option HybridWord.State) := rfl
theorem assignPure (r : Nat) (e : HybridWord.Expr) (i x y : Word) (s : HybridWord.State) (ls : List Word)
    (v : Word) (h : e.eval i x y s ls = some v) :
    HybridWord.Cmd.eval i x y (.assign r e) s ls = (pure (s.set r v) : Option HybridWord.State) := by
  simp [HybridWord.Cmd.eval,h]
theorem branch (e : HybridWord.Expr) (a b : HybridWord.Cmd) (i x y : Word)
    (s : HybridWord.State) (ls : List Word) (v : Word) (d : Decidable (v != 0))
    (yes no : Option HybridWord.State) (he : e.eval i x y s ls = some v)
    (ha : a.eval i x y s ls = yes) (hb : b.eval i x y s ls = no) :
    HybridWord.Cmd.eval i x y (.branch e a b) s ls = @ite (Option HybridWord.State) (v != 0) d yes no := by
  simp [HybridWord.Cmd.eval,he,ha,hb]
theorem select (e a b : HybridWord.Expr) (i x y : Word)
    (s : HybridWord.State) (ls : List Word) (v : Word) (d : Decidable (v != 0))
    (yes no : Word) (he : e.eval i x y s ls = some v)
    (ha : a.eval i x y s ls = some yes) (hb : b.eval i x y s ls = some no) :
    HybridWord.Expr.eval i x y s ls (.select e a b) = some (@ite Word (v != 0) d yes no) := by
  simp [HybridWord.Expr.eval,he,ha,hb]
  split <;> rfl
theorem forRange (e : HybridWord.Expr) (b : HybridWord.Cmd) (i x y : Word)
    (s : HybridWord.State) (ls : List Word) (n : Word)
    (f : HybridWord.State → Nat → Option HybridWord.State)
    (he : e.eval i x y s ls = some n)
    (hb : ∀ t k, b.eval i x y t (BitVec.ofNat 32 k::ls) = f t k) :
    HybridWord.Cmd.eval i x y (.forRange e b) s ls = (List.range n.toNat).foldlM f s := by
  simp [HybridWord.Cmd.eval,he,hb]
end IRComparison.WordFrontendFacts
