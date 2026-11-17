import IRComparison.Frontend.WordFrontendFacts
import IRComparison.Frontend.NativeLoop

namespace IRComparison.WordLoopFacts
open HybridWord
def lift (r : Option HybridWord.State) := r.map ForInStep.yield
theorem someYield (s : HybridWord.State) :
    lift (some s) = (pure (ForInStep.yield s) : Option (ForInStep HybridWord.State)) := rfl
theorem letBinding (α : Type) (value : α) (plain : α → Option HybridWord.State)
    (original : α → Option (ForInStep HybridWord.State))
    (h : ∀ v, lift (plain v) = original v) :
    lift (plain value) = original value := h value
theorem bindState (a : Option HybridWord.State) (plain : HybridWord.State → Option HybridWord.State)
    (original : HybridWord.State → Option (ForInStep HybridWord.State)) (h : ∀ s, lift (plain s) = original s) :
    lift (a >>= plain) = a >>= original := by cases a <;> simp [lift,← h]
theorem bindWord (a : Option Word) (plain : Word → Option HybridWord.State)
    (original : Word → Option (ForInStep HybridWord.State)) (h : ∀ s, lift (plain s) = original s) :
    lift (a >>= plain) = a >>= original := by cases a <;> simp [lift,← h]
theorem bindUnit (plain : Option HybridWord.State) (original : PUnit.{1} → Option (ForInStep HybridWord.State))
    (h : lift plain = original PUnit.unit) :
    lift plain = (pure PUnit.unit : Option PUnit.{1}) >>= original := h
theorem branch (p : Prop) (d : Decidable p) (a b : Option HybridWord.State)
    (c e : Option (ForInStep HybridWord.State)) (ha : lift a = c) (hb : lift b = e) :
    lift (@ite (Option HybridWord.State) p d a b) = @ite (Option (ForInStep HybridWord.State)) p d c e := by
  by_cases h : p <;> simp [h,ha,hb]
theorem compose (result plain : Option HybridWord.State) (original : Option (ForInStep HybridWord.State))
    (h : result = plain) (hn : lift plain = original) : lift result = original := h ▸ hn

/-- Compile a `for` continuation directly. These rules avoid constructing an
ordinary Option-State body and then traversing that body a second time. -/
theorem letValue (e : HybridWord.Expr) (b : HybridWord.Cmd) (i x y : Word)
    (s : HybridWord.State) (ls : List Word) (value : Word)
    (next : Word → Option (ForInStep HybridWord.State))
    (he : e.eval i x y s ls = some value)
    (hb : ∀ v, lift (b.eval i x y s (v::ls)) = next v) :
    lift (HybridWord.Cmd.eval i x y (.letValue e b) s ls) = next value := by
  simp [HybridWord.Cmd.eval, he, hb]

theorem letStateAlias (b : HybridWord.Cmd) (i x y : Word)
    (s : HybridWord.State) (ls : List Word)
    (next : HybridWord.State → Option (ForInStep HybridWord.State))
    (hb : ∀ t, lift (b.eval i x y t ls) = next t) :
    lift (HybridWord.Cmd.eval i x y b s ls) = next s := hb s

theorem letState (a b : HybridWord.Cmd) (i x y : Word)
    (s : HybridWord.State) (ls : List Word) (value : HybridWord.State)
    (next : HybridWord.State → Option (ForInStep HybridWord.State))
    (ha : a.eval i x y s ls = some value)
    (hb : ∀ t, lift (b.eval i x y t ls) = next t) :
    lift (HybridWord.Cmd.eval i x y (.seq a b) s ls) = next value := by
  simp [HybridWord.Cmd.eval, ha, hb]

theorem bindValue (e : HybridWord.Expr) (b : HybridWord.Cmd) (i x y : Word)
    (s : HybridWord.State) (ls : List Word) (value : Option Word)
    (next : Word → Option (ForInStep HybridWord.State))
    (he : e.eval i x y s ls = value)
    (hb : ∀ v, lift (b.eval i x y s (v::ls)) = next v) :
    lift (HybridWord.Cmd.eval i x y (.letValue e b) s ls) = Bind.bind value next := by
  simp only [HybridWord.Cmd.eval, he]
  cases value <;> simp_all [lift]

theorem sequence (a b : HybridWord.Cmd) (i x y : Word)
    (s : HybridWord.State) (ls : List Word) (first : Option HybridWord.State)
    (next : HybridWord.State → Option (ForInStep HybridWord.State))
    (ha : a.eval i x y s ls = first)
    (hb : ∀ t, lift (b.eval i x y t ls) = next t) :
    lift (HybridWord.Cmd.eval i x y (.seq a b) s ls) = Bind.bind first next := by
  simp only [HybridWord.Cmd.eval, ha]
  cases first <;> simp_all [lift]

theorem branchCmd (e : HybridWord.Expr) (a b : HybridWord.Cmd) (i x y : Word)
    (s : HybridWord.State) (ls : List Word) (v : Word) (d : Decidable (v != 0))
    (yes no : Option (ForInStep HybridWord.State))
    (he : e.eval i x y s ls = some v)
    (ha : lift (a.eval i x y s ls) = yes) (hb : lift (b.eval i x y s ls) = no) :
    lift (HybridWord.Cmd.eval i x y (.branch e a b) s ls) =
      @ite (Option (ForInStep HybridWord.State)) (v != 0) d yes no := by
  simp only [HybridWord.Cmd.eval, he, Option.bind_some]
  split <;> simp_all

theorem unitSequence (b : HybridWord.Cmd) (i x y : Word)
    (s : HybridWord.State) (ls : List Word)
    (next : PUnit.{1} → Option (ForInStep HybridWord.State))
    (hb : ∀ u, lift (b.eval i x y s ls) = next u) :
    lift (b.eval i x y s ls) = (pure PUnit.unit : Option PUnit.{1}) >>= next := hb PUnit.unit
theorem forIn_lift (n : Nat) (s : HybridWord.State) (plain : Nat → HybridWord.State → Option HybridWord.State)
    (original : Nat → HybridWord.State → Option (ForInStep HybridWord.State))
    (h : ∀ k t, lift (plain k t) = original k t) :
    forIn (List.range n) s original = (List.range n).foldlM (fun t k => plain k t) s :=
  NativeLoop.forIn_lift (List.range n) s plain original h

theorem forIn (e : HybridWord.Expr) (b : HybridWord.Cmd) (i x y : Word)
    (s : HybridWord.State) (ls : List Word) (n : Word)
    (f : Nat → HybridWord.State → Option (ForInStep HybridWord.State))
    (he : e.eval i x y s ls = some n)
    (hb : ∀ k t, lift (b.eval i x y t (BitVec.ofNat 32 k::ls)) = f k t) :
    HybridWord.Cmd.eval i x y (.forRange e b) s ls = forIn (List.range n.toNat) s f := by
  rw [forIn_lift _ _ _ _ hb]
  simp [HybridWord.Cmd.eval,he]

/-- Signed, exclusive bounds in an ordinary Lean for-loop. This theorem is
independent of the iteration count, body shape, and nesting depth. -/
theorem forStatic (start stop stride : Int) (b : HybridWord.Cmd) (i x y : Word)
    (s : HybridWord.State) (ls : List Word)
    (f : Word → HybridWord.State → Option (ForInStep HybridWord.State))
    (hb : ∀ k t, lift (b.eval i x y t (k::ls)) = f k t) :
    HybridWord.Cmd.eval i x y (.forStatic start stop stride b) s ls =
      ForIn.forIn (HybridWord.range start stop stride) s f := by
  rw [NativeLoop.forIn_lift _ _ _ _ hb]
  rfl
end IRComparison.WordLoopFacts
