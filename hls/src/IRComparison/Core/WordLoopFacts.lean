import IRComparison.Frontend.WordFrontendFacts
import IRComparison.Frontend.NativeLoop

namespace IRComparison.WordLoopFacts
open HybridWord
def lift (r : Option HybridWord.State) := r.map ForInStep.yield
theorem someYield (s : HybridWord.State) :
    lift (some s) = (pure (ForInStep.yield s) : Option (ForInStep HybridWord.State)) := rfl
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
theorem forIn_lift (n : Nat) (s : HybridWord.State) (plain : Nat → HybridWord.State → Option HybridWord.State)
    (original : Nat → HybridWord.State → Option (ForInStep HybridWord.State))
    (h : ∀ k t, lift (plain k t) = original k t) :
    forIn (List.range n) s original = (List.range n).foldlM (fun t k => plain k t) s := by
  have eq : original = fun k t => do return ForInStep.yield (← plain k t) := by
    funext k t
    rw [← h]
    cases plain k t <;> rfl
  rw [eq]
  exact NativeLoop.forIn_option _ _ _
theorem forIn (e : HybridWord.Expr) (b : HybridWord.Cmd) (i x y : Word)
    (s : HybridWord.State) (ls : List Word) (n : Word)
    (f : Nat → HybridWord.State → Option (ForInStep HybridWord.State))
    (he : e.eval i x y s ls = some n)
    (hb : ∀ k t, lift (b.eval i x y t (BitVec.ofNat 32 k::ls)) = f k t) :
    HybridWord.Cmd.eval i x y (.forRange e b) s ls = forIn (List.range n.toNat) s f := by
  rw [forIn_lift _ _ _ _ hb]
  simp [HybridWord.Cmd.eval,he]
end IRComparison.WordLoopFacts
