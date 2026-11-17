import IRComparison.Core.SnapshotIR
import IRComparison.Core.LoopFacts

namespace IRComparison.VersionFacts

theorem lookupZero (s : State) (ss : List State) : (s::ss)[Nat.zero]? = some s := rfl
theorem lookupSucc (n : Nat) (s t : State) (ss : List State) (h : ss[n]? = some t) :
    (s::ss)[Nat.succ n]? = some t := h

theorem yieldSome (v : Nat) (i x y : Int) (ss : List State) (ls : List Int)
    (s : State) (h : ss[v]? = some s) : (Functional.Term.yield v).eval i x y ss ls = some s := h

theorem yieldPure (v : Nat) (i x y : Int) (ss : List State) (ls : List Int)
    (s : State) (h : ss[v]? = some s) :
    (Functional.Term.yield v).eval i x y ss ls = (pure s : Option State) := h

theorem store (v a : Nat) (j e : Expr) (i x y : Int) (ss : List State) (ls : List Int)
    (s : State) (address value : Int) (hs : ss[v]? = some s)
    (hj : j.eval i x y s ls = some address) (he : e.eval i x y s ls = some value) :
    (Functional.Term.letWrite v a j e (.yield Nat.zero)).eval i x y ss ls = s.write a address value := by
  simp [Functional.Term.eval,hs,hj,he]

theorem storeLiteral (v a : Nat) (j e : Expr) (i x y : Int) (ss : List State) (ls : List Int)
    (s : State) (address value : Int) (hs : ss[v]? = some s)
    (hj : j.eval i x y s ls = some address) (he : e.eval i x y s ls = some value) :
    (Functional.Term.letWrite v a j e (.yield Nat.zero)).eval i x y ss ls =
      s.write (@OfNat.ofNat Nat a (instOfNatNat a)) address value := store v a j e i x y ss ls s address value hs hj he

theorem bind (first next : Functional.Term) (i x y : Int) (ss : List State) (ls : List Int)
    (a : Option State) (f : State → Option State)
    (ha : first.eval i x y ss ls = a)
    (hn : ∀ s, next.eval i x y (s::ss) ls = f s) :
    (Functional.Term.bindResult first next).eval i x y ss ls = a >>= f := by
  simp [Functional.Term.eval,ha,hn]

theorem capture (v : Nat) (e : Expr) (next : Functional.Term) (i x y : Int)
    (ss : List State) (ls : List Int) (s : State) (a : Option Int) (f : Int → Option State)
    (hs : ss[v]? = some s) (ha : e.eval i x y s ls = a)
    (hn : ∀ z, next.eval i x y ss (z::ls) = f z) :
    (Functional.Term.letValue v e next).eval i x y ss ls = a >>= f := by
  simp [Functional.Term.eval,hs,ha,hn]

theorem branch (v : Nat) (e : Expr) (yes no : Functional.Term) (i x y : Int)
    (ss : List State) (ls : List Int) (s : State) (z : Int)
    (d : Decidable (z != 0)) (a b : Option State) (hs : ss[v]? = some s)
    (he : e.eval i x y s ls = some z)
    (ha : yes.eval i x y ss ls = a) (hb : no.eval i x y ss ls = b) :
    (Functional.Term.branch v e yes no).eval i x y ss ls = @ite (Option State) (z != 0) d a b := by
  simp [Functional.Term.eval,hs,he,ha,hb]

theorem capturedLoop (v : Nat) (e : Expr) (body : Functional.Term)
    (i x y : Int) (ss : List State) (ls : List Int) (s : State) (n : Int)
    (original : Nat → State → Option (ForInStep State))
    (hs : ss[v]? = some s) (hc : e.eval i x y s ls = some n)
    (hb : ∀ (k : Nat) t, LoopFacts.lift (body.eval i x y (t::ss) ((k : Int)::ls)) = original k t) :
    (Functional.Term.forRangeCaptured v e body (.yield Nat.zero)).eval i x y ss ls =
      forIn (List.range n.toNat) s original := by
  rw [LoopFacts.forIn_lift _ _ _ _ hb]
  simp [Functional.Term.eval,hs,hc]

end IRComparison.VersionFacts
