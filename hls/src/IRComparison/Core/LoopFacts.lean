import IRComparison.Frontend.NativeLoop

namespace IRComparison.LoopFacts

def lift (r : Option State) : Option (ForInStep State) := r.map ForInStep.yield

theorem someYield (s : State) : lift (some s) = (pure (ForInStep.yield s) : Option (ForInStep State)) := rfl

theorem bindState (a : Option State) (plain : State → Option State)
    (original : State → Option (ForInStep State)) (h : ∀ s, lift (plain s) = original s) :
    lift (a >>= plain) = a >>= original := by cases a <;> simp [lift,h,← h]

theorem bindInt (a : Option Int) (plain : Int → Option State)
    (original : Int → Option (ForInStep State)) (h : ∀ s, lift (plain s) = original s) :
    lift (a >>= plain) = a >>= original := by cases a <;> simp [lift,h,← h]

theorem bindUnit (plain : Option State) (original : PUnit.{1} → Option (ForInStep State))
    (h : lift plain = original PUnit.unit) :
    lift plain = (pure PUnit.unit : Option PUnit.{1}) >>= original := h

theorem branch (p : Prop) (decision : Decidable p) (a b : Option State)
    (c d : Option (ForInStep State)) (ha : lift a = c) (hb : lift b = d) :
    lift (@ite (Option State) p decision a b) = @ite (Option (ForInStep State)) p decision c d := by
  by_cases h : p <;> simp [h,ha,hb]

theorem compose (result plain : Option State) (original : Option (ForInStep State))
    (h : result = plain) (hn : lift plain = original) : lift result = original := h ▸ hn

theorem forIn_lift (n : Nat) (s : State) (plain : Nat → State → Option State)
    (original : Nat → State → Option (ForInStep State))
    (h : ∀ k t, lift (plain k t) = original k t) :
    forIn (List.range n) s original = (List.range n).foldlM (fun t k => plain k t) s := by
  have eq : original = fun k t => do return ForInStep.yield (← plain k t) := by
    funext k t
    rw [← h]
    cases plain k t <;> rfl
  rw [eq]
  exact NativeLoop.forIn_option _ _ _

theorem imperative (e : Expr) (body : Imperative.Cmd) (i x y : Int) (s : State) (ls : List Int)
    (n : Int) (original : Nat → State → Option (ForInStep State))
    (hc : e.eval i x y s ls = some n)
    (hb : ∀ (k : Nat) t, lift (body.eval i x y t ((k : Int) :: ls)) = original k t) :
    (Imperative.Cmd.forRange e body).eval i x y s ls = forIn (List.range n.toNat) s original := by
  rw [forIn_lift _ _ _ _ hb]
  simp [Imperative.Cmd.eval,hc]

theorem functional (e : Expr) (body : Functional.Term) (i x y : Int) (s : State) (ls : List Int)
    (n : Int) (original : Nat → State → Option (ForInStep State))
    (hc : e.eval i x y s ls = some n)
    (hb : ∀ (k : Nat) t, lift (body.eval i x y [t] ((k : Int) :: ls)) = original k t) :
    (Functional.Term.forRange Nat.zero e body (.yield Nat.zero)).eval i x y [s] ls =
      forIn (List.range n.toNat) s original := by
  rw [forIn_lift _ _ _ _ hb]
  simp [Functional.Term.eval,hc]

end IRComparison.LoopFacts
