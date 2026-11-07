import IRComparison.Frontend.NativeBody

namespace IRComparison.BodyFacts

theorem storeImperative (a : Nat) (address value : Expr) (i x y : Int) (s : State) (locals : List Int)
    (j v : Int) (hj : address.eval i x y s locals = some j) (hv : value.eval i x y s locals = some v) :
    (Imperative.Cmd.store a address value).eval i x y s locals = s.write a j v := by
  simp [Imperative.Cmd.eval, hj, hv]

theorem storeFunctional (a : Nat) (address value : Expr) (i x y : Int) (s : State) (locals : List Int)
    (j v : Int) (hj : address.eval i x y s locals = some j) (hv : value.eval i x y s locals = some v) :
    (Functional.Term.letWrite Nat.zero a address value (.yield Nat.zero)).eval i x y [s] locals = s.write a j v := by
  simp [Functional.Term.eval, hj, hv]

theorem storeImperativeLiteral (a : Nat) (address value : Expr) (i x y : Int) (s : State) (locals : List Int)
    (j v : Int) (hj : address.eval i x y s locals = some j) (hv : value.eval i x y s locals = some v) :
    (Imperative.Cmd.store a address value).eval i x y s locals =
      s.write (@OfNat.ofNat Nat a (instOfNatNat a)) j v :=
  storeImperative a address value i x y s locals j v hj hv

theorem storeFunctionalLiteral (a : Nat) (address value : Expr) (i x y : Int) (s : State) (locals : List Int)
    (j v : Int) (hj : address.eval i x y s locals = some j) (hv : value.eval i x y s locals = some v) :
    (Functional.Term.letWrite Nat.zero a address value (.yield Nat.zero)).eval i x y [s] locals =
      s.write (@OfNat.ofNat Nat a (instOfNatNat a)) j v :=
  storeFunctional a address value i x y s locals j v hj hv

theorem branchImperative (c : Expr) (a b : Imperative.Cmd) (i x y : Int) (s : State) (locals : List Int)
    (v : Int) (decision : Decidable ((v != 0) = true)) (yes no : Option State)
    (hc : c.eval i x y s locals = some v) (ha : a.eval i x y s locals = yes) (hb : b.eval i x y s locals = no) :
    (Imperative.Cmd.branch c a b).eval i x y s locals =
      @ite (Option State) ((v != 0) = true) decision yes no := by
  by_cases h : v = 0 <;> simp [Imperative.Cmd.eval,hc,ha,hb,h]

theorem branchFunctional (c : Expr) (a b : Functional.Term) (i x y : Int) (s : State) (locals : List Int)
    (v : Int) (decision : Decidable ((v != 0) = true)) (yes no : Option State)
    (hc : c.eval i x y s locals = some v) (ha : a.eval i x y [s] locals = yes) (hb : b.eval i x y [s] locals = no) :
    (Functional.Term.branch Nat.zero c a b).eval i x y [s] locals =
      @ite (Option State) ((v != 0) = true) decision yes no := by
  by_cases h : v = 0 <;> simp [Functional.Term.eval,hc,ha,hb,h]

/-- Sequencing preserves failure and passes the resulting state to the next
    computation. These lemmas quantify every state, not just successful writes. -/
theorem seqImperative (a b : Imperative.Cmd) (i x y : Int) (s : State) (locals : List Int)
    (first : Option State) (next : State → Option State)
    (ha : a.eval i x y s locals = first) (hb : ∀ t, b.eval i x y t locals = next t) :
    (Imperative.Cmd.seq a b).eval i x y s locals = first >>= next := by
  cases first <;> simp [Imperative.Cmd.eval,ha,hb]

theorem seqFunctional (a b : Functional.Term) (i x y : Int) (s : State) (locals : List Int)
    (first : Option State) (next : State → Option State)
    (ha : a.eval i x y [s] locals = first) (hb : ∀ t, b.eval i x y [t] locals = next t) :
    (Functional.Term.letResult Nat.zero a
      (.letResult Nat.zero b (.yield Nat.zero))).eval i x y [s] locals = first >>= next := by
  cases first <;> simp [Functional.Term.eval,ha,hb]

theorem skipImperative (i x y : Int) (s : State) (locals : List Int) :
    Imperative.Cmd.skip.eval i x y s locals = some s := rfl

theorem skipFunctional (i x y : Int) (s : State) (locals : List Int) :
    (Functional.Term.yield Nat.zero).eval i x y [s] locals = some s := rfl

theorem returnImperative (i x y : Int) (s : State) (locals : List Int) :
    Imperative.Cmd.skip.eval i x y s locals = (pure s : Option State) := rfl

theorem returnFunctional (i x y : Int) (s : State) (locals : List Int) :
    (Functional.Term.yield Nat.zero).eval i x y [s] locals = (pure s : Option State) := rfl

/-- Read bindings preserve failure, even when the bound value is unused. -/
theorem letImperative (e : Expr) (b : Imperative.Cmd) (i x y : Int) (s : State) (locals : List Int)
    (first : Option Int) (next : Int → Option State)
    (he : e.eval i x y s locals = first)
    (hb : ∀ v, b.eval i x y s (v :: locals) = next v) :
    (Imperative.Cmd.letValue e b).eval i x y s locals = first >>= next := by
  cases first <;> simp [Imperative.Cmd.eval,he,hb]

theorem letFunctional (e : Expr) (b : Functional.Term) (i x y : Int) (s : State) (locals : List Int)
    (first : Option Int) (next : Int → Option State)
    (he : e.eval i x y s locals = first)
    (hb : ∀ v, b.eval i x y [s] (v :: locals) = next v) :
    (Functional.Term.letValue Nat.zero e b).eval i x y [s] locals = first >>= next := by
  cases first <;> simp [Functional.Term.eval,he,hb]

end IRComparison.BodyFacts
