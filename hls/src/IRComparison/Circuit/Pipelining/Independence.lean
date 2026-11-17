import IRComparison.Circuit.Pipelining.Actions

namespace IRComparison.Circuit.Pipelining

variable {α : Type} [ExpressionEvaluation α] [ExpressionDependencies α]
variable {a b : Action α} {as : List (Action α)}

def Apart (xs ys : List Cell) : Prop := ∀ c ∈ xs, c ∉ ys

instance (xs ys : List Cell) : Decidable (Apart xs ys) :=
  inferInstanceAs (Decidable (∀ c ∈ xs, c ∉ ys))

/-- RAW, WAR and WAW hazards, including partial-expression validity and FIFO
occupancy. Whole-array footprints are conservative, not a source restriction. -/
def Independent (a b : Action α) : Prop :=
  Apart (actionWrites a) (actionReads b) ∧
  Apart (actionWrites b) (actionReads a) ∧
  Apart (actionWrites a) (actionWrites b)

instance (a b : Action α) : Decidable (Independent a b) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def independent (a b : Action α) : Bool := decide (Independent a b)

/-- Ordered same-edge execution. Earlier writes must not feed later reads,
and writes must be disjoint. Earlier reads MAY be overwritten by later
actions: both read the pre-edge state. This is directional, not a swap rule. -/
def OrderedCompatible (a b : Action α) : Prop :=
  Apart (actionWrites a) (actionReads b) ∧
  Apart (actionWrites a) (actionWrites b)

instance (a b : Action α) : Decidable (OrderedCompatible a b) :=
  inferInstanceAs (Decidable (_ ∧ _))

def orderedCompatible (a b : Action α) : Bool := decide (OrderedCompatible a b)

theorem Independent.ordered (h : Independent a b) : OrderedCompatible a b :=
  ⟨h.1,h.2.2⟩

theorem commit_frame (us : List Update) (p : Payload) (c : Cell)
    (h : ∀ u ∈ us, u.1 ≠ c) : get (commit us p) c = get p c := by
  induction us generalizing p with
  | nil => rfl
  | cons u us ih =>
    change get (commit us (put p u.1 u.2)) c = get p c
    rw [ih _ (fun v hv => h v (by simp [hv])), get_put_other p u.1 c u.2 (h u (by simp))]

theorem commit_put (us : List Update) (p : Payload) (c : Cell) (v : Content)
    (h : ∀ u ∈ us, u.1 ≠ c) :
    commit us (put p c v) = put (commit us p) c v := by
  induction us generalizing p with
  | nil => rfl
  | cons u us ih =>
    change commit us (put (put p c v) u.1 u.2) = put (commit us (put p u.1 u.2)) c v
    rw [put_commute p c u.1 v u.2 (Ne.symm (h u (by simp)))]
    exact ih _ (fun w hw => h w (by simp [hw]))

theorem commit_commute (us vs : List Update) (p : Payload)
    (h : ∀ u ∈ us, ∀ v ∈ vs, u.1 ≠ v.1) :
    commit vs (commit us p) = commit us (commit vs p) := by
  induction vs generalizing p with
  | nil => rfl
  | cons v vs ih =>
    change commit vs (put (commit us p) v.1 v.2) = commit us (commit vs (put p v.1 v.2))
    rw [← commit_put us p v.1 v.2 (fun u hu => h u hu v (by simp))]
    exact ih _ (fun u hu w hw => h u hu w (by simp [hw]))

theorem prepare_after (ha : prepare cap a p = some us)
    (hd : Apart (actionWrites a) (actionReads b)) :
    prepare cap b (commit us q) = prepare cap b q := by
  apply prepare_agrees
  intro c hc
  apply commit_frame
  intro u hu eq
  have hw := prepare_writes ha u hu
  exact hd _ hw (eq ▸ hc)

theorem independent_sound (cap : Nat → Nat) (a b : Action α)
    (h : independent a b = true) : Commutes (Action.eval cap) a b := by
  have hh : Independent a b := of_decide_eq_true h
  intro p
  simp only [← prepare_correct]
  cases ha : prepare cap a p with
  | none =>
    cases hb : prepare cap b p with
    | none => rfl
    | some vs => simp [← prepare_correct,prepare_after hb hh.2.1,ha]
  | some us =>
    have hb' := prepare_after (q := p) (b := b) ha hh.1
    cases hb : prepare cap b p with
    | none => simp [← prepare_correct,hb',hb]
    | some vs =>
      have ha' := prepare_after (q := p) (b := a) hb hh.2.1
      simp only [Option.map_some,Option.bind_some,← prepare_correct,hb',ha',ha,hb,Option.map_some]
      congr 1
      exact commit_commute us vs p (fun u hu v hv eq =>
        hh.2.2 _ (prepare_writes ha u hu) (eq ▸ prepare_writes hb v hv))

/-- All right hand sides are read from `old`; the accumulator contains only
pending writes. This is simultaneous clock-edge execution, not a sequential
interpreter renamed as a clock. Failure discards the payload result. -/
def clockFrom (cap : Nat → Nat) (old : Payload) : List (Action α) → Payload → Option Payload
  | [], pending => some pending
  | a :: as, pending => (prepare cap a old).bind (fun us => clockFrom cap old as (commit us pending))

def clock (cap : Nat → Nat) (as : List (Action α)) (p : Payload) : Option Payload := clockFrom cap p as p

/-- The list order is significant even though right hand sides all read
the old state. Reordering still uses the stronger Independent relation. -/
def BundleSafe (as : List (Action α)) : Prop := as.Pairwise OrderedCompatible

instance (as : List (Action α)) : Decidable (BundleSafe as) :=
  inferInstanceAs (Decidable (as.Pairwise OrderedCompatible))

theorem independent_bundle_safe (h : as.Pairwise Independent) : BundleSafe as :=
  h.imp (fun hab => hab.ordered)

theorem clockFrom_correct (as : List (Action α)) (safe : BundleSafe as) (old pending : Payload)
    (same : ∀ a ∈ as, Agrees (actionReads a) old pending) :
    clockFrom cap old as pending = evalList (Action.eval cap) as pending := by
  induction as generalizing pending with
  | nil => rfl
  | cons a as ih =>
    have hs := List.pairwise_cons.mp safe
    have ha := prepare_agrees cap a old pending (same a (by simp))
    simp only [clockFrom, evalList, ← prepare_correct, ha]
    cases hp : prepare cap a pending with
    | none => rfl
    | some us =>
      simp only [Option.map_some,Option.bind_some]
      apply ih hs.2
      intro b hb c hc
      rw [same b (by simp [hb]) c hc]
      symm
      apply commit_frame
      intro u hu eq
      exact (hs.1 b hb).1 _ (prepare_writes hp u hu) (eq ▸ hc)

theorem clock_correct (as : List (Action α)) (safe : BundleSafe as) (p : Payload) :
    clock cap as p = evalList (Action.eval cap) as p :=
  clockFrom_correct as safe p p (fun _ _ _ _ => rfl)

/-- General RHL rule: the sequential list and one simultaneous edge agree,
including failures. No syntactic restriction on the operand expressions. -/
theorem bundle_rule (safe : BundleSafe as) :
    Relational.Translation Eq (evalList (Action.eval cap) as) (clock cap as) Eq :=
  Relational.of_eq (fun p => (clock_correct as safe p).symm)

theorem ordered_bundle_rhl (safe : BundleSafe as) :
    RHL Eq (evalList (Action.eval cap) as) (clock cap as) Eq := by
  intro p q hpq
  subst q
  exact Relational.eq_of_translation (bundle_rule safe) p

theorem ordered_pair_rhl (h : OrderedCompatible a b) :
    RHL Eq (evalList (Action.eval cap) [a,b]) (clock cap [a,b]) Eq := by
  apply ordered_bundle_rhl
  simpa [BundleSafe] using h

end IRComparison.Circuit.Pipelining
