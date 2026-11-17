import Std

/-! Semantic RHL rules shared by memory conversion and scheduling.
The source and target state types need not coincide. Failure is observable:
`Option.Rel` admits two failures, never a one-sided failure. Insertions must
succeed even when the requested postcondition is True. -/
namespace IRComparison.Relational

def Judgment (P : S → T → Prop) (source : S → Option A)
    (target : T → Option B) (Q : Option A → Option B → Prop) : Prop :=
  ∀ s t, P s t → Q (source s) (target t)

def Translation (P : S → T → Prop) (source : S → Option A)
    (target : T → Option B) (Q : A → B → Prop) : Prop :=
  Judgment P source target (Option.Rel Q)

abbrev Insertion (P : S → T → Prop) (target : T → Option U) (Q : S → U → Prop) :=
  Translation P some target Q

theorem skip : Translation P some some P := fun _ _ h => .some h

theorem consequence (h : Translation P f g Q)
    (pre : ∀ s t, P' s t → P s t) (post : ∀ a b, Q a b → Q' a b) :
    Translation P' f g Q' := by
  intro s t hp
  have hr := h s t (pre s t hp)
  cases hf : f s <;> cases hg : g t <;> simp only [hf,hg] at hr ⊢
  · exact .none
  · cases hr
  · cases hr
  · cases hr with
    | some hq => exact .some (post _ _ hq)

theorem seq (first : Translation P f g R) (second : Translation R f' g' Q) :
    Translation P (fun s => (f s).bind f') (fun t => (g t).bind g') Q := by
  intro s t hp
  have hr := first s t hp
  cases hf : f s <;> cases hg : g t <;> simp only [hf,hg,Option.bind_none,Option.bind_some] at hr ⊢
  · exact .none
  · cases hr
  · cases hr
  · cases hr with
    | some hr => exact second _ _ hr

theorem insertLeft (ins : Insertion P before R) (body : Translation R f g Q) :
    Translation P f (fun t => (before t).bind g) Q :=
  seq ins body

theorem insertRight (body : Translation P f g R) (ins : Insertion R after Q) :
    Translation P f (fun t => (g t).bind after) Q := by
  simpa using seq body ins

theorem insertion_succeeds (ins : Insertion P g Q) (hp : P s t) :
    ∃ u, g t = some u ∧ Q s u := by
  have h := ins s t hp
  cases hg : g t <;> simp only [hg] at h
  · cases h
  · cases h with
    | some hq => exact ⟨_,rfl,hq⟩

def branch (guard : S → Option Bool) (yes no : S → Option A) (s : S) : Option A := do
  if ← guard s then yes s else no s

/-- Guard evaluation must agree, including failure. Each branch receives
its own condition as in Tr-If, rather than requiring one unconditional proof. -/
theorem branch_rule (guards : ∀ s t, P s t → c s = d t)
    (yes : Translation (fun s t => P s t ∧ c s = some true) f g Q)
    (no : Translation (fun s t => P s t ∧ c s = some false) f' g' Q) :
    Translation P (branch c f f') (branch d g g') Q := by
  intro s t hp
  have hd := guards s t hp
  cases hc : c s with
  | none => simp only [branch,hc,← hd]; exact .none
  | some b =>
    cases b with
    | false => simpa only [branch,← hd,hc,Option.bind_some,Bool.false_eq_true,↓reduceIte]
        using no s t ⟨hp,hc⟩
    | true => simpa only [branch,← hd,hc,Option.bind_some,↓reduceIte]
        using yes s t ⟨hp,hc⟩

def iterate (step : Nat → S → Option S) : Nat → Nat → S → Option S
  | 0,_,s => some s
  | n+1,k,s => (step k s).bind (iterate step n (k+1))

theorem fold_rule {P : S → T → Prop} {f : S → A → Option S} {g : T → A → Option T}
    (body : ∀ a, Translation P (fun s => f s a) (fun t => g t a) P) (xs : List A) :
    Translation P (fun s => xs.foldlM f s) (fun t => xs.foldlM g t) P := by
  induction xs with
  | nil => exact skip
  | cons a xs ih => exact seq (body a) ih

/-- Tr-For for a counted loop. The invariant is arbitrary and indexed by
the iteration number, independently of the source loop's signed stride. -/
theorem for_rule {P : Nat → S → T → Prop} {f : Nat → S → Option S}
    {g : Nat → T → Option T} (body : ∀ k, Translation (P k) (f k) (g k) (P (k+1)))
    (n k : Nat) : Translation (P k) (iterate f n k) (iterate g n k) (P (k+n)) := by
  induction n generalizing k with
  | zero => exact skip
  | succ n ih =>
    simpa only [iterate, Nat.add_assoc, Nat.add_comm 1 n] using seq (body k) (ih (k+1))

/-- A derived counted-loop rule with target-only insertions between iterations.
The last iteration has no refill. `run` is an existing evaluator, connected by
its unfolding equation; this rule introduces no executable IR operation. -/
theorem for_with_refill_rule {P Q : Nat → S → T → Prop}
    {f : Nat → S → Option S} {g refill : Nat → T → Option T}
    {finish : T → Option U} {run : Nat → Nat → T → Option U}
    (body : ∀ k, k < limit → Translation (P k) (f k) (g k) (Q k))
    (insert : ∀ k, k+1 < limit → Insertion (Q k) (refill k) (P (k+1)))
    (last : ∀ k, Translation (Q k) some finish R)
    (unfold_run : ∀ n k t, run (n+1) k t = (g k t).bind (fun u =>
      if n = 0 then finish u else (refill k u).bind (run n (k+1))))
    (n k : Nat) (bound : k+n < limit) :
    Translation (P k) (iterate f (n+1) k) (run (n+1) k) R := by
  induction n generalizing k with
  | zero =>
    intro s t h
    simpa only [iterate,unfold_run,ite_true,Option.bind_some] using
      (seq (body k (by omega)) (last k)) s t h
  | succ n ih =>
    intro s t h
    simpa only [iterate,unfold_run,Nat.succ_ne_zero,ite_false,Option.bind_assoc] using
      (seq (insertRight (body k (by omega)) (insert k (by omega)))
        (ih (k+1) (by omega))) s t h

theorem of_eq (same : ∀ s, f s = g s) : Translation Eq f g Eq := by
  intro s t h
  subst t
  rw [same]
  cases g s with
  | none => exact .none
  | some v => exact .some rfl

theorem result_eq (h : Option.Rel Eq a b) : a = b := by
  cases h with
  | none => rfl
  | some same => exact congrArg some same

theorem eq_of_translation {f g : S → Option A} (h : Translation Eq f g Eq) (s : S) : f s = g s :=
  result_eq (h s s rfl)

end IRComparison.Relational
