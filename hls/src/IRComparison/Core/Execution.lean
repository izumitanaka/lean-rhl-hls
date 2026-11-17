/-! Shared finite execution facts. Individual controllers retain their own
states and transition functions; only deterministic reachability is shared. -/
namespace IRComparison.Execution

@[simp] def run (step : α → α) : Nat → α → α
  | 0, s => s
  | n+1, s => run step n (step s)

inductive Reaches (step : α → α) : α → α → Prop where
  | refl (a) : Reaches step a a
  | next : Reaches step (step a) b → Reaches step a b

theorem Reaches.trans (h : Reaches step a b) (k : Reaches step b c) : Reaches step a c := by
  induction h with
  | refl => exact k
  | next _ ih => exact .next (ih k)

theorem Reaches.finite (h : Reaches step a b) : ∃ n, run step n a = b := by
  induction h with
  | refl => exact ⟨0,rfl⟩
  | next _ ih => obtain ⟨n,hn⟩ := ih; exact ⟨n+1,hn⟩

/-- Lift an execution through an embedding. A source step may correspond to
zero, one, or several target steps, including a stopped source submachine. -/
theorem Reaches.map {step : α → α} {target : β → β} {a b : α}
    (h : Reaches step a b) (f : α → β)
    (advance : ∀ a, Reaches target (f a) (f (step a))) :
    Reaches target (f a) (f b) := by
  induction h with
  | refl => exact .refl _
  | next _ ih => exact (advance _).trans ih

end IRComparison.Execution
