import IRComparison.Circuit.QueueAllocation

namespace IRComparison.Circuit

structure QueueWellFormed (b : Build) : Prop where
  distinct : b.queues.toList.Pairwise (fun p q => p.1 ≠ q.1)
  fresh : ∀ p ∈ b.queues.toList, p.1 < b.nextQueue

theorem QueueWellFormed.allocate {b : Build} (h : QueueWellFormed b) (capacity : Nat) :
    QueueWellFormed (b.allocateQueue capacity) := by
  constructor
  · simp only [Build.allocateQueue,Array.toList_push,List.pairwise_append,List.pairwise_singleton,true_and]
    refine ⟨h.distinct,?_⟩
    intro p hp q hq
    have eq : q = (b.nextQueue,capacity) := by simpa using hq
    subst q
    have := h.fresh p hp
    omega
  · intro p hp
    simp only [Build.allocateQueue,Array.toList_push,List.mem_append,List.mem_singleton] at hp ⊢
    rcases hp with hp | rfl
    · have := h.fresh p hp; omega
    · omega

theorem QueueWellFormed.resources {b c : Build} (h : QueueWellFormed b) (same : c.resources = b.resources) :
    QueueWellFormed c := by
  have hq := congrArg (fun r => r.2.1) same
  have hn := congrArg (fun r => r.2.2.2) same
  dsimp only [Build.resources] at hq hn
  exact ⟨by simpa [hq] using h.distinct,by simpa [hq,hn] using h.fresh⟩

theorem queue_find (entries : List (Nat × Nat)) (distinct : entries.Pairwise (fun p q => p.1 ≠ q.1))
    (member : (q,n) ∈ entries) : entries.find? (fun p => p.1 == q) = some (q,n) := by
  induction entries with
  | nil => contradiction
  | cons head tail ih =>
    have pair := List.pairwise_cons.mp distinct
    rcases List.mem_cons.mp member with he | ht
    · rw [← he]; simp
    · have ne := pair.1 (q,n) ht
      dsimp only at ne
      simpa only [List.find?,beq_false_of_ne ne] using ih pair.2 ht

theorem QueueWellFormed.covers {b : Build} (h : QueueWellFormed b) (schedule : Schedule) :
    CoversQueues (schedule.assemble b.queues).capacity b := by
  intro q n hn
  have he := queue_find b.queues.toList h.distinct hn
  simp [Machine.capacity,Schedule.assemble,he]

def PreservesQueues (f : Builder α) := ∀ b, QueueWellFormed b → QueueWellFormed (f b).2

theorem queues_of_resources (f : Builder α) (hf : PreservesResources f) : PreservesQueues f :=
  fun b h => h.resources (hf b)

theorem queues_pure (a : α) : PreservesQueues (pure a) := fun _ h => h

theorem queues_bind (f : Builder α) (g : α → Builder β) (hf : PreservesQueues f)
    (hg : ∀ a, PreservesQueues (g a)) : PreservesQueues (f >>= g) :=
  fun b h => hg (f b).1 (f b).2 (hf b h)

theorem queues_allocate (capacity : Nat) : PreservesQueues (queue capacity) :=
  fun _ h => h.allocate capacity

theorem tailCode_queues (sizes : Nat → Nat) (incoming : Nat) (code : HybridCompactChainControl.Code) :
    PreservesQueues (tailCode sizes incoming code) := by
  induction code generalizing incoming with
  | finish r => exact queues_bind _ _ (queues_allocate 0) (fun _ =>
      queues_bind _ _ (queues_of_resources _ (counted_resources _ _ _ _ _ _ _ _ _)) (fun _ => queues_pure _))
  | stage a s rest ih =>
    exact queues_bind _ _ (queues_allocate _) (fun out =>
      queues_bind _ _ (queues_of_resources _ (counted_resources _ _ _ _ _ _ _ _ _)) (fun _ =>
        queues_bind _ _ (ih out) (fun _ => queues_pure _)))

end IRComparison.Circuit
