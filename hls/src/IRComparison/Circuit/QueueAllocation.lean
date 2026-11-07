import IRComparison.Circuit.CountedFrame

namespace IRComparison.Circuit

structure BuildExtension (before after : Build) : Prop where
  wires : before.wires.size ≤ after.wires.size
  queues : ∀ pair ∈ before.queues.toList, pair ∈ after.queues.toList
  nextQueue : before.nextQueue ≤ after.nextQueue

theorem BuildExtension.refl (b : Build) : BuildExtension b b := ⟨Nat.le_refl _,fun _ h => h,Nat.le_refl _⟩
theorem BuildExtension.trans (h : BuildExtension a b) (g : BuildExtension b c) : BuildExtension a c :=
  ⟨Nat.le_trans h.wires g.wires,fun p hp => g.queues p (h.queues p hp),Nat.le_trans h.nextQueue g.nextQueue⟩

def ExtendsBuild (f : Builder α) := ∀ b, BuildExtension b (f b).2

theorem extends_pure (a : α) : ExtendsBuild (pure a) := BuildExtension.refl

theorem extends_bind (f : Builder α) (g : α → Builder β) (hf : ExtendsBuild f)
    (hg : ∀ a, ExtendsBuild (g a)) : ExtendsBuild (f >>= g) :=
  fun b => (hf b).trans (hg (f b).1 (f b).2)

def Build.allocateQueue (b : Build) (capacity : Nat) : Build :=
  { b with queues := b.queues.push (b.nextQueue,capacity),nextQueue := b.nextQueue+1 }

theorem queue_run (b : Build) (capacity : Nat) : queue capacity b = (b.nextQueue,b.allocateQueue capacity) := rfl

theorem extends_queue (capacity : Nat) : ExtendsBuild (queue capacity) := by
  intro b
  refine ⟨Nat.le_refl _,?_,?_⟩
  · intro pair hp; simpa [queue_run,Build.allocateQueue] using Or.inl hp
  · change b.nextQueue ≤ b.nextQueue+1; omega

theorem extends_counted (start stride : Int) (count : Nat) (initial refill : List Load)
    (body : HybridIR.Cmd) (input qi qo : Nat) :
    ExtendsBuild (counted start stride count initial refill body input qi qo) := by
  intro b
  have hr := counted_resources start stride count initial refill body input qi qo b
  have hq := congrArg (fun r => r.2.1) hr
  have hn := congrArg (fun r => r.2.2.2) hr
  dsimp only [Build.resources] at hq hn
  refine ⟨counted_grows _ _ _ _ _ _ _ _ _ b,?_,?_⟩
  · intro pair hp; rw [hq]; exact hp
  · rw [hn]; exact Nat.le_refl _

theorem tailCode_extension (sizes : Nat → Nat) (incoming : Nat) (code : HybridCompactChainControl.Code) :
    ExtendsBuild (tailCode sizes incoming code) := by
  induction code generalizing incoming with
  | finish r => exact extends_bind _ _ (extends_queue 0) (fun _ =>
      extends_bind _ _ (extends_counted _ _ _ _ _ _ _ _ _) (fun _ => extends_pure _))
  | stage a s rest ih =>
    apply extends_bind _ _ (extends_queue _)
    intro out
    apply extends_bind _ _ (extends_counted _ _ _ _ _ _ _ _ _)
    intro _
    exact extends_bind _ _ (ih out) (fun _ => extends_pure _)

/-- The final table covers every capacity requested during construction. The
machine's lookup supplies this property once freshness of allocated IDs is
established; this is a construction fact, not a source-program assumption. -/
def CoversQueues (cap : Nat → Nat) (b : Build) : Prop :=
  ∀ q n, (q,n) ∈ b.queues.toList → n ≤ cap q

theorem CoversQueues.before {before after : Build} (h : CoversQueues cap after) (e : BuildExtension before after) :
    CoversQueues cap before := fun q n hn => h q n (e.queues (q,n) hn)

theorem CoversQueues.allocated {b : Build} (h : CoversQueues cap (b.allocateQueue n)) : n ≤ cap b.nextQueue :=
  h _ _ (by simp [Build.allocateQueue])

end IRComparison.Circuit
