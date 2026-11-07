import IRComparison.Circuit.InstructionsSound

namespace IRComparison.Circuit

theorem allocateChannels_extension (capacity : Nat → Nat) (ids : List Nat) :
    ExtendsBuild (allocateChannels capacity ids) := by
  induction ids with
  | nil => exact extends_pure _
  | cons a ids ih => exact extends_bind _ _ (extends_queue _) (fun _ => extends_bind _ _ ih (fun _ => extends_pure _))

theorem allocateChannels_queues (capacity : Nat → Nat) (ids : List Nat) :
    PreservesQueues (allocateChannels capacity ids) := by
  induction ids with
  | nil => exact queues_pure _
  | cons a ids ih => exact queues_bind _ _ (queues_allocate _) (fun _ => queues_bind _ _ ih (fun _ => queues_pure _))

structure ChannelsAllocated (capacity : Nat → Nat) (ids : List Nat) (b : Build)
    (entries : List (Nat × Nat)) (after : Build) : Prop where
  names : entries.map Prod.fst = ids
  distinct : entries.Pairwise (fun p q => p.2 ≠ q.2)
  bounds : ∀ pair ∈ entries, b.nextQueue ≤ pair.2 ∧ pair.2 < after.nextQueue
  requested : ∀ pair ∈ entries, (pair.2,capacity pair.1) ∈ after.queues.toList
  wires : after.wires = b.wires
  arrays : after.nextArray = b.nextArray

theorem allocateChannels_correct (capacity : Nat → Nat) (ids : List Nat) (b : Build) :
    ChannelsAllocated capacity ids b (allocateChannels capacity ids b).1 (allocateChannels capacity ids b).2 := by
  induction ids generalizing b with
  | nil =>
    change ChannelsAllocated capacity [] b [] b
    exact ⟨rfl,by simp,by simp,by simp,rfl,rfl⟩
  | cons a ids ih =>
    let next := b.allocateQueue (capacity a)
    have tail := ih next
    have extension := allocateChannels_extension capacity ids next
    change ChannelsAllocated capacity (a::ids) b
      ((a,b.nextQueue)::(allocateChannels capacity ids next).1) (allocateChannels capacity ids next).2
    refine ⟨by simp only [List.map_cons,tail.names],?_,?_,?_,tail.wires,tail.arrays⟩
    · apply List.pairwise_cons.mpr
      refine ⟨?_,tail.distinct⟩
      intro pair hp
      have := (tail.bounds pair hp).1
      change b.nextQueue+1 ≤ pair.2 at this
      dsimp only
      omega
    · intro pair hp
      rcases List.mem_cons.mp hp with rfl | hp
      · have := extension.nextQueue
        change b.nextQueue+1 ≤ _ at this
        exact ⟨Nat.le_refl _,by dsimp; omega⟩
      · have hb := tail.bounds pair hp
        change b.nextQueue+1 ≤ pair.2 ∧ _ at hb
        exact ⟨by omega,hb.2⟩
    · intro pair hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact extension.queues _ (by simp [next,Build.allocateQueue])
      · exact tail.requested pair hp

theorem channelLookup_member (entries : List (Nat × Nat)) (member : a ∈ entries.map Prod.fst) :
    (a,channelLookup entries a) ∈ entries := by
  induction entries with
  | nil => contradiction
  | cons pair rest ih =>
    by_cases he : pair.1 = a
    · have eq : channelLookup (pair::rest) a = pair.2 := by simp [channelLookup,he]
      rw [eq,← he]
      exact List.mem_cons_self
    · have tail : a ∈ rest.map Prod.fst := by simpa [he,Ne.symm he] using member
      have eq : channelLookup (pair::rest) a = channelLookup rest a := by simp [channelLookup,he]
      rw [eq]
      exact List.mem_cons_of_mem _ (ih tail)

theorem distinct_snd_injective (entries : List (Nat × Nat))
    (h : entries.Pairwise (fun p q => p.2 ≠ q.2))
    (hp : p ∈ entries) (hq : q ∈ entries) (eq : p.2 = q.2) : p = q := by
  induction entries with
  | nil => contradiction
  | cons a rest ih =>
    have hh := List.pairwise_cons.mp h
    rcases List.mem_cons.mp hp with rfl | hpt
    · rcases List.mem_cons.mp hq with rfl | hqt
      · rfl
      · exact False.elim (hh.1 q hqt eq)
    · rcases List.mem_cons.mp hq with rfl | hqt
      · exact False.elim (hh.1 p hpt eq.symm)
      · exact ih hh.2 hpt hqt

theorem ChannelsAllocated.channels (h : ChannelsAllocated capacity ids b entries after) :
    ChannelMap ids (channelLookup entries) after.nextQueue := by
  have member : ∀ a ∈ ids, (a,channelLookup entries a) ∈ entries := by
    intro a ha; apply channelLookup_member; rwa [h.names]
  refine ⟨?_,fun a ha => (h.bounds _ (member a ha)).2⟩
  intro a ha d hd eq
  exact congrArg Prod.fst (distinct_snd_injective entries h.distinct (member a ha) (member d hd) eq)

theorem ChannelsAllocated.capacity {capacity : Nat → Nat} (h : ChannelsAllocated capacity ids b entries after)
    (covered : CoversQueues cap after) (member : a ∈ ids) : capacity a ≤ cap (channelLookup entries a) := by
  have hm := channelLookup_member entries (a:=a) (by rwa [h.names])
  exact covered _ _ (h.requested _ hm)

end IRComparison.Circuit
