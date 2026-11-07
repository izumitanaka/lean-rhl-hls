import IRComparison.Circuit.QueueAllocation

namespace IRComparison.Circuit

structure ChannelMap (ids : List Nat) (mapping : Nat → Nat) (next : Nat) : Prop where
  injective : ∀ a ∈ ids, ∀ b ∈ ids, mapping a = mapping b → a = b
  below : ∀ a ∈ ids, mapping a < next

def channelView (ids : List Nat) (mapping : Nat → Nat) (physical : Nat → List Int) : GlobalPipeline.Queues :=
  fun a => if a ∈ ids then physical (mapping a) else []

theorem ChannelMap.grow (h : ChannelMap ids mapping n) (hn : n ≤ m) : ChannelMap ids mapping m :=
  ⟨h.injective,fun a ha => Nat.lt_of_lt_of_le (h.below a ha) hn⟩

theorem channelView_private (h : ChannelMap ids mapping next) (fresh : next ≤ q) :
    channelView ids mapping (GlobalPipeline.put physical q values) = channelView ids mapping physical := by
  funext a
  by_cases ha : a ∈ ids
  · have different : mapping a ≠ q := by have := h.below a ha; omega
    simp [channelView,GlobalPipeline.put,ha,different]
  · simp [channelView,ha]

theorem channelView_public (h : ChannelMap ids mapping next) (member : a ∈ ids) :
    channelView ids mapping (GlobalPipeline.put physical (mapping a) values) =
      GlobalPipeline.put (channelView ids mapping physical) a values := by
  funext b
  by_cases same : b = a
  · subst b; simp [channelView,GlobalPipeline.put,member]
  · by_cases hb : b ∈ ids
    · have different : mapping b ≠ mapping a := fun he => same (h.injective b hb a member he)
      simp [channelView,GlobalPipeline.put,hb,different,same]
    · simp [channelView,GlobalPipeline.put,hb,same]

theorem channelView_put_unmapped (absent : a ∉ ids) :
    GlobalPipeline.put (channelView ids mapping physical) a [] = channelView ids mapping physical := by
  funext b
  by_cases same : b = a
  · subst b; simp [channelView,GlobalPipeline.put,absent]
  · simp [GlobalPipeline.put,same]

end IRComparison.Circuit
