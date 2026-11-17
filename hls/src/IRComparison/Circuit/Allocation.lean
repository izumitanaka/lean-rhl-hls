import IRComparison.Circuit.CountedBackend
import IRComparison.Circuit.LayoutScope
import IRComparison.Circuit.BuildInvariant

/-! Allocation invariants of the executable circuit builder. These describe
physical declarations, independently of source execution and RTL validation. -/
namespace IRComparison.Circuit.Allocation

structure Bank (entries : Array (Nat × Nat)) (nextId : Nat) : Prop where
  unique : (entries.toList.map Prod.fst).Nodup
  below : ∀ p ∈ entries.toList, p.1 < nextId

theorem Bank.push (h : Bank entries nextId) (capacity : Nat) :
    Bank (entries.push (nextId,capacity)) (nextId+1) := by
  constructor
  · simp only [Array.toList_push,List.map_append,List.map_cons,List.map_nil]
    apply List.nodup_append.mpr
    refine ⟨h.unique,by simp,?_⟩
    intro a ha b hb
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp ha
    have bound := h.below p hp
    simp only [List.mem_singleton] at hb
    omega
  · intro p hp
    simp only [Array.toList_push,List.mem_append,List.mem_singleton] at hp
    rcases hp with hp | rfl
    · have := h.below p hp; omega
    · simp

structure Valid (b : Build) : Prop where
  memories : Bank b.memories b.nextArray
  queues : Bank b.queues b.nextQueue

/-- Allocation appends declarations; it never renames or resizes an old bank. -/
structure Extends (before after : Build) : Prop where
  memories : before.memories.toList.IsPrefix after.memories.toList
  queues : before.queues.toList.IsPrefix after.queues.toList

theorem Extends.refl (b : Build) : Extends b b := ⟨⟨[],by simp⟩,⟨[],by simp⟩⟩
theorem Extends.trans (h : Extends a b) (k : Extends b c) : Extends a c :=
  ⟨h.memories.trans k.memories,h.queues.trans k.queues⟩

def Preserves (action : Builder α) : Prop :=
  ∀ b, Valid b → Valid (action b).2 ∧ Extends b (action b).2

theorem resources_preserves (h : PreservesResources action) : Preserves action := by
  intro b hb
  have same := h b
  have hm := congrArg (fun r => r.1) same
  have hq := congrArg (fun r => r.2.1) same
  have hn := congrArg (fun r => r.2.2.1) same
  have hk := congrArg (fun r => r.2.2.2) same
  dsimp only [Build.resources] at hm hq hn hk
  constructor
  · exact ⟨by simpa only [hm,hn] using hb.memories, by simpa only [hq,hk] using hb.queues⟩
  · constructor <;> simp only [hm,hq] <;> exact ⟨[],by simp⟩

theorem queue_preserves (capacity : Nat) : Preserves (queue capacity) := by
  intro b hb
  change Valid { b with queues := b.queues.push (b.nextQueue,capacity), nextQueue := b.nextQueue+1 } ∧
    Extends b { b with queues := b.queues.push (b.nextQueue,capacity), nextQueue := b.nextQueue+1 }
  refine ⟨⟨hb.memories,hb.queues.push capacity⟩,?_,?_⟩
  · exact ⟨[],by simp⟩
  · exact ⟨[(b.nextQueue,capacity)],by simp⟩

theorem snapshot_preserves (source : Nat) (sizes : Nat → Nat) : Preserves (snapshot source sizes) := by
  intro b hb
  change Valid { b with memories := b.memories.push (b.nextArray,sizes source), nextArray := b.nextArray+1 } ∧
    Extends b { b with memories := b.memories.push (b.nextArray,sizes source), nextArray := b.nextArray+1 }
  refine ⟨⟨hb.memories.push _,hb.queues⟩,?_,?_⟩
  · exact ⟨[(b.nextArray,sizes source)],by simp⟩
  · exact ⟨[],by simp⟩

private theorem anchored (original : Build) (h : Preserves action) :
    BuildInvariant.Preserves (fun b => Valid b ∧ Extends original b) action := by
  intro b hb
  obtain ⟨valid,kept⟩ := h b hb.1
  exact ⟨valid,hb.2.trans kept⟩

private def rules (original : Build) : BuildInvariant.Rules (fun b => Valid b ∧ Extends original b) where
  fresh := fun r => anchored original (resources_preserves (resources_fresh r))
  queue := fun n => anchored original (queue_preserves n)
  snapshot := fun a sizes => anchored original (snapshot_preserves a sizes)

/-- Every code variant retains the input layout and allocates distinct banks.
The theorem covers both counted backends through their existing contract. -/
theorem schedule_allocated (backend : CountedBackend) (layout : Array (Nat × Nat))
    (unique : (layout.toList.map Prod.fst).Nodup) (code : HybridUnifiedPipeline.Code) :
    Valid (scheduleWith backend.build layout code).build ∧
    Extends { memories := layout, nextArray := layoutLimit layout }
      (scheduleWith backend.build layout code).build := by
  have initial : Valid { memories := layout, nextArray := layoutLimit layout } := by
    refine ⟨⟨unique,?_⟩,⟨by simp,by simp⟩⟩
    intro p hp
    exact layout_member_bound hp
  exact (rules { memories := layout, nextArray := layoutLimit layout }).schedule backend.build
    (fun start stride count initial refill body input qi qo =>
      anchored _ (resources_preserves (backend.resources start stride count initial refill body input qi qo)))
    layout code ⟨initial,.refl _⟩

end IRComparison.Circuit.Allocation

namespace IRComparison.Circuit.WireAllocation

/-- Allocating private holding registers preserves every earlier range.
Memory-bank preservation alone does not imply this separate property. -/
def Extends (before after : Build) : Prop := before.wires.toList.IsPrefix after.wires.toList

theorem Extends.refl (b : Build) : Extends b b := ⟨[],by simp⟩
theorem Extends.trans (a : Extends first second) (b : Extends second third) : Extends first third :=
  List.IsPrefix.trans a b

theorem Extends.size (h : Extends before after) : before.wires.size ≤ after.wires.size := by
  simpa using List.IsPrefix.length_le h

theorem Extends.get (h : Extends before after) (valid : n < before.wires.size) :
    before.wires[n]? = after.wires[n]? := by
  have nextValid : n < after.wires.size := Nat.lt_of_lt_of_le valid h.size
  have eq := List.IsPrefix.getElem h (by simpa using valid)
  simpa [Array.getElem?_eq_getElem valid,Array.getElem?_eq_getElem nextValid] using congrArg some eq

private def rules (original : Build) : BuildInvariant.Rules (Extends original) where
  fresh := fun r b h => h.trans (show Extends b (b.addWire r) from
    ⟨[⟨min 0 r.lo,max 0 r.hi⟩],by simp [Build.addWire]⟩)
  queue := fun _ _ h => h
  snapshot := fun _ _ _ h => h

theorem command (c : HybridIR.Cmd) (i : Expr) (locals : List Expr) (output : Nat) (b : Build) :
    Extends b (Circuit.command i locals output c b).2 :=
  (rules b).command c i locals output b (.refl b)

theorem channelLower (c : HybridIR.ChannelCmd) (buffers i locals b) :
    Extends b (ChannelLower.lower buffers i locals c b).2 :=
  (rules b).channelLower c buffers i locals b (.refl b)

theorem reserve (c : HybridIR.ChannelCmd) (b : Build) : Extends b (ChannelLower.reserve c b) := by
  unfold Extends ChannelLower.reserve
  simp only [Array.toList_append]
  exact ⟨_,rfl⟩

private theorem named (original : Build) (start stride count initial refill body input qi qo) :
    BuildInvariant.Preserves (Extends original)
      (CountedBackend.named.build start stride count initial refill body input qi qo) := by
  intro b h
  exact (rules original).channelLower _ _ _ _ _ (h.trans (reserve _ b))

theorem symbolicInstructions (sizes channels : Nat → Nat) (cs : List HybridSymbolicGlobal.Instruction) (b : Build) :
    Extends b (symbolicInstructionsWith CountedBackend.named.build sizes channels cs b).2 :=
  (rules b).symbolicInstructions CountedBackend.named.build (named b) sizes channels cs b (.refl _)

theorem symbolicInstruction (sizes channels : Nat → Nat) (c : HybridSymbolicGlobal.Instruction) (b : Build) :
    Extends b (symbolicInstructionWith CountedBackend.named.build sizes channels c b).2 :=
  (rules b).symbolicInstruction CountedBackend.named.build (named b) sizes channels c b (.refl _)

theorem channels (capacity : Nat → Nat) (ids : List Nat) (b : Build) :
    Extends b (allocateChannels capacity ids b).2 :=
  (rules b).channels capacity ids b (.refl _)

theorem chooseInput (channels : Nat → Nat) (mode : GlobalPipeline.InputMode) (b : Build) :
    Extends b (chooseInputQueue channels mode b).2 :=
  (rules b).chooseInput channels mode b (.refl _)

theorem chooseOutput (channels : Nat → Nat) (budget : Nat) (output : Option Nat) (b : Build) :
    Extends b (chooseOutputQueue channels budget output b).2 :=
  (rules b).chooseOutput channels budget output b (.refl _)

theorem scheduled (layout : Array (Nat × Nat)) (code : HybridUnifiedPipeline.Code) :
    Extends {memories := layout,nextArray := layoutLimit layout}
      (scheduleWith CountedBackend.named.build layout code).build :=
  (rules _).schedule CountedBackend.named.build (named _) layout code (.refl _)

end IRComparison.Circuit.WireAllocation
