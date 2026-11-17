import IRComparison.Circuit.ChannelReferenceScope
import IRComparison.Circuit.ReferenceProperties

namespace IRComparison.Circuit
open ReferenceScope HybridSymbolicGlobal

private theorem inputQueue_declared (mode : GlobalPipeline.InputMode)
    (mapped : ∀ a, mode = .channel a → Queue b (channels a)) :
    Queue (chooseInputQueue channels mode b).2 (chooseInputQueue channels mode b).1 := by
  cases mode with
  | channel a => exact mapped a rfl
  | memory a order fifo =>
    refine ⟨if fifo then order.length else 0,?_⟩
    simp [chooseInputQueue,queue_run,Build.allocateQueue]

private theorem outputQueue_declared (output : Option Nat)
    (mapped : ∀ a ∈ output.toList, Queue b (channels a)) :
    Queue (chooseOutputQueue channels budget output b).2 (chooseOutputQueue channels budget output b).1 := by
  cases output with
  | some a => exact mapped a (by simp)
  | none => exact ⟨budget,by simp [chooseOutputQueue,queue_run,Build.allocateQueue]⟩

private theorem symbolicSchedule_references (a : InstructionLayout) (c : HybridSymbolicGlobal.Instruction)
    (frozen : Copy final a.frozen (symbolicInput c))
    (input : Queue final a.inputQueue) (output : Queue final a.outputQueue)
    (outputs : ∀ id ∈ (symbolicOutput c).toList, Memory final id)
    (body : Control final a.body) : Control final (symbolicSchedule a c) := by
  cases c <;> simp_all [symbolicSchedule,symbolicMode,symbolicOutput,Control,Operation]

/-- Snapshot, queue choices and the named body all use declarations produced
by the actual allocator. Copies have matching capacities by construction. -/
theorem symbolicInstruction_references (c : HybridSymbolicGlobal.Instruction)
    (sources : ∀ a ∈ symbolicInput c :: (symbolicOutput c).toList ++ allCommandArrays c.body,
      (a,sizes a) ∈ b.memories.toList)
    (inputs : 2 ≤ b.wires.size)
    (inputMap : ∀ a, symbolicMode c = .channel a → Queue b (channels a))
    (outputMap : ∀ a ∈ (symbolicOutput c).toList, Queue b (channels a))
    (wiresKept : WireAllocation.Extends
      (symbolicInstructionWith CountedBackend.named.build sizes channels c b).2 final)
    (kept : ReferenceScope.Extension
      (symbolicInstructionWith CountedBackend.named.build sizes channels c b).2 final) :
    Control final (symbolicInstructionWith CountedBackend.named.build sizes channels c b).1 := by
  let b0 := b.allocateSnapshot (symbolicInput c) sizes
  have old : ReferenceScope.Extension b b0 := ⟨Nat.le_refl _,by
    intro p hp; simpa [b0,Build.allocateSnapshot] using Or.inl hp,fun _ hq => hq⟩
  have privateMemory : (b.nextArray,sizes (symbolicInput c)) ∈ b0.memories.toList := by
    simp [b0,Build.allocateSnapshot]
  have hi := ReferenceScope.Extension.chooseInput channels (symbolicMode c) b0
  have inputDeclared := inputQueue_declared (symbolicMode c) (fun a eq => (inputMap a eq).extend old)
  change (let (qi,b1) := chooseInputQueue channels (symbolicMode c) b0;
    let (qo,b2) := chooseOutputQueue channels (symbolicBudget c) (symbolicOutput c) b1;
    let (body,_) := CountedBackend.named.build (symbolicBody c).start (symbolicBody c).stride (symbolicBody c).count
      (symbolicInitial c) (symbolicRefill c) (symbolicBody c).body b.nextArray qi qo b2;
    Control final (symbolicSchedule ⟨b.nextArray,qi,qo,body⟩ c))
  change (let (qi,b1) := chooseInputQueue channels (symbolicMode c) b0;
    let (qo,b2) := chooseOutputQueue channels (symbolicBudget c) (symbolicOutput c) b1;
    ReferenceScope.Extension (CountedBackend.named.build (symbolicBody c).start (symbolicBody c).stride (symbolicBody c).count
      (symbolicInitial c) (symbolicRefill c) (symbolicBody c).body b.nextArray qi qo b2).2 final) at kept
  change (let (qi,b1) := chooseInputQueue channels (symbolicMode c) b0;
    let (qo,b2) := chooseOutputQueue channels (symbolicBudget c) (symbolicOutput c) b1;
    WireAllocation.Extends (CountedBackend.named.build (symbolicBody c).start (symbolicBody c).stride (symbolicBody c).count
      (symbolicInitial c) (symbolicRefill c) (symbolicBody c).body b.nextArray qi qo b2).2 final) at wiresKept
  generalize ei : chooseInputQueue channels (symbolicMode c) b0 = pair at *
  obtain ⟨qi,b1⟩ := pair
  dsimp only at hi inputDeclared kept wiresKept ⊢
  have ho := ReferenceScope.Extension.chooseOutput channels (symbolicBudget c) (symbolicOutput c) b1
  have outputDeclared := outputQueue_declared (budget:=symbolicBudget c) (symbolicOutput c)
    (fun a ha => (outputMap a ha).extend (old.trans hi))
  generalize eo : chooseOutputQueue channels (symbolicBudget c) (symbolicOutput c) b1 = pair at *
  obtain ⟨qo,b2⟩ := pair
  dsimp only at ho outputDeclared kept wiresKept ⊢
  have bodyGrowth := ReferenceScope.Extension.named (symbolicBody c).start (symbolicBody c).stride (symbolicBody c).count
    (symbolicInitial c) (symbolicRefill c) (symbolicBody c).body b.nextArray qi qo b2
  have fromBody := bodyGrowth.trans kept
  have fromPrivate := (hi.trans ho).trans fromBody
  have all := old.trans fromPrivate
  have inputFinal : Queue final qi := inputDeclared.extend (ho.trans fromBody)
  have outputFinal : Queue final qo := outputDeclared.extend fromBody
  have privateFinal : Memory final b.nextArray := ⟨_,fromPrivate.memories privateMemory⟩
  have bodyRefs : (symbolicBody c).body.ArraysWithin (Memory final) := by
    rw [symbolicBody_body]
    apply (commandArrays_closed c.body).mpr
    intro a member
    exact ⟨sizes a,all.memories (sources a (by simp [member]))⟩
  exact symbolicSchedule_references _ c
    ⟨sizes (symbolicInput c),fromPrivate.memories privateMemory,all.memories (sources _ (by simp))⟩
    inputFinal outputFinal (fun a ha => ⟨sizes a,all.memories (sources a (by simp [ha]))⟩)
    (ChannelCounted.lower_references bodyRefs privateFinal inputFinal outputFinal
      (Nat.le_trans inputs all.wires) wiresKept)

private theorem symbolic_output_channel_member (member : c ∈ cs) (output : a ∈ (symbolicOutput c).toList) :
    a ∈ symbolicChannels cs := by
  apply List.mem_eraseDups.mpr
  exact List.mem_flatMap.mpr ⟨c,member,List.mem_append_left _ output⟩

private theorem input_channel_member (member : c ∈ cs) (mode : symbolicMode c = .channel a) :
    a ∈ symbolicChannels cs := by
  apply List.mem_eraseDups.mpr
  exact List.mem_flatMap.mpr ⟨c,member,by simp [mode]⟩

private theorem tail_channel_member (member : a ∈ symbolicChannels cs) : a ∈ symbolicChannels (c::cs) := by
  simpa only [symbolicChannels,List.mem_eraseDups,List.flatMap_cons,List.mem_append] using Or.inr member

theorem symbolicInstructions_references (cs : List HybridSymbolicGlobal.Instruction)
    (sources : ∀ a ∈ sourceArrays (.symbolic cs), (a,sizes a) ∈ b.memories.toList)
    (inputs : 2 ≤ b.wires.size)
    (mapping : ∀ a ∈ symbolicChannels cs, Queue b (channels a))
    (wiresKept : WireAllocation.Extends
      (symbolicInstructionsWith CountedBackend.named.build sizes channels cs b).2 final)
    (kept : ReferenceScope.Extension
      (symbolicInstructionsWith CountedBackend.named.build sizes channels cs b).2 final) :
    Control final (symbolicInstructionsWith CountedBackend.named.build sizes channels cs b).1 := by
  induction cs generalizing b with
  | nil => trivial
  | cons c cs ih =>
    let middle := (symbolicInstructionWith CountedBackend.named.build sizes channels c b).2
    have first := ReferenceScope.Extension.symbolicInstruction sizes channels c b
    have rest := ReferenceScope.Extension.symbolicInstructions sizes channels cs middle
    have restWires := WireAllocation.symbolicInstructions sizes channels cs middle
    apply And.intro
    · apply symbolicInstruction_references c
      · intro a member
        apply sources a
        simp only [sourceArrays,List.flatMap_cons,List.mem_append,symbolicBody_body]
        exact Or.inl (by simpa only [List.mem_append] using member)
      · exact inputs
      · intro a mode
        exact mapping a (input_channel_member (by simp) mode)
      · intro a member
        exact mapping a (symbolic_output_channel_member (by simp) member)
      · exact restWires.trans wiresKept
      · exact rest.trans kept
    · apply ih
      · intro a member
        apply first.memories
        apply sources a
        exact List.mem_append_right _ member
      · exact Nat.le_trans inputs first.wires
      · intro a member
        exact (mapping a (tail_channel_member member)).extend first
      · exact wiresKept
      · exact kept

/-- The whole symbolic schedule has declared references. The only premises
are source declaration coverage and uniqueness, not a target validation. -/
theorem symbolic_schedule_references (cs : List HybridSymbolicGlobal.Instruction)
    (layout : Array (Nat × Nat)) (unique : (layout.toList.map Prod.fst).Nodup)
    (covered : layoutCovers layout (.symbolic cs) = true) :
    let generated := scheduleWith CountedBackend.named.build layout (.symbolic cs)
    Control generated.build generated.schedule := by
  let sizes := fun a => ((layout.toList.find? (fun p => p.1 == a)).map Prod.snd).getD 0
  let initial : Build := {memories:=layout,nextArray:=layoutLimit layout}
  let allocated := allocateChannels (symbolicCapacity cs) (symbolicChannels cs) initial
  have growth := ReferenceScope.Extension.channels (symbolicCapacity cs) (symbolicChannels cs) initial
  have channels := allocateChannels_correct (symbolicCapacity cs) (symbolicChannels cs) initial
  apply symbolicInstructions_references cs (sizes:=sizes) (b:=allocated.2)
  · intro a member
    obtain ⟨n,hn⟩ := layoutCovers_sound covered a member
    have size : sizes a = n := by
      unfold sizes
      rw [Allocation.find_declared unique hn]
      rfl
    apply growth.memories
    simpa only [size] using hn
  · exact Nat.le_trans (by change 2 ≤ 2; decide) growth.wires
  · intro a member
    have selected : (a,channelLookup allocated.1 a) ∈ allocated.1 := by
      apply channelLookup_member
      rwa [channels.names]
    exact ⟨symbolicCapacity cs a,channels.requested _ selected⟩
  · exact .refl _
  · exact .refl _

end IRComparison.Circuit
