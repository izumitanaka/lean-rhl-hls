import IRComparison.Circuit.ChannelRanges
import IRComparison.Circuit.Pipelining.InitialWidths
import IRComparison.Circuit.ReferenceProperties

namespace IRComparison.Circuit
open HybridIR HybridSymbolicGlobal CommandWordRanges

private theorem symbolicSchedule_ranges {final : Build} (a : InstructionLayout) (c : HybridSymbolicGlobal.Instruction)
    (body : RangeSafe final.wires.toList a.body) : RangeSafe final.wires.toList (symbolicSchedule a c) := by
  cases c <;> dsimp only [symbolicSchedule,symbolicMode,symbolicOutput]
  all_goals repeat' first | exact body | exact RangeSafe.skip | apply RangeSafe.seq | exact RangeSafe.data trivial

theorem symbolicInstruction_ranges (c : HybridSymbolicGlobal.Instruction)
    (typed : WordCommand (fun _ => True) c.body)
    (ctx : CommandWordRanges.Context b [] (fun _ => True))
    (kept : WireAllocation.Extends
      (symbolicInstructionWith CountedBackend.named.build sizes channels c b).2 final) :
    RangeSafe final.wires.toList (symbolicInstructionWith CountedBackend.named.build sizes channels c b).1 := by
  let b0 := b.allocateSnapshot (symbolicInput c) sizes
  have ctx0 : CommandWordRanges.Context b0 [] (fun _ => True) :=
    ctx.extend ⟨[],by simp [b0,Build.allocateSnapshot]⟩
  have hi := WireAllocation.chooseInput channels (symbolicMode c) b0
  change (let (qi,b1) := chooseInputQueue channels (symbolicMode c) b0;
    let (qo,b2) := chooseOutputQueue channels (symbolicBudget c) (symbolicOutput c) b1;
    let (body,_) := CountedBackend.named.build (symbolicBody c).start (symbolicBody c).stride (symbolicBody c).count
      (symbolicInitial c) (symbolicRefill c) (symbolicBody c).body b.nextArray qi qo b2;
    RangeSafe final.wires.toList (symbolicSchedule ⟨b.nextArray,qi,qo,body⟩ c))
  change (let (qi,b1) := chooseInputQueue channels (symbolicMode c) b0;
    let (qo,b2) := chooseOutputQueue channels (symbolicBudget c) (symbolicOutput c) b1;
    WireAllocation.Extends (CountedBackend.named.build (symbolicBody c).start (symbolicBody c).stride (symbolicBody c).count
      (symbolicInitial c) (symbolicRefill c) (symbolicBody c).body b.nextArray qi qo b2).2 final) at kept
  generalize ei : chooseInputQueue channels (symbolicMode c) b0 = pair at *
  obtain ⟨qi,b1⟩ := pair
  dsimp only at hi kept ⊢
  have ho := WireAllocation.chooseOutput channels (symbolicBudget c) (symbolicOutput c) b1
  generalize eo : chooseOutputQueue channels (symbolicBudget c) (symbolicOutput c) b1 = pair at *
  obtain ⟨qo,b2⟩ := pair
  dsimp only at ho kept ⊢
  have typeBody : WordCommand (fun _ => True) (symbolicBody c).body := by
    simpa only [symbolicBody_body] using typed
  exact symbolicSchedule_ranges _ c (ChannelCounted.lower_ranges typeBody ((ctx0.extend hi).extend ho) kept)

theorem symbolicInstructions_ranges (cs : List HybridSymbolicGlobal.Instruction)
    (typed : ∀ c ∈ cs, WordCommand (fun _ => True) c.body)
    (ctx : CommandWordRanges.Context b [] (fun _ => True))
    (kept : WireAllocation.Extends
      (symbolicInstructionsWith CountedBackend.named.build sizes channels cs b).2 final) :
    RangeSafe final.wires.toList (symbolicInstructionsWith CountedBackend.named.build sizes channels cs b).1 := by
  induction cs generalizing b with
  | nil => exact RangeSafe.skip
  | cons c cs ih =>
    let middle := (symbolicInstructionWith CountedBackend.named.build sizes channels c b).2
    have first := WireAllocation.symbolicInstruction sizes channels c b
    have rest := WireAllocation.symbolicInstructions sizes channels cs middle
    exact RangeSafe.seq (symbolicInstruction_ranges c (typed c (by simp)) ctx (rest.trans kept))
      (ih (fun c member => typed c (by simp [member])) (ctx.extend first) kept)

theorem symbolic_schedule_ranges (cs : List HybridSymbolicGlobal.Instruction)
    (typed : ∀ c ∈ cs, WordCommand (fun _ => True) c.body) (layout : Array (Nat × Nat)) :
    let generated := scheduleWith CountedBackend.named.build layout (.symbolic cs)
    RangeSafe generated.build.wires.toList generated.schedule := by
  let initial : Build := {memories:=layout,nextArray:=layoutLimit layout}
  have ctx : CommandWordRanges.Context initial [] (fun _ => True) := {
    inputs := by change 2 ≤ 2; decide
    left := rfl
    right := rfl
    scopedSlots := by simp
    words := fun _ _ => by simp [lookup,WordRanges.Word,range,wrapped?,isWord] }
  have extended := ctx.extend (WireAllocation.channels (symbolicCapacity cs) (symbolicChannels cs) initial)
  exact symbolicInstructions_ranges cs typed extended (.refl _)

/-- Word source → memory optimization → named buffer/FIFO lowering.
The resulting structural range derivation does not assume inference success. -/
theorem compile_schedule_ranges (outputs : List Nat) (sizes : Nat → Nat)
    (ks : List HybridWord.Kernel) (layout : Array (Nat × Nat)) :
    ∃ p, HybridWord.compileProgram outputs sizes ks = some p ∧
      let generated := scheduleWith CountedBackend.named.build layout (HybridUnifiedPipeline.lower p)
      RangeSafe generated.build.wires.toList generated.schedule := by
  obtain ⟨program,hp⟩ := symbolic_compile_total outputs sizes
    (HybridUnifiedPipeline.compactStages (ks.map HybridWord.Kernel.lower))
  refine ⟨.symbolic program,?_,?_⟩
  · simp [HybridWord.compileProgram,HybridUnifiedPipeline.compile,hp]
  · exact symbolic_schedule_ranges program.plan.code (program.plan.word (word_compactStages ks)) layout

/-- The real memory compiler and rolled named lowering always reach a
successful interval analysis for arbitrary word kernels. Search, buffers,
communication and graph cycles are included; no checker-success assumption
or concrete source execution is required. -/
theorem compile_schedule_inference (outputs : List Nat) (sizes : Nat → Nat)
    (ks : List HybridWord.Kernel) (layout : Array (Nat × Nat)) :
    ∃ p table, HybridWord.compileProgram outputs sizes ks = some p ∧
      let generated := scheduleWith CountedBackend.named.build layout (HybridUnifiedPipeline.lower p)
      let a : Artifact := ⟨generated.schedule.assemble generated.build.queues,
        generated.build.wires,generated.build.memories,layout⟩
      inferInvariant a = .ok table ∧ validInvariant a table = true := by
  obtain ⟨p,compiled,ranges⟩ := compile_schedule_ranges outputs sizes ks layout
  let generated := scheduleWith CountedBackend.named.build layout (HybridUnifiedPipeline.lower p)
  let a : Artifact := ⟨generated.schedule.assemble generated.build.queues,
    generated.build.wires,generated.build.memories,layout⟩
  have initial := Pipelining.InitialWidths.scheduled_check layout (HybridUnifiedPipeline.lower p)
  have fits : (initialFrame a).within a.wires.toList = true := by
    simp only [Pipelining.initialWidthsSafe,Bool.and_eq_true] at initial
    simpa [Pipelining.initialWidthFrame,initialFrame,a] using initial.2
  obtain ⟨table,inferred,valid⟩ := ranges.inferInvariant (a:=a) rfl fits trivial
  exact ⟨p,table,compiled,inferred,valid⟩

/-- Layout, memory-policy and numerical checks agree on the SAME actual
optimization result. A failed optimized candidate is never replaced in this
proof by a different memory plan. Storage references and printing remain the
next obligations of the full HLS success theorem. -/
theorem compile_rolled_checks (outputs : List Nat) (sizes : Nat → Nat)
    (ks : List HybridWord.Kernel) (layout : Array (Nat × Nat))
    (unique : (layout.toList.map Prod.fst).Nodup)
    (sourceClosed : ∀ k ∈ ks, (∃ n, (k.array,n) ∈ layout.toList) ∧
      k.body.lower.target.ArraysWithin (fun a => ∃ n, (a,n) ∈ layout.toList)) :
    ∃ p table, HybridWord.compileProgram outputs sizes ks = some p ∧
      checkLayout layout (HybridUnifiedPipeline.lower p) = .ok () ∧
      checkSendBudgets (HybridUnifiedPipeline.lower p) = .ok () ∧
      checkCommunication (HybridUnifiedPipeline.lower p) = .ok () ∧
      inferInvariant (lowerWith CountedBackend.named.build layout (HybridUnifiedPipeline.lower p)) = .ok table ∧
      validInvariant (lowerWith CountedBackend.named.build layout (HybridUnifiedPipeline.lower p)) table = true := by
  obtain ⟨p,table,compiled,inferred,valid⟩ := compile_schedule_inference outputs sizes ks layout
  obtain ⟨q,hq,layoutChecked⟩ := compile_layout outputs sizes ks layout unique sourceClosed
  have eqp := Option.some.inj (hq.symm.trans compiled)
  subst q
  obtain ⟨q,hq,budget,communication⟩ := compile_memory_checks outputs sizes (ks.map HybridWord.Kernel.lower)
  have eqp := Option.some.inj (hq.symm.trans compiled)
  subst q
  exact ⟨p,table,compiled,layoutChecked,budget,communication,inferred,valid⟩

end IRComparison.Circuit
