import IRComparison.Circuit.ChannelWordRanges
import IRComparison.Circuit.PolicyProperties

namespace IRComparison.Circuit
open HybridIR HybridSymbolicGlobal CommandWordRanges

private theorem symbolicSchedule_words (a : InstructionLayout) (c : HybridSymbolicGlobal.Instruction)
    (body : DataWords final a.body) : DataWords final (symbolicSchedule a c) := by
  cases c <;> simpa [symbolicSchedule,symbolicMode,symbolicOutput,DataWords,ActionWords] using body

theorem symbolicInstruction_dataWords (c : HybridSymbolicGlobal.Instruction)
    (typed : WordCommand (fun _ => True) c.body)
    (ctx : CommandWordRanges.Context b [] (fun _ => True))
    (kept : WireAllocation.Extends
      (symbolicInstructionWith CountedBackend.named.build sizes channels c b).2 final) :
    DataWords final (symbolicInstructionWith CountedBackend.named.build sizes channels c b).1 := by
  let b0 := b.allocateSnapshot (symbolicInput c) sizes
  have ctx0 : CommandWordRanges.Context b0 [] (fun _ => True) :=
    ctx.extend ⟨[],by simp [b0,Build.allocateSnapshot]⟩
  have hi := WireAllocation.chooseInput channels (symbolicMode c) b0
  change (let (qi,b1) := chooseInputQueue channels (symbolicMode c) b0;
    let (qo,b2) := chooseOutputQueue channels (symbolicBudget c) (symbolicOutput c) b1;
    let (body,_) := CountedBackend.named.build (symbolicBody c).start (symbolicBody c).stride (symbolicBody c).count
      (symbolicInitial c) (symbolicRefill c) (symbolicBody c).body b.nextArray qi qo b2;
    DataWords final (symbolicSchedule ⟨b.nextArray,qi,qo,body⟩ c))
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
  exact symbolicSchedule_words _ c (ChannelCounted.lower_dataWords typeBody ((ctx0.extend hi).extend ho) kept)

theorem symbolicInstructions_dataWords (cs : List HybridSymbolicGlobal.Instruction)
    (typed : ∀ c ∈ cs, WordCommand (fun _ => True) c.body)
    (ctx : CommandWordRanges.Context b [] (fun _ => True))
    (kept : WireAllocation.Extends
      (symbolicInstructionsWith CountedBackend.named.build sizes channels cs b).2 final) :
    DataWords final (symbolicInstructionsWith CountedBackend.named.build sizes channels cs b).1 := by
  induction cs generalizing b with
  | nil => trivial
  | cons c cs ih =>
    let middle := (symbolicInstructionWith CountedBackend.named.build sizes channels c b).2
    have first := WireAllocation.symbolicInstruction sizes channels c b
    have rest := WireAllocation.symbolicInstructions sizes channels cs middle
    exact ⟨symbolicInstruction_dataWords c (typed c (by simp)) ctx (rest.trans kept),
      ih (fun c member => typed c (by simp [member])) (ctx.extend first) kept⟩

theorem symbolic_schedule_dataWords (cs : List HybridSymbolicGlobal.Instruction)
    (typed : ∀ c ∈ cs, WordCommand (fun _ => True) c.body) (layout : Array (Nat × Nat)) :
    let generated := scheduleWith CountedBackend.named.build layout (.symbolic cs)
    DataWords generated.build generated.schedule := by
  let initial : Build := {memories:=layout,nextArray:=layoutLimit layout}
  have ctx : CommandWordRanges.Context initial [] (fun _ => True) := {
    inputs := by change 2 ≤ 2; decide
    left := rfl
    right := rfl
    scopedSlots := by simp
    words := fun _ _ => by simp [lookup,WordRanges.Word,range,wrapped?,isWord] }
  have extended := ctx.extend (WireAllocation.channels (symbolicCapacity cs) (symbolicChannels cs) initial)
  exact symbolicInstructions_dataWords cs typed extended (.refl _)

/-- Word source → memory optimization (including inserted buffers and FIFOs)
→ actual scheduled actions. No word-width check is assumed at any stage. -/
theorem compile_schedule_dataWords (outputs : List Nat) (sizes : Nat → Nat)
    (ks : List HybridWord.Kernel) (layout : Array (Nat × Nat)) :
    ∃ p, HybridWord.compileProgram outputs sizes ks = some p ∧
      let generated := scheduleWith CountedBackend.named.build layout (HybridUnifiedPipeline.lower p)
      DataWords generated.build generated.schedule := by
  obtain ⟨program,hp⟩ := symbolic_compile_total outputs sizes
    (HybridUnifiedPipeline.compactStages (ks.map HybridWord.Kernel.lower))
  refine ⟨.symbolic program,?_,?_⟩
  · simp [HybridWord.compileProgram,HybridUnifiedPipeline.compile,hp]
  · exact symbolic_schedule_dataWords program.plan.code (program.plan.word (word_compactStages ks)) layout

end IRComparison.Circuit
