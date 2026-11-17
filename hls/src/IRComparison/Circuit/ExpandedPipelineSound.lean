import IRComparison.Circuit.ChannelsAllocation
import IRComparison.Circuit.LayoutScope
import IRComparison.Circuit.BudgetCheck
import IRComparison.Circuit.CompactPipelineSound
import IRComparison.Circuit.RegionsSound
import IRComparison.Circuit.SymbolicPipelineSound
namespace IRComparison.Circuit

theorem outputBudget_fold (cs : List HybridIR.Instruction) (a base : Nat) :
    let total := cs.foldl (fun n c => if c.output = some a then max n ((blocksBudget c.blocks).getD 0) else n) base
    base ≤ total ∧ ∀ c ∈ cs, c.output = some a → (blocksBudget c.blocks).getD 0 ≤ total := by
  induction cs generalizing base with
  | nil => exact ⟨Nat.le_refl _,by simp⟩
  | cons c cs ih =>
    dsimp only [List.foldl_cons]
    split
    next hc =>
      have hh := ih (max base ((blocksBudget c.blocks).getD 0))
      refine ⟨Nat.le_trans (Nat.le_max_left _ _) hh.1,?_⟩
      intro d hd he
      rcases List.mem_cons.mp hd with rfl | ht
      · exact Nat.le_trans (Nat.le_max_right _ _) hh.1
      · exact hh.2 d ht he
    next hc =>
      have hh := ih base
      refine ⟨hh.1,?_⟩
      intro d hd he
      rcases List.mem_cons.mp hd with rfl | ht
      · exact False.elim (hc he)
      · exact hh.2 d ht he

theorem outputBudget_member (hc : c ∈ cs) (ha : a ∈ c.output.toList) :
    (blocksBudget c.blocks).getD 0 ≤ outputBudget cs a := by
  apply (outputBudget_fold cs a 0).2 c hc
  cases ho : c.output <;> simp_all

theorem output_channel_member (hc : c ∈ cs) (ha : a ∈ c.output.toList) : a ∈ channelIds cs := by
  simp only [channelIds,List.mem_eraseDups,List.mem_filterMap]
  refine ⟨c,hc,?_⟩
  cases ho : c.output <;> simp_all

theorem expanded_layout_scoped (covered : layoutCovers layout (.expanded cs) = true)
    (communication : checkCommunication (.expanded cs) = .ok ()) :
    InstructionsScoped (channelIds cs) (layoutLimit layout) cs := by
  have member : ∀ c ∈ cs, ∀ a ∈ (c.input :: c.output.toList ++
        (match c.mode with | .channel a => [a] | .memory a _ _ => [a]) ++
        c.blocks.flatMap (fun b => allCommandArrays b.body)), a < layoutLimit layout := by
    intro c hc a ha
    apply source_layout_bound covered
    exact List.mem_flatMap.mpr ⟨c,hc,ha⟩
  refine ⟨communication_checked communication,fun c hc a ha => output_channel_member hc ha,?_,?_⟩
  · intro c hc
    refine ⟨member c hc c.input (by simp),?_,?_⟩
    · cases hm : c.mode with
      | channel a => exact member c hc a (by simp [hm])
      | memory a order fifo => exact member c hc a (by simp [hm])
    · intro block hb a ha
      exact member c hc a (by simp only [List.mem_cons,List.mem_append]; exact Or.inr (List.mem_flatMap.mpr ⟨block,hb,ha⟩))
  · intro c hc a ha
    exact member c hc a (by simp [ha])

end IRComparison.Circuit

namespace IRComparison.Circuit

/-- Expanded control code, including interleaved memory and channel stages,
refines the allocated clock machine for every execution of accepted code. -/
theorem expanded_pipeline_schedule (layout : Array (Nat × Nat)) (cs : List HybridIR.Instruction)
    (covered : layoutCovers layout (.expanded cs) = true)
    (known : hasSendBounds (.expanded cs) = true)
    (communication : checkCommunication (.expanded cs) = .ok ())
    (outputsSafe : ∀ a ∈ outputs, a < layoutLimit layout) (s : State) (x y : Int) :
    let machine := (lower layout (.expanded cs)).machine
    ∃ result, (schedule layout (.expanded cs)).schedule.Eval machine.capacity
      ⟨s,(fun n => if n = 0 then x else if n = 1 then y else 0),fun _ => []⟩ result ∧
      result.map (fun p => PipelineUse.observe outputs p.data) =
        (HybridIR.execute x y cs s (fun _ => [])).map (PipelineUse.observe outputs) := by
  let sizes := fun a => ((layout.toList.find? (fun p => p.1 == a)).map Prod.snd).getD 0
  let requested := fun a => max (sizes a) (outputBudget cs a)
  let b : Build := { memories := layout, nextArray := layoutLimit layout }
  let allocated := allocateChannels requested (channelIds cs) b
  let mapping := channelLookup allocated.1
  let generated := instructions sizes mapping cs allocated.2
  let machine := generated.1.assemble generated.2.queues
  let p : Payload := ⟨s,(fun n => if n = 0 then x else if n = 1 then y else 0),fun _ => []⟩
  have initialQueues : QueueWellFormed b := ⟨by simp [b],by simp [b]⟩
  have afterAllocation := allocateChannels_queues requested (channelIds cs) b initialQueues
  have finalQueues := instructions_queues sizes mapping cs allocated.2 afterAllocation
  have table := finalQueues.covers generated.1
  have allocation := allocateChannels_correct requested (channelIds cs) b
  have allocatedTable := table.before (instructions_extension sizes mapping cs allocated.2)
  have sourceScope := expanded_layout_scoped covered communication
  have capacity : InstructionsCapacity mapping machine.capacity cs := by
    intro c hc
    obtain ⟨budget,hbudget⟩ := expandedSendBounds known c hc
    refine ⟨budget,hbudget,?_⟩
    intro a ha
    have bound := outputBudget_member hc ha
    rw [hbudget,Option.getD_some] at bound
    exact Nat.le_trans bound (Nat.le_trans (Nat.le_max_right _ _) (allocation.capacity allocatedTable (output_channel_member hc ha)))
  obtain ⟨r,hr,ho⟩ := instructions_correct (x:=x) (y:=y) sizes mapping cs allocated.2
    (by rw [allocation.wires]; change 2 ≤ 2; omega)
    (by rw [allocation.arrays]; exact Nat.le_refl _) allocation.channels sourceScope capacity table p rfl (by simp [p])
  refine ⟨r,hr,?_⟩
  have projected := congrArg (Option.map (PipelineUse.observe outputs)) ho
  have empty : channelView (channelIds cs) mapping p.queues = fun _ => [] := by
    funext a; simp [channelView,p]
  rw [empty,← execute_trim cs sourceScope.arrays] at projected
  simpa only [Option.map_map,Function.comp_def,p,observe_trim outputsSafe] using projected

theorem expanded_pipeline_finishes (layout : Array (Nat × Nat)) (cs : List HybridIR.Instruction)
    (covered : layoutCovers layout (.expanded cs) = true)
    (known : hasSendBounds (.expanded cs) = true)
    (communication : checkCommunication (.expanded cs) = .ok ())
    (outputsSafe : ∀ a ∈ outputs, a < layoutLimit layout) (s : State) (x y : Int) :
    let machine := (lower layout (.expanded cs)).machine
    ∃ cycles result, (machine.run cycles (machine.start s x y)).result = some result ∧
      result.map (PipelineUse.observe outputs) =
        (HybridIR.execute x y cs s (fun _ => [])).map (PipelineUse.observe outputs) := by
  obtain ⟨result,he,ho⟩ := expanded_pipeline_schedule layout cs covered known communication outputsSafe s x y
  obtain ⟨cycles,hc⟩ := Schedule.assemble_finishes _ _ he
  exact ⟨cycles,result.map Payload.data,hc,by simpa only [Option.map_map,Function.comp_def] using ho⟩

/-- Both allocation routes compose with the verified memory-optimization plan.
The remaining serialization trust boundary is not part of this statement. -/
theorem unified_pipeline_finishes (p : HybridUnifiedPipeline.Plan outputs sizes ks)
    (layout : Array (Nat × Nat))
    (covered : layoutCovers layout (HybridUnifiedPipeline.lower p) = true)
    (known : hasSendBounds (HybridUnifiedPipeline.lower p) = true)
    (communication : checkCommunication (HybridUnifiedPipeline.lower p) = .ok ())
    (outputsSafe : ∀ a ∈ outputs, a < layoutLimit layout) (s : State) (x y : Int)
    (sized : PipelineShapes.Layout sizes s) (ready : p.Ready x y s) :
    let machine := (lower layout (HybridUnifiedPipeline.lower p)).machine
    ∃ cycles result, (machine.run cycles (machine.start s x y)).result = some result ∧
      result.map (PipelineUse.observe outputs) = (HybridIR.source x y ks s).map (PipelineUse.observe outputs) := by
  cases p with
  | symbolic program =>
    obtain ⟨r,he,ho⟩ := symbolic_pipeline_schedule layout program.plan.code covered known communication outputsSafe s x y
    obtain ⟨cycles,hc⟩ := Schedule.assemble_finishes _ _ he
    refine ⟨cycles,r.map Payload.data,hc,?_⟩
    have connected := ho.trans ((HybridUnifiedPipeline.Plan.symbolic program).correct s sized ready)
    simpa only [Option.map_map,Function.comp_def] using connected
  | regions =>
    obtain ⟨r,he,ho⟩ := regions_pipeline_schedule layout _ covered outputsSafe s x y
    obtain ⟨cycles,hc⟩ := Schedule.assemble_finishes _ _ he
    refine ⟨cycles,r.map Payload.data,hc,?_⟩
    have connected := ho.trans ((HybridUnifiedPipeline.Plan.regions (ks:=ks) (sizes:=sizes)).correct s sized ready)
    simpa only [Option.map_map,Function.comp_def] using connected
  | expanded program =>
    obtain ⟨cycles,result,hcycles,ho⟩ := expanded_pipeline_finishes layout program.code covered known communication outputsSafe s x y
    refine ⟨cycles,result,hcycles,ho.trans ?_⟩
    exact (HybridUnifiedPipeline.Plan.expanded program).correct s sized ready
  | compact program =>
    exact unified_compact_finishes (.compact program) rfl layout covered known outputsSafe s x y sized ready

end IRComparison.Circuit
