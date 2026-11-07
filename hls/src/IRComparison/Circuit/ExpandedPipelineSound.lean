import IRComparison.Circuit.ExpandedLayout
import IRComparison.Circuit.CompactPipelineSound

namespace IRComparison.Circuit

/-- Expanded control code, including interleaved memory and channel stages,
refines the allocated clock machine for every execution of accepted code. -/
theorem expanded_pipeline_finishes (layout : Array (Nat × Nat)) (cs : List HybridIR.Instruction)
    (covered : layoutCovers layout (.expanded cs) = true)
    (known : hasSendBounds (.expanded cs) = true)
    (communication : checkCommunication (.expanded cs) = .ok ())
    (outputsSafe : ∀ a ∈ outputs, a < layoutLimit layout) (s : State) (x y : Int) :
    let machine := (lower layout (.expanded cs)).machine
    ∃ cycles result, (machine.run cycles (machine.start s x y)).result = some result ∧
      result.map (PipelineUse.observe outputs) =
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
  obtain ⟨cycles,hcycles⟩ := Schedule.assemble_finishes generated.1 p hr
  refine ⟨cycles,r.map Payload.data,hcycles,?_⟩
  have projected := congrArg (Option.map (PipelineUse.observe outputs)) ho
  have empty : channelView (channelIds cs) mapping p.queues = fun _ => [] := by
    funext a; simp [channelView,p]
  rw [empty,← execute_trim cs sourceScope.arrays] at projected
  simpa only [Option.map_map,Function.comp_def,p,observe_trim outputsSafe] using projected

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
  | expanded program =>
    obtain ⟨cycles,result,hcycles,ho⟩ := expanded_pipeline_finishes layout program.code covered known communication outputsSafe s x y
    refine ⟨cycles,result,hcycles,ho.trans ?_⟩
    exact (HybridUnifiedPipeline.Plan.expanded program).correct s sized ready
  | compact program =>
    exact unified_compact_finishes (.compact program) rfl layout covered known outputsSafe s x y sized ready

end IRComparison.Circuit
