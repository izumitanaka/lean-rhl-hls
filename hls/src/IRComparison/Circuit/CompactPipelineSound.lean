import IRComparison.Circuit.RootSound
import IRComparison.Circuit.LayoutScope

namespace IRComparison.Circuit

/-- Complete compact control-IR → allocated clock-machine connection. It
includes private snapshots, all FIFO stages, finite capacities, and assembler
layout. The finite-storage representation theorem is a separate layer. -/
theorem compact_pipeline_finishes (layout : Array (Nat × Nat)) (code : HybridCompactChainControl.RootCode)
    (covered : layoutCovers layout (.compact code) = true)
    (known : hasSendBounds (.compact code) = true)
    (outputsSafe : ∀ a ∈ outputs, a < layoutLimit layout) (s : State) (x y : Int) :
    let machine := (lower layout (.compact code)).machine
    ∃ cycles result, (machine.run cycles (machine.start s x y)).result = some result ∧
      result.map (PipelineUse.observe outputs) = (code.eval x y s).map (PipelineUse.observe outputs) := by
  let sizes := fun a => ((layout.toList.find? (fun p => p.1 == a)).map Prod.snd).getD 0
  let b : Build := { memories := layout, nextArray := layoutLimit layout }
  let p : Payload := ⟨s,(fun n => if n = 0 then x else if n = 1 then y else 0),fun _ => []⟩
  have initialQueues : QueueWellFormed b := ⟨by simp [b],by simp [b]⟩
  have finalQueues := rootCode_queues sizes code b initialQueues
  have senderSafe : ∀ a ∈ allCommandArrays code.sender.body, a < b.nextArray := by
    intro a ha
    exact source_layout_bound covered (by simp [sourceArrays,ha])
  have tailSafe : ∀ a ∈ tailArrays code.tail, a < b.nextArray := by
    intro a ha
    exact source_layout_bound covered (by simp [sourceArrays,ha])
  obtain ⟨r,hr,ho⟩ := rootCode_correct (x:=x) (y:=y) sizes code b p (by change 2 ≤ 2; omega) known
    (finalQueues.covers (rootCode sizes code b).1) senderSafe tailSafe rfl (by simp [p])
  obtain ⟨cycles,hcycles⟩ := Schedule.assemble_finishes _ p hr
  refine ⟨cycles,r.map Payload.data,?_,?_⟩
  · exact hcycles
  · have projected := congrArg (Option.map (PipelineUse.observe outputs)) ho
    simpa only [Option.map_map,Function.comp_def,b,p,observe_trim outputsSafe] using projected

/-- Compose the backend theorem with the existing memory-optimization theorem
for any typed plan that selects the compact route. -/
theorem unified_compact_finishes (p : HybridUnifiedPipeline.Plan outputs sizes ks)
    (route : HybridUnifiedPipeline.lower p = .compact code) (layout : Array (Nat × Nat))
    (covered : layoutCovers layout (.compact code) = true) (known : hasSendBounds (.compact code) = true)
    (outputsSafe : ∀ a ∈ outputs, a < layoutLimit layout) (s : State) (x y : Int)
    (sized : PipelineShapes.Layout sizes s) (ready : p.Ready x y s) :
    let machine := (lower layout (.compact code)).machine
    ∃ cycles result, (machine.run cycles (machine.start s x y)).result = some result ∧
      result.map (PipelineUse.observe outputs) = (HybridIR.source x y ks s).map (PipelineUse.observe outputs) := by
  have same : code.eval x y s = p.eval x y s := by
    cases p with
    | expanded p => cases route
    | compact p =>
      cases route
      exact HybridCompactChainControl.lowerRoot_correct p
  obtain ⟨cycles,result,hcycles,ho⟩ := compact_pipeline_finishes layout code covered known outputsSafe s x y
  exact ⟨cycles,result,hcycles,ho.trans ((congrArg (Option.map (PipelineUse.observe outputs)) same).trans (p.correct s sized ready))⟩

end IRComparison.Circuit
