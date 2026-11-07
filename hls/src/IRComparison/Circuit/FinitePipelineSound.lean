import IRComparison.Circuit.WordPipelineSound
import IRComparison.Circuit.FiniteObservation

namespace IRComparison.Circuit

/-- End-to-end theorem for the current sequential backend: a successful
compiler result reaches the native BV32 source result in finite clock cycles,
using only fixed-size bitvector banks between cycles. The serializer is the
explicitly trusted boundary after this finite circuit representation. -/
theorem finite_pipeline_finishes (p : HybridWord.Plan outputs sizes ks)
    (compiled : compile layout (HybridUnifiedPipeline.lower p) = .ok checked)
    (outputsSafe : ∀ a ∈ outputs, a < layoutLimit layout)
    (outputPorts : ∀ a ∈ outputs, checked.artifact.storageShape.hasMemory a)
    (s : HybridWord.State) (x y : HybridWord.Word)
    (sized : PipelineShapes.Layout sizes s.encode)
    (ready : p.Ready (HybridWord.encode x) (HybridWord.encode y) s.encode)
    (fits : checked.artifact.InputFits s.encode) :
    let a := checked.artifact
    ∃ cycles, ((FiniteRuntime.run a.machine a.storageShape cycles
      (FiniteRuntime.pack a.storageShape (a.machine.start s.encode (HybridWord.encode x) (HybridWord.encode y)))).result s.encode).map
        (Option.map (PipelineUse.observe outputs)) =
      some ((HybridWord.source x y ks s).map (fun t => PipelineUse.observe outputs t.encode)) := by
  obtain ⟨cycles,result,hr,ho⟩ := word_pipeline_finishes p compiled outputsSafe s x y sized ready
  have observed := finite_observation checked.storage checked.valid checked.inputs s x y fits outputPorts cycles
  rw [checked.execution] at hr
  rw [hr,Option.map_some,ho] at observed
  exact ⟨cycles,observed⟩

end IRComparison.Circuit
