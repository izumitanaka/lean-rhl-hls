import IRComparison.Circuit.SharedPipelineSound
import IRComparison.Circuit.SharedGraphRun
import IRComparison.Circuit.Pipelining.StructuredCompiler

namespace IRComparison.Circuit.Shared
open Pipelining SystemVerilog

structure StructuredCircuit where
  tree : ClockTree Program
  graph : ClockGraph Program
  artifact : Artifact
  module : ModuleCode

def structuredTree (s : Schedule Program) : ClockTree Program :=
  overlapLoops (scheduleStructure earliestProposal s)

def compileStructured (p : HybridWord.Plan outputs sizes ks) (layout : Array (Nat × Nat)) :
    Except String StructuredCircuit := do
  let source := HybridUnifiedPipeline.lower p
  checkLayout layout source
  checkSendBudgets source
  checkCommunication source
  let generated := pipeline layout source
  let tree := structuredTree generated.schedule
  let graph := tree.assemble generated.build.queues
  let artifact := artifact graph generated.build.wires generated.build.memories layout
  let code ← generateGraphModule artifact graph outputs
  return ⟨tree,graph,artifact,code⟩

structure StructuredFacts (p : HybridWord.Plan outputs sizes ks) (layout : Array (Nat × Nat))
    (built : StructuredCircuit) : Prop where
  covered : layoutCovers layout (HybridUnifiedPipeline.lower p) = true
  known : hasSendBounds (HybridUnifiedPipeline.lower p) = true
  communication : checkCommunication (HybridUnifiedPipeline.lower p) = .ok ()
  graph : built.graph = (structuredTree (pipeline layout (HybridUnifiedPipeline.lower p)).schedule).assemble
    (pipeline layout (HybridUnifiedPipeline.lower p)).build.queues
  generated : generateGraphModule built.artifact built.graph outputs = .ok built.module

theorem compileStructured_facts (h : compileStructured p layout = .ok built) : StructuredFacts p layout built := by
  cases hl : checkLayout layout (HybridUnifiedPipeline.lower p) <;> simp [compileStructured,hl,bind,Except.bind] at h
  cases hs : checkSendBudgets (HybridUnifiedPipeline.lower p) <;> simp [hs] at h
  cases hc : checkCommunication (HybridUnifiedPipeline.lower p) <;> simp [hc] at h
  rename_i u v w
  cases u; cases v; cases w
  split at h
  · contradiction
  · cases h
    exact ⟨checkLayout_covered hl,checkSendBudgets_sound hs,hc,rfl,by assumption⟩


/-- Source-wide preservation through the actual shared compiler and printed
RTL. Input layout/readiness are the existing memory-plan contract. -/
theorem compileStructured_correct {p : HybridWord.Plan outputs sizes ks}
    (success : compileStructured p layout = .ok built)
    (outputsSafe : ∀ a ∈ outputs, a < layoutLimit layout)
    (s : HybridWord.State) (x y : HybridWord.Word)
    (sized : PipelineShapes.Layout sizes s.encode) (ready : p.Ready (HybridWord.encode x) (HybridWord.encode y) s.encode)
    (fits : built.artifact.InputFits s.encode)
    (r : RTL.InterfaceState built.artifact.storageShape) (running : r.Running)
    (same : StorageAgreement built.artifact.storageShape r.core.decode ((wordPayload s x y).at 1)) :
    ∃ cycles result, (Concrete.parseModule built.module.text).bind (fun parsed =>
      parsed.run built.artifact.storageShape cycles r) = some result ∧
      PublicObservation built.artifact.storageShape outputs result.core.decode
        ((HybridWord.source x y ks s).map HybridWord.State.encode) := by
  have facts := compileStructured_facts success
  obtain ⟨table,checks,_⟩ := generateGraphModule_components facts.generated
  obtain ⟨result,he,ho⟩ := optimized_schedule_correct_with CountedBackend.named p layout facts.covered facts.known facts.communication
    outputsSafe s x y sized ready
  have relation := pipeline_related layout (HybridUnifiedPipeline.lower p)
  have queues := congrArg (fun x => x.2.1) relation.2.resources
  change (Circuit.scheduleWith CountedBackend.named.build layout (HybridUnifiedPipeline.lower p)).build.queues =
    (pipeline layout (HybridUnifiedPipeline.lower p)).build.queues at queues
  have executed := relation.1 _ _ _ he
  have cap : ((Circuit.scheduleWith CountedBackend.named.build layout (HybridUnifiedPipeline.lower p)).schedule.assemble
      (Circuit.scheduleWith CountedBackend.named.build layout (HybridUnifiedPipeline.lower p)).build.queues).capacity =
      capacityOf (pipeline layout (HybridUnifiedPipeline.lower p)).build.queues := by
    change capacityOf _ = capacityOf _
    rw [queues]
    rfl
  rw [cap] at executed
  obtain ⟨cycles,finished⟩ := ClockTree.assemble_finishes (overlapLoops_correct (scheduleStructure_correct executed earliestProposal))
  have finished' : (built.graph.run cycles ((wordPayload s x y).at 1)).result = some (result.map Payload.data) := by
    rw [facts.graph]; exact finished
  have numeric := word_initial_bound checks.initial s x y
  have initial : ClockBound built.artifact built.graph table ((wordPayload s x y).at 1) :=
    ⟨⟨numeric.data,numeric.wires,numeric.queues⟩,⟨fits,by intro q; simp [wordPayload,Payload.at,Runtime.payload]⟩,checks.entry,clock_initial_table checks.invariant (by
      have h := checks.initial
      simp only [initialWidthsSafe,Bool.and_eq_true,decide_eq_true_eq] at h
      simpa using h.1) s x y⟩
  obtain ⟨physical,executed,agrees,_⟩ := generated_text_run facts.generated checks initial r running same cycles
  refine ⟨cycles,physical,executed,public_observation agrees ?_⟩
  rw [finished']
  simpa only [Option.map_some,Option.map_map,Function.comp_def] using congrArg some ho

end IRComparison.Circuit.Shared
