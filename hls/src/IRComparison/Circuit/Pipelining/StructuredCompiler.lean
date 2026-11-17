import IRComparison.Circuit.Pipelining.StructuredStorage
import IRComparison.Circuit.Pipelining.GenerationTotal
import IRComparison.Circuit.Pipelining.Rolled
import IRComparison.Circuit.AllocationLayout
import IRComparison.Circuit.Pipelining.Construction
import IRComparison.Circuit.CommandWordRanges
import IRComparison.Circuit.CounterRanges
import IRComparison.Circuit.PipelineWordRanges
import IRComparison.Circuit.PipelineRanges

namespace IRComparison.Circuit.Pipelining
open SystemVerilog

theorem generated_graph_run (generated : generateGraphModule a g outputs = .ok code)
    (checks : GraphChecks a g table)
    (logical : Circuit.Runtime) (initial : ClockBound a g table logical)
    (r : RTL.InterfaceState a.storageShape) (running : r.Running)
    (same : StorageAgreement a.storageShape r.core.decode logical) (cycles : Nat) :
    ∃ result, (Concrete.parseModule code.text).bind (fun parsed => parsed.run a.storageShape cycles r) = some result ∧
      StorageAgreement a.storageShape result.core.decode (g.rtl.run a.storageShape.wireRange cycles logical) ∧ result.Running := by
  obtain ⟨_,_,codes,emission,compiled,rfl⟩ := generateGraphModule_components generated
  have invariant := fun n => clockGraph_run_bound checks initial n
  obtain ⟨result,executed,agrees,running'⟩ := physical_graph_run a g checks.capacity checks.closed checks.distinct compiled logical
    (fun n => by rw [clockGraph_rtl_run checks initial]; exact (invariant n).storage checks.size)
    (fun n _ => by rw [clockGraph_rtl_run checks initial]; simpa [graphStatements] using (invariant n).pc)
    r running same cycles
  refine ⟨result,?_,agrees,running'⟩
  rw [graphModule_text generated,SystemVerilog.moduleCode_run]
  exact executed

structure StructuredCircuit where
  tree : ClockTree
  graph : ClockGraph
  artifact : Artifact
  module : SystemVerilog.ModuleCode

/-- Retain runtime loops, schedule straight-line regions, then overlap safe
iteration boundaries without enumerating trip counts.
Holding registers are retained across control edges, so no loop-insensitive
liveness allocation is applied. -/
def structuredTree (s : Circuit.Schedule) : ClockTree :=
  overlapLoops (scheduleStructure earliestProposal s)

theorem structured_safe (s : Circuit.Schedule) : (structuredTree s).Safe :=
  overlapLoops_safe _ (scheduleStructure_safe _ s)

/-- The standard scheduler establishes the graph's control checks for arbitrary
source control, including nested branches and loops. -/
theorem structured_control_checks (s : Circuit.Schedule) (queues : Array (Nat × Nat)) :
    let graph := (structuredTree s).assemble queues
    1 < graph.nodes.size ∧
    graph.nodes.toList.all (fun n => decide n.distinct) = true ∧
    graph.nodes.toList.all (fun n => decide (n.targets graph.nodes.size)) = true := by
  refine ⟨(structuredTree s).assemble_entry queues,?_,?_⟩
  · apply List.all_eq_true.mpr
    intro n member
    exact decide_eq_true ((structuredTree s).assemble_distinct (structured_safe s) queues n member)
  · apply List.all_eq_true.mpr
    intro n member
    exact decide_eq_true ((structuredTree s).assemble_targets queues n member)

/-- Declaration checks are consequences of circuit construction, independently
of interval analysis, node validation, or successful RTL emission. -/
theorem structured_metadata (layout : Array (Nat × Nat))
    (unique : (layout.toList.map Prod.fst).Nodup) (code : HybridUnifiedPipeline.Code) :
    let generated := scheduleWith CountedBackend.named.build layout code
    let graph := (structuredTree generated.schedule).assemble generated.build.queues
    Allocation.MetadataReady (graph.artifact generated.build.wires generated.build.memories layout) := by
  exact Allocation.scheduled_metadata CountedBackend.named layout unique code _ rfl

/-- The assembled graph always has its reserved halt state, and the inventory
therefore has a valid entry even for an empty source body. -/
theorem structured_entry (tree : ClockTree) (queues : Array (Nat × Nat))
    (wires : Array Interval) (memories originals : Array (Nat × Nat)) :
    let a := (tree.assemble queues).artifact wires memories originals
    a.machine.entry < a.machine.nodes.size := by
  simp [ClockTree.assemble,ClockGraph.artifact,ClockNode.inventory]
  omega

/-- Construction discharges declarations, control and initial widths. Local
emission conditions and a transfer invariant imply success of inference,
validation and actual module generation. Deriving these local obligations
from the source grammar remains separate. -/
theorem structured_generation (layout : Array (Nat × Nat))
    (unique : (layout.toList.map Prod.fst).Nodup) (source : HybridUnifiedPipeline.Code)
    (outputs : List Nat) :
    let generated := scheduleWith CountedBackend.named.build layout source
    let graph := (structuredTree generated.schedule).assemble generated.build.queues
    let artifact := graph.artifact generated.build.wires generated.build.memories layout
    ∀ allowed : Nat → Frame → Prop,
      (∀ n ∈ graph.nodes.toList, n.EmitReady artifact) →
      InferenceProgress.TransferClosed artifact.wires.toList graph.nodes.size allowed
        (fun pc f => do
          let some node := graph.nodes[pc]? | throw "invalid structured node"
          node.transfer f) →
      allowed 1 (initialFrame artifact) →
      (∀ n ∈ outputs, ∃ size, (n,size) ∈ layout.toList) →
      ∃ code, generateGraphModule artifact graph outputs = .ok code := by
  dsimp only
  intro allowed ready transferClosed initialAllowed ports
  let generated := scheduleWith CountedBackend.named.build layout source
  let tree := structuredTree generated.schedule
  let graph := tree.assemble generated.build.queues
  let artifact := graph.artifact generated.build.wires generated.build.memories layout
  have metadata := structured_metadata layout unique source
  have initial := InitialWidths.scheduled_check layout source
  have initialFits : (initialFrame artifact).within artifact.wires.toList = true := by
    have h : (initialWidthFrame generated.build.wires.toList.length).within generated.build.wires.toList = true := by
      simp only [initialWidthsSafe,Bool.and_eq_true] at initial
      exact initial.2
    simpa [initialWidthFrame,initialFrame,artifact,ClockGraph.artifact] using h
  obtain ⟨table,inferred,_,_,_,valid⟩ := inferClockInvariant_complete (g := graph) (a := artifact) (by
    refine ⟨?_,transferClosed.widen⟩
    intro pc f hp ha hf
    obtain ⟨edges,step,valid⟩ := transferClosed.transfer pc f hp ha hf
    refine ⟨edges,?_,valid⟩
    cases found : graph.nodes[pc]? <;>
      dsimp only [graph,tree,generated] at found <;>
      simpa only [found] using step)
    (tree.assemble_entry _) initialFits initialAllowed
  have closed : ∀ n ∈ graph.nodes.toList, n.closed artifact.storageShape :=
    fun n member => (ready n member).closed
  have targets := tree.assemble_targets generated.build.queues
  have checks : GraphChecks artifact graph table := {
    capacity := rfl
    size := graph.inventory_size _ _ _
    entry := tree.assemble_entry _
    initial := initial
    invariant := valid
    closed := closed
    distinct := tree.assemble_distinct (structured_safe generated.schedule) _
    targets := targets }
  have module := metadata.moduleReady (structured_entry tree _ _ _ _)
    (graph.inventory_closed _ _ _ closed targets)
  exact generateGraphModule_succeeds (checkGraph_succeeds module checks inferred) ready (metadata.ports ports)

def compileStructured (p : HybridWord.Plan outputs sizes ks) (layout : Array (Nat × Nat)) :
    Except String StructuredCircuit := do
  let source := HybridUnifiedPipeline.lower p
  checkLayout layout source
  checkSendBudgets source
  checkCommunication source
  let generated := scheduleWith CountedBackend.named.build layout source
  let tree := structuredTree generated.schedule
  let graph := tree.assemble generated.build.queues
  let artifact := graph.artifact generated.build.wires generated.build.memories layout
  let code ← generateGraphModule artifact graph outputs
  return ⟨tree,graph,artifact,code⟩

structure StructuredFacts (p : HybridWord.Plan outputs sizes ks) (layout : Array (Nat × Nat))
    (built : StructuredCircuit) : Prop where
  covered : layoutCovers layout (HybridUnifiedPipeline.lower p) = true
  known : hasSendBounds (HybridUnifiedPipeline.lower p) = true
  communication : checkCommunication (HybridUnifiedPipeline.lower p) = .ok ()
  graph : built.graph = (structuredTree (scheduleWith CountedBackend.named.build layout (HybridUnifiedPipeline.lower p)).schedule).assemble
    (scheduleWith CountedBackend.named.build layout (HybridUnifiedPipeline.lower p)).build.queues
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

/-- The structured route reaches the same public observations as the native
source, through the actual printed text. A finite source execution is supplied
by the existing memory optimization theorem, not assumed per input. -/
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
  obtain ⟨cycles,finished⟩ := ClockTree.assemble_finishes (overlapLoops_correct (scheduleStructure_correct he earliestProposal))
  have finished' : (built.graph.run cycles ((wordPayload s x y).at 1)).result = some (result.map Payload.data) := by
    rw [facts.graph]; exact finished
  have numeric := word_initial_bound checks.initial s x y
  have initial : ClockBound built.artifact built.graph table ((wordPayload s x y).at 1) :=
    ⟨⟨numeric.data,numeric.wires,numeric.queues⟩,⟨fits,by intro q; simp [wordPayload,Payload.at,Circuit.Runtime.payload]⟩,checks.entry,clock_initial_table checks.invariant (by
      have h := checks.initial
      simp only [initialWidthsSafe,Bool.and_eq_true,decide_eq_true_eq] at h
      simpa using h.1) s x y⟩
  obtain ⟨physical,executed,agrees,_⟩ := generated_graph_run facts.generated checks _ initial r running same cycles
  refine ⟨cycles,physical,executed,public_observation agrees ?_⟩
  rw [clockGraph_rtl_run checks initial,finished']
  simpa only [Option.map_some,Option.map_map,Function.comp_def] using congrArg some ho

end IRComparison.Circuit.Pipelining
