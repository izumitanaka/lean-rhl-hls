import IRComparison.Circuit.RTL.ExpressionMapping
import IRComparison.Circuit.RTL.BankLoops
import IRComparison.Circuit.FinitePipelineSound

namespace IRComparison.Circuit.RTL

def Program.finiteTick (p : Program Combinational) (shape : StorageShape) (r : FiniteRuntime shape) : FiniteRuntime shape :=
  FiniteRuntime.pack shape (p.combinationalTick r.decode)

def Program.finiteRun (p : Program Combinational) (shape : StorageShape) : Nat → FiniteRuntime shape → FiniteRuntime shape
  | 0,r => r
  | n+1,r => p.finiteRun shape n (p.finiteTick shape r)

theorem artifact_tick_correct (a : Artifact) (r : FiniteRuntime a.storageShape) :
    (artifactProgram a).finiteTick a.storageShape r = FiniteRuntime.tick a.machine a.storageShape r := by
  unfold Program.finiteTick artifactProgram FiniteRuntime.tick
  rw [lowerCombinational_tick]
  rfl

theorem artifact_run_correct (a : Artifact) (r : FiniteRuntime a.storageShape) (cycles : Nat) :
    (artifactProgram a).finiteRun a.storageShape cycles r = FiniteRuntime.run a.machine a.storageShape cycles r := by
  induction cycles generalizing r with
  | zero => rfl
  | succ n ih => rw [Program.finiteRun,artifact_tick_correct,FiniteRuntime.run,ih]

/-- Arbitrary stable initial memory contents are supported: any physical
initial state agreeing with the source on live storage is sufficient. There
is no zero requirement on unused cells, and no per-read nondeterminism.
Establishing this relation from reset/config/start ports is a separate task. -/
theorem rtl_pipeline_from_initial (p : HybridWord.Plan outputs sizes ks)
    (compiled : compile layout (HybridUnifiedPipeline.lower p) = .ok checked)
    (outputsSafe : ∀ a ∈ outputs, a < layoutLimit layout)
    (outputPorts : ∀ a ∈ outputs, checked.artifact.storageShape.hasMemory a)
    (s : HybridWord.State) (x y : HybridWord.Word)
    (sized : PipelineShapes.Layout sizes s.encode)
    (ready : p.Ready (HybridWord.encode x) (HybridWord.encode y) s.encode)
    (fits : checked.artifact.InputFits s.encode)
    (physical : FiniteRuntime checked.artifact.storageShape)
    (initial : StorageAgreement checked.artifact.storageShape physical.decode
      (checked.artifact.machine.start s.encode (HybridWord.encode x) (HybridWord.encode y))) :
    let a := checked.artifact
    ∃ cycles, (((artifactProgram a).finiteRun a.storageShape cycles physical).result s.encode).map
        (Option.map (PipelineUse.observe outputs)) =
      some ((HybridWord.source x y ks s).map (fun t => PipelineUse.observe outputs t.encode)) := by
  obtain ⟨cycles,result,hr,ho⟩ := word_pipeline_finishes p compiled outputsSafe s x y sized ready
  have observed := finite_observation_from_initial checked.storage checked.valid checked.inputs
    s x y fits physical initial outputPorts cycles
  rw [checked.execution] at hr
  rw [hr,Option.map_some,ho] at observed
  exact ⟨cycles,by rw [artifact_run_correct]; exact observed⟩

/-- The exact RTL statement/expression structure consumed by the printer
preserves the native source. This theorem does not identify arbitrary text
with its SystemVerilog parsing, nor silently assume an IEEE four-state model. -/
theorem rtl_pipeline_finishes (p : HybridWord.Plan outputs sizes ks)
    (compiled : compile layout (HybridUnifiedPipeline.lower p) = .ok checked)
    (outputsSafe : ∀ a ∈ outputs, a < layoutLimit layout)
    (outputPorts : ∀ a ∈ outputs, checked.artifact.storageShape.hasMemory a)
    (s : HybridWord.State) (x y : HybridWord.Word)
    (sized : PipelineShapes.Layout sizes s.encode)
    (ready : p.Ready (HybridWord.encode x) (HybridWord.encode y) s.encode)
    (fits : checked.artifact.InputFits s.encode) :
    let a := checked.artifact
    ∃ cycles, (((artifactProgram a).finiteRun a.storageShape cycles
      (FiniteRuntime.pack a.storageShape (a.machine.start s.encode (HybridWord.encode x) (HybridWord.encode y)))).result s.encode).map
        (Option.map (PipelineUse.observe outputs)) =
      some ((HybridWord.source x y ks s).map (fun t => PipelineUse.observe outputs t.encode)) := by
  exact rtl_pipeline_from_initial p compiled outputsSafe outputPorts s x y sized ready fits _
    (FiniteRuntime.pack_correct (storage_reachable checked.storage checked.valid checked.inputs s x y fits 0))

end IRComparison.Circuit.RTL
