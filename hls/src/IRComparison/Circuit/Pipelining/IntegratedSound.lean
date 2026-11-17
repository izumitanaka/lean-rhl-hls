import IRComparison.Circuit.Pipelining.Dispatch

namespace IRComparison.Circuit.Pipelining

def Integrated.artifact : Integrated p layout fuel → Artifact
  | .pipelined b _ => b.artifact
  | .structured b _ => b.artifact
  | .sequential b _ _ _ _ => b.artifact

/-- The logical post-start boundary of the selected backend, not a new
source semantics. Static and structured graphs have different entry PCs. -/
def Integrated.initial (c : Integrated p layout fuel)
    (s : HybridWord.State) (x y : HybridWord.Word) : Circuit.Runtime :=
  match c with
  | .pipelined .. => (wordPayload s x y).at 0
  | .structured .. => (wordPayload s x y).at 1
  | .sequential b _ _ _ _ => b.artifact.machine.start s.encode (HybridWord.encode x) (HybridWord.encode y)

/-- The sequential fallback uses the same named-communication builder as the
structured route. Only scheduling changes; its memory plan is retained. -/
theorem sequential_named_finishes {p : HybridWord.Plan outputs sizes ks}
    (compiled : Circuit.compile layout (HybridUnifiedPipeline.lower p) CountedBackend.named.build = .ok checked)
    (outputsSafe : ∀ a ∈ outputs, a < layoutLimit layout)
    (s : HybridWord.State) (x y : HybridWord.Word)
    (sized : PipelineShapes.Layout sizes s.encode)
    (ready : p.Ready (HybridWord.encode x) (HybridWord.encode y) s.encode) :
    ∃ cycles result,
      (checked.artifact.machine.run cycles
        (checked.artifact.machine.start s.encode (HybridWord.encode x) (HybridWord.encode y))).result = some result ∧
      result.map (PipelineUse.observe outputs) =
        (HybridWord.source x y ks s).map (fun t => PipelineUse.observe outputs t.encode) := by
  obtain ⟨same,covered,known,communication⟩ := Circuit.compile_facts compiled
  obtain ⟨result,executed,observed⟩ := optimized_schedule_correct_with CountedBackend.named p layout
    covered known communication outputsSafe s x y sized ready
  obtain ⟨cycles,finished⟩ := Schedule.assemble_finishes _ (wordPayload s x y) executed
  refine ⟨cycles,result.map Payload.data,?_,?_⟩
  · rw [same]
    exact finished
  · simpa only [Option.map_map,Function.comp_def] using observed

theorem sequential_text_correct {p : HybridWord.Plan outputs sizes ks}
    (compiled : Circuit.compile layout (HybridUnifiedPipeline.lower p) CountedBackend.named.build = .ok checked)
    (emitted : checked.emit outputs = .ok text)
    (outputsSafe : ∀ a ∈ outputs, a < layoutLimit layout)
    (s : HybridWord.State) (x y : HybridWord.Word)
    (sized : PipelineShapes.Layout sizes s.encode)
    (ready : p.Ready (HybridWord.encode x) (HybridWord.encode y) s.encode)
    (fits : checked.artifact.InputFits s.encode)
    (r : RTL.InterfaceState checked.artifact.storageShape) (running : r.Running)
    (same : StorageAgreement checked.artifact.storageShape r.core.decode
      (checked.artifact.machine.start s.encode (HybridWord.encode x) (HybridWord.encode y))) :
    ∃ cycles result, SystemVerilog.runText text checked.artifact.storageShape cycles r = some result ∧
      PublicObservation checked.artifact.storageShape outputs result.core.decode
        ((HybridWord.source x y ks s).map HybridWord.State.encode) := by
  obtain ⟨code,generated,printed⟩ := SystemVerilog.emit_module emitted
  obtain ⟨cases,emission,computed,hcode⟩ := SystemVerilog.generateModule_components generated
  have bounded := storage_reachable checked.storage checked.valid checked.inputs s x y fits
  obtain ⟨cycles,expected,finished,observed⟩ := sequential_named_finishes compiled outputsSafe s x y sized ready
  obtain ⟨actual,executed,agrees,_⟩ := SystemVerilog.physicalRun_agrees checked.artifact checked.storage computed
    _ bounded (fun n => reachable_widths checked.valid checked.inputs s x y n) r running same cycles
  refine ⟨cycles,actual,?_,public_observation agrees ?_⟩
  · have matched := SystemVerilog.moduleCode_storage checked.artifact outputs cases emission.text
    rw [← printed]
    unfold SystemVerilog.runText
    unfold SystemVerilog.ModuleCode.text
    rw [SystemVerilog.Concrete.parse_printModule code (by simpa [hcode] using matched.positive)
      (SystemVerilog.generated_standard generated)]
    simp only [Option.bind_some,SystemVerilog.moduleReadback_run]
    rw [hcode,SystemVerilog.moduleCode_run]
    exact executed
  · rw [finished,Option.map_some]
    exact congrArg some (by simpa only [Option.map_map,Function.comp_def] using observed)

/-- All production backend alternatives share one source-to-text contract.
No assumption of target termination or per-input equivalence is required. -/
theorem Integrated.correct {p : HybridWord.Plan outputs sizes ks}
    (c : Integrated p layout fuel)
    (outputsSafe : ∀ a ∈ outputs, a < layoutLimit layout)
    (s : HybridWord.State) (x y : HybridWord.Word)
    (sized : PipelineShapes.Layout sizes s.encode)
    (ready : p.Ready (HybridWord.encode x) (HybridWord.encode y) s.encode)
    (fits : c.artifact.InputFits s.encode)
    (r : RTL.InterfaceState c.artifact.storageShape) (running : r.Running)
    (same : StorageAgreement c.artifact.storageShape r.core.decode (c.initial s x y)) :
    ∃ cycles result, SystemVerilog.runText c.text c.artifact.storageShape cycles r = some result ∧
      PublicObservation c.artifact.storageShape outputs result.core.decode
        ((HybridWord.source x y ks s).map HybridWord.State.encode) := by
  cases c with
  | pipelined b success =>
    obtain ⟨result,executed,observed⟩ := compileOptimizedScheduled_correct success outputsSafe s x y sized ready fits r running same
    exact ⟨_,result,executed,observed⟩
  | structured b success =>
    exact Shared.compileStructured_correct success outputsSafe s x y sized ready fits r running same
  | sequential b text compiled emitted reason =>
    exact sequential_text_correct compiled emitted outputsSafe s x y sized ready fits r running same

end IRComparison.Circuit.Pipelining
