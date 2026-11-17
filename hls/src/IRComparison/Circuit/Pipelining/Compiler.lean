import IRComparison.Circuit.Pipelining.WholeProgram

namespace IRComparison.Circuit.Pipelining

structure WordCircuit where
  artifact : Artifact
  realization : Realized
  module : SystemVerilog.ModuleCode
  virtualWires : Nat
  scheduleAccepted : Bool

def inputBuild (layout : Array (Nat × Nat)) : Build :=
  { memories := layout, nextArray := layout.foldl (fun n p => max n (p.1+1)) 0 }

/-- Opt-in pipelined backend. Dynamic structured control is explicitly
reported as unsupported here; pipelineWord retains its original Schedule
and the existing sequential backend remains available. -/
def compileWordCircuit (k : HybridWord.Kernel) (layout : Array (Nat × Nat))
    (ii : Nat) (outputs : List Nat) : Except String WordCircuit := do
  match pipelineWord k (inputBuild layout) ii with
  | (.original _,_) => throw "dynamic structured control: use the existing sequential backend"
  | (.scheduled source plan,b) =>
    let r := realize source plan.cycles b.wires
    let a := declarationArtifact r.batches r.widths b.memories layout b.queues
    let code ← generateBatchModule a r.batches outputs
    return ⟨a,r,code,b.wires.size,plan.accepted⟩

/-- General theorem for the executable source-to-text entry point, including
schedule selection, allocation fallback and every static output check. -/
theorem compileWordCircuit_correct (success : compileWordCircuit k layout ii outputs = .ok built)
    (s : HybridWord.State) (x y : HybridWord.Word) (fits : built.artifact.InputFits s.encode)
    (r : RTL.InterfaceState built.artifact.storageShape) (running : r.Running)
    (same : StorageAgreement built.artifact.storageShape r.core.decode ((wordPayload s x y).at 0)) :
    ∃ result, (SystemVerilog.Concrete.parseModule built.module.text).bind (fun parsed =>
      parsed.run built.artifact.storageShape (built.realization.batches.length+1) r) = some result ∧
      SourceObservation built.artifact.storageShape result.core.decode ((k.source x y s).map HybridWord.State.encode) := by
  cases selected : pipelineWord k (inputBuild layout) ii with
  | mk transformed b =>
    cases transformed with
    | original control => simp [compileWordCircuit,selected,throw] at success
    | scheduled source plan =>
      cases generated : generateBatchModule
          (declarationArtifact (realize source plan.cycles b.wires).batches (realize source plan.cycles b.wires).widths
            b.memories layout b.queues) (realize source plan.cycles b.wires).batches outputs with
      | error why => simp [compileWordCircuit,selected,generated,bind,Except.bind] at success
      | ok code =>
        simp only [compileWordCircuit,selected,generated,bind,Except.bind,pure,Except.pure,Except.ok.injEq] at success
        subst built
        exact pipelineWord_text_correct k (inputBuild layout) (by simp [inputBuild]) ii selected _ rfl generated s x y fits r running same

end IRComparison.Circuit.Pipelining
