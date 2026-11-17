import IRComparison.Circuit.RTL.Interface

namespace IRComparison.Circuit.RTL

def interfaceRun (a : Artifact) : Nat → InterfaceState a.storageShape → InterfaceState a.storageShape
  | 0,r => r
  | n+1,r => interfaceRun a n (interfaceTick a {} r)

def InterfaceState.Running (r : InterfaceState shape) : Prop := r.busy = !r.core.done

theorem quiet_tick (a : Artifact) (r : InterfaceState a.storageShape) :
    interfaceTick a {} r = if r.busy then
      let next := (artifactProgram a).finiteTick a.storageShape r.core
      ⟨next,!next.done⟩ else r := by
  cases h : r.busy <;> simp [interfaceTick,controller,Controller.select,PortTest.eval,h]

theorem quiet_tick_running (a : Artifact) (r : InterfaceState a.storageShape) (h : r.Running) :
    (interfaceTick a {} r).Running := by
  rw [quiet_tick]
  split
  · rfl
  · exact h

theorem quiet_tick_agrees (a : Artifact)
    (closed : ∀ node ∈ a.machine.nodes.toList, node.inStorage a.storageShape)
    (r : InterfaceState a.storageShape) (logical : Runtime)
    (running : r.Running) (same : StorageAgreement a.storageShape r.core.decode logical)
    (bounded : StorageBound a.storageShape (a.machine.tick logical))
    (widths : logical.done = false → InputsBound logical.data logical.wires a.storageShape.wireRange) :
    StorageAgreement a.storageShape (interfaceTick a {} r).core.decode (a.machine.tick logical) := by
  rw [quiet_tick]
  split
  · simp only
    rw [artifact_tick_correct,finiteTick_from_agreement closed same widths]
    exact FiniteRuntime.pack_correct bounded
  · rename_i idle
    have hd : logical.done = true := by
      have he := same.done
      change r.core.done = logical.done at he
      unfold InterfaceState.Running at running
      cases hb : r.busy <;> cases hc : r.core.done <;> simp_all
    rw [halt_stable a.machine logical hd]
    exact same

theorem quiet_run_agrees (a : Artifact)
    (closed : ∀ node ∈ a.machine.nodes.toList, node.inStorage a.storageShape)
    (logical : Runtime)
    (bounded : ∀ n, StorageBound a.storageShape (a.machine.run n logical))
    (widths : ∀ n, (a.machine.run n logical).done = false →
      InputsBound (a.machine.run n logical).data (a.machine.run n logical).wires a.storageShape.wireRange)
    (r : InterfaceState a.storageShape) (running : r.Running)
    (same : StorageAgreement a.storageShape r.core.decode logical) (cycles : Nat) :
    StorageAgreement a.storageShape (interfaceRun a cycles r).core.decode (a.machine.run cycles logical) := by
  induction cycles generalizing r logical with
  | zero => exact same
  | succ n ih =>
    apply ih (a.machine.tick logical) (fun k => bounded (k+1)) (fun k => widths (k+1))
      (interfaceTick a {} r) (quiet_tick_running a r running)
    exact quiet_tick_agrees a closed r logical running same (bounded 1) (widths 0)

/-- After a permitted start edge, the actual interface model reaches the
source result with control inputs deasserted until completion. This proves
one invocation, not a protocol for arbitrary interrupt/reset sequences. -/
theorem interface_pipeline_finishes (p : HybridWord.Plan outputs sizes ks)
    (compiled : compile layout (HybridUnifiedPipeline.lower p) = .ok checked)
    (outputsSafe : ∀ id ∈ outputs, id < layoutLimit layout)
    (outputPorts : ∀ id ∈ outputs, checked.artifact.storageShape.hasMemory id)
    (r : InterfaceState checked.artifact.storageShape) (ports : Ports)
    (idle : r.busy = false) (noReset : ports.reset = false) (start : ports.start = true)
    (sized : PipelineShapes.Layout sizes (restoreLengths checked.artifact r.core).inputSource.encode)
    (ready : p.Ready (HybridWord.encode ports.x) (HybridWord.encode ports.y)
      (restoreLengths checked.artifact r.core).inputSource.encode) :
    let a := checked.artifact
    let s := (restoreLengths a r.core).inputSource
    ∃ cycles, ((interfaceRun a cycles (interfaceTick a ports r)).core.result s.encode).map
      (Option.map (PipelineUse.observe outputs)) =
      some ((HybridWord.source ports.x ports.y ks s).map (fun t => PipelineUse.observe outputs t.encode)) := by
  let a := checked.artifact
  let s := (restoreLengths a r.core).inputSource
  let logical := a.machine.start s.encode (HybridWord.encode ports.x) (HybridWord.encode ports.y)
  have fits : a.InputFits s.encode := by
    intro n hn
    rw [FiniteRuntime.inputSource_encode]
    simp only [Circuit.FiniteRuntime.decode,hn.1,↓reduceDIte]
    exact WordBuffer.contents_size _
  have bounded := storage_reachable checked.storage checked.valid checked.inputs s ports.x ports.y fits
  have initial := beginInvocation_agrees a r.core ports.x ports.y (bounded 0)
  obtain ⟨cycles,result,hr,ho⟩ := word_pipeline_finishes p compiled outputsSafe s ports.x ports.y sized ready
  have running : (interfaceTick a ports r).Running := by
    rw [start_edge a ports r idle noReset start]
    rfl
  have same := quiet_run_agrees a checked.storage.closed logical bounded
    (fun n => reachable_widths checked.valid checked.inputs s ports.x ports.y n)
    (interfaceTick a ports r) running (by rw [start_edge a ports r idle noReset start]; exact initial) cycles
  have observed := observation_from_agreement checked.storage.closed logical cycles _ same outputPorts
  rw [checked.execution] at hr
  change (a.machine.run cycles logical).result = some result at hr
  rw [hr,Option.map_some,ho] at observed
  exact ⟨cycles,observed⟩

end IRComparison.Circuit.RTL
