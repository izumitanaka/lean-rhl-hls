import IRComparison.Circuit.SystemVerilog.DeclarationSound

namespace IRComparison.Circuit.SystemVerilog

/-- Execute the actual module fields. The finite physical layout is supplied
as the representation of storage; generated declaration types and capacities
are related to it by DeclarationSound. No source Artifact is available here. -/
def ModuleCode.tick (code : ModuleCode) (shape : StorageShape)
    (ports : RTL.Ports) (r : RTL.InterfaceState shape) : Option (RTL.InterfaceState shape) := do
  let base := environmentFor shape r.core code.wires #[] r.busy ports
  let (env,body) ← match code.controller.select ports r.busy with
    | .reset => pure (base,code.reset)
    | .start => pure (base,code.start)
    | .configure => pure (base,code.configure)
    | .hold => pure (base,Statement.skip)
    | .execute => do
      let values ← appendWires (environmentFor shape r.core code.wires #[]) code.wires.toList #[]
      pure (base.withTemporaries values,(code.cases[r.core.pc.toNat]?).getD code.fault)
  let writes ← body.eval env base.store
  return ⟨writes.commit shape,writes.busy⟩

def ModuleCode.run (code : ModuleCode) (shape : StorageShape) :
    Nat → RTL.InterfaceState shape → Option (RTL.InterfaceState shape)
  | 0,r => some r
  | n+1,r => do code.run shape n (← code.tick shape {} r)

theorem moduleCode_tick (a : Artifact) (outputs : List Nat) (cases : List Statement)
    (wires : Array Wire) (ports : RTL.Ports) (r : RTL.InterfaceState a.storageShape) :
    (moduleCode a outputs cases wires).tick a.storageShape ports r = physicalTick a cases wires ports r := by
  cases action : RTL.controller.select ports r.busy <;>
    simp [ModuleCode.tick,moduleCode,physicalTick,clockCode,action,evaluateWires,environment,Option.bind_assoc]

theorem moduleCode_run (a : Artifact) (outputs : List Nat) (cases : List Statement)
    (wires : Array Wire) (cycles : Nat) (r : RTL.InterfaceState a.storageShape) :
    (moduleCode a outputs cases wires).run a.storageShape cycles r = physicalRun a cases wires cycles r := by
  induction cycles generalizing r with
  | zero => rfl
  | succ n ih =>
    rw [ModuleCode.run,physicalRun,moduleCode_tick]
    cases physicalTick a cases wires {} r with
    | none => rfl
    | some next => exact ih next

/-- Recover the exact generated components from successful module assembly,
including the existing checks. No per-program proof search is performed. -/
theorem generateModule_components (success : generateModule a outputs = .ok code) :
    ∃ cases emission, generateCode a = .ok (cases,emission) ∧
      code = moduleCode a outputs cases emission.text := by
  unfold generateModule at success
  cases artifact : checkModuleArtifact a with
  | error why => simp [artifact,bind,Except.bind] at success
  | ok unit =>
    cases unit
    cases generated : generateCode a with
    | error why => simp [artifact,generated,bind,Except.bind] at success
    | ok result =>
      obtain ⟨cases,emission⟩ := result
      cases ports : checkReadOutputs a outputs with
      | error why => simp [artifact,generated,ports,bind,Except.bind] at success
      | ok unit =>
        cases unit
        simp only [artifact,generated,ports,bind,Except.bind,pure,Except.pure,Except.ok.injEq] at success
        exact ⟨cases,emission,rfl,success.symm⟩

theorem emit_module (success : emit a outputs = .ok text) :
    ∃ code, generateModule a outputs = .ok code ∧ code.text = text := by
  unfold emit at success
  cases generated : generateModule a outputs with
  | error why => simp [generated,bind,Except.bind] at success
  | ok code =>
    simp only [generated,bind,Except.bind,pure,Except.pure,Except.ok.injEq] at success
    exact ⟨code,rfl,success⟩

/-- Declaration/layout obligations carried alongside the module execution.
Names here are structured identifiers; lexical correspondence remains part
of the serialization boundary. -/
structure ModuleCode.StorageMatches (code : ModuleCode) (shape : StorageShape) : Prop where
  types : ∀ (r : FiniteRuntime shape) name t,
    declaredType code.storage name = some t → t = (environmentFor shape r code.wires #[]).type name
  memories : ∀ id, (declaredCapacity code.storage (.memory id)).getD 0 = shape.memorySize id
  queues : ∀ id, (declaredCapacity code.storage (.queue id)).getD 0 = shape.queueSize id
  positive : ∀ d ∈ code.storage, 0 < d.width

theorem moduleCode_storage (a : Artifact) (outputs : List Nat) (cases : List Statement) (wires : Array Wire) :
    (moduleCode a outputs cases wires).StorageMatches a.storageShape := by
  constructor
  · exact fun r name t found => storageDeclarations_type a r wires name t found
  · intro id
    change (declaredCapacity (storageDeclarations a) (.memory id)).getD 0 = _
    rw [storageDeclarations_memory_capacity]
    rfl
  · intro id
    change (declaredCapacity (storageDeclarations a) (.queue id)).getD 0 = _
    rw [storageDeclarations_queue_capacity]
    rfl
  · exact storageDeclarations_positive a

/-- Whole emitted-module connection, from the existing post-start boundary.
The module actually passed to the printer terminates and exposes every
successful source result through its read port. This is the structured-module theorem. `SerializationSound` connects it
to the independently parsed String and proves the production printer. It
still does not claim all IEEE four-state/event semantics. -/
theorem emitted_pipeline_readout (p : HybridWord.Plan outputs sizes ks)
    (compiled : compile layout (HybridUnifiedPipeline.lower p) = .ok checked)
    (emitted : emit checked.artifact outputs = .ok text)
    (outputsSafe : ∀ id ∈ outputs, id < layoutLimit layout)
    (outputPorts : ∀ id ∈ outputs, checked.artifact.storageShape.hasMemory id)
    (prepared : FiniteRuntime checked.artifact.storageShape) (x y : BitVec 32)
    (sized : PipelineShapes.Layout sizes (RTL.restoreLengths checked.artifact prepared).inputSource.encode)
    (ready : p.Ready (HybridWord.encode x) (HybridWord.encode y)
      (RTL.restoreLengths checked.artifact prepared).inputSource.encode) :
    let a := checked.artifact
    let s := (RTL.restoreLengths a prepared).inputSource
    ∃ code cycles result,
      generateModule a outputs = .ok code ∧ code.text = text ∧ code.StorageMatches a.storageShape ∧
      code.run a.storageShape cycles ⟨RTL.beginInvocation a prepared x y,true⟩ = some result ∧
      result.core.done = true ∧ result.busy = false ∧
      (∀ final, HybridWord.source x y ks s = some final →
        result.core.error = false ∧ ∀ request,
          code.read.eval (environmentFor a.storageShape result.core code.wires #[]) request =
            some (stateReadResult a outputs final.encode request)) ∧
      (HybridWord.source x y ks s = none → result.core.error = true) := by
  obtain ⟨code,generated,printed⟩ := emit_module emitted
  obtain ⟨cases,emission,computed,same⟩ := generateModule_components generated
  obtain ⟨cycles,result,executed,finished,idle,readout,failed⟩ :=
    physical_pipeline_readout p compiled computed outputsSafe outputPorts prepared x y sized ready
  refine ⟨code,cycles,result,generated,printed,?_,?_,finished,idle,?_,failed⟩
  · rw [same]
    exact moduleCode_storage _ _ _ _
  · rw [same,moduleCode_run]
    exact executed
  · rw [same]
    exact readout

end IRComparison.Circuit.SystemVerilog
