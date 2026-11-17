import IRComparison.Circuit.Pipelining.Realization
import IRComparison.Circuit.SystemVerilog.SerializationSound

namespace IRComparison.Circuit.Pipelining

/-- Merge only physical storage ranges. Acceptance below rechecks the actual
renamed instructions, rather than trusting this allocation heuristic. -/
def allocatedWidths (wires : Array Interval) (m : Nat → Nat) : Array Interval := Id.run do
  let count := wires.size.fold (fun k _ n => max n (m k+1)) 2
  let mut result := Array.replicate count zeroRange
  for k in List.range wires.size do
    result := result.modify (m k) (union · (wires[k]?.getD zeroRange))
  return result

structure Realized where
  batches : Batches
  widths : Array Interval
  allocation : Allocation

/-- Width rejection retains the original holding registers. It does not
change scheduling or silently truncate values. -/
def realize (code : Array Action) (cycles : Cycles) (wires : Array Interval) : Realized :=
  let bs := batches code cycles
  let allocation := chooseAllocation bs (color bs wires.size)
  let allocated := renamed allocation.mapping bs
  let widths := allocatedWidths wires allocation.mapping
  if batchWidthsSafe widths.toList allocated then ⟨allocated,widths,allocation⟩
  else ⟨bs,wires,⟨#[],false⟩⟩

theorem realize_correct (code : Array Action) (cycles : Cycles) (wires : Array Interval)
    (s : HybridWord.State) (x y : HybridWord.Word) :
    (runBatches cap (realize code cycles wires).batches (wordPayload s x y)).map Payload.data =
      (runCycles cap code cycles (wordPayload s x y)).map Payload.data := by
  unfold realize
  dsimp only
  split
  · rw [allocated_word_correct,runBatches_eq]
  · rw [runBatches_eq]

/-- Existing Artifact is reused for port/storage declarations only. Its node
inventory is NOT executed. Actual execution uses batchProgram and each
emitted case contains all writes assigned to that clock edge. -/
def declarationArtifact (bs : Batches) (wires : Array Interval)
    (memories publicMemories capacities : Array (Nat × Nat)) : Artifact :=
  ⟨⟨0,((bs.flatten.map (fun (a : Action) => a.node 0)) ++ List.replicate (bs.length+1) Node.halt).toArray,capacities⟩,
    wires,memories,publicMemories⟩

def combinationalCases (a : Artifact) (bs : Batches) : List (RTL.Statement RTL.Combinational) :=
  (batchStatements 0 bs).map (RTL.Statement.mapExpressions (RTL.combinational a.storageShape.wireRange))

def generateBatches (a : Artifact) (bs : Batches) : Except String (List SystemVerilog.Statement × Emission) :=
  ((combinationalCases a bs).mapM (statementCode a)).run {}

def checkBatchArtifact (a : Artifact) (bs : Batches) : Except String Unit := do
  checkModuleArtifact a
  let _ ← checkStorage a
  unless a.machine.entry = 0 do throw "pipeline entry must be zero"
  unless bs.length+1 ≤ a.storageShape.states do throw "pipeline PC does not fit storage"
  unless batchWidthsSafe a.wires.toList bs do throw "pipeline holding-register width invariant failed"
  unless initialWidthsSafe a.wires.toList do throw "pipeline input values do not fit holding registers"
  unless bs.all (fun as => decide (BanksDistinct as)) do throw "pipeline has simultaneous writes to the same bank"
  -- Validate the executed operations too, even if a caller supplies its own layout.
  unless bs.all (fun as => as.all (fun act => decide ((act.node 0).inStorage a.storageShape))) do
    throw "pipeline action refers outside storage"

def generateBatchModule (a : Artifact) (bs : Batches) (outputs : List Nat) : Except String SystemVerilog.ModuleCode := do
  checkBatchArtifact a bs
  let (cases,emission) ← generateBatches a bs
  checkReadOutputs a outputs
  return SystemVerilog.moduleCode a outputs cases emission.text

def emitBatches (a : Artifact) (bs : Batches) (outputs : List Nat) : Except String String := do
  return (← generateBatchModule a bs outputs).text

theorem batchModule_text (a : Artifact) (bs : Batches) (outputs : List Nat)
    (generated : generateBatchModule a bs outputs = .ok code)
    (cycles : Nat) (r : RTL.InterfaceState a.storageShape) :
    (SystemVerilog.Concrete.parseModule code.text).bind (fun parsed => parsed.run a.storageShape cycles r) =
      code.run a.storageShape cycles r := by
  cases hc : checkBatchArtifact a bs <;> simp [generateBatchModule,hc,bind,Except.bind] at generated
  cases hg : generateBatches a bs <;> simp [hg] at generated
  cases hr : checkReadOutputs a outputs <;> simp [hr,pure,Except.pure] at generated
  subst code
  exact SystemVerilog.printModule_run _ (SystemVerilog.moduleCode_storage _ _ _ _).positive rfl _ _ _

end IRComparison.Circuit.Pipelining
