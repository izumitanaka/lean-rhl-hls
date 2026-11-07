import IRComparison.Circuit.StorageNumeric

namespace IRComparison.Circuit

def idBound (ids : List Nat) : Nat := ids.foldl (fun n id => max n (id+1)) 0

def Artifact.storageShape (a : Artifact) : StorageShape where
  registers := idBound (a.machine.nodes.toList.flatMap Node.registers)
  memories := idBound (a.memories.toList.map Prod.fst)
  queues := idBound (a.machine.capacities.toList.map Prod.fst)
  memorySize := fun n => ((a.memories.toList.find? (fun p => p.1 == n)).map Prod.snd).getD 0
  memoryLive := fun n => a.memories.any (fun p => p.1 == n)
  queueSize := a.machine.capacity
  wires := a.wires
  states := a.machine.nodes.size

instance Expr.inStorageDecidable (s : StorageShape) (e : Expr) : Decidable (e.inStorage s) := by
  cases e with
  | fail | lit => exact isTrue True.intro
  | reg | wire => unfold inStorage; infer_instance
  | memory a j =>
    let _ := j.inStorageDecidable s
    exact instDecidableAnd
  | natIndex a => exact a.inStorageDecidable s
  | bin op a b =>
    let _ := a.inStorageDecidable s
    let _ := b.inStorageDecidable s
    exact instDecidableAnd
  | seq a b =>
    let _ := a.inStorageDecidable s
    let _ := b.inStorageDecidable s
    exact instDecidableAnd
  | select c a b =>
    let _ := c.inStorageDecidable s
    let _ := a.inStorageDecidable s
    let _ := b.inStorageDecidable s
    exact instDecidableAnd

instance Node.inStorageDecidable (s : StorageShape) (n : Node) : Decidable (n.inStorage s) := by
  cases n <;> unfold inStorage <;> infer_instance

structure StorageCertificate (a : Artifact) : Type where
  entry : a.machine.entry < a.storageShape.states
  closed : ∀ node ∈ a.machine.nodes.toList, node.inStorage a.storageShape

def checkStorage (a : Artifact) : Except String (StorageCertificate a) :=
  if hp : a.machine.entry < a.storageShape.states then
    if hn : ∀ node ∈ a.machine.nodes.toList, node.inStorage a.storageShape then .ok ⟨hp,hn⟩
    else .error "circuit storage layout does not cover an operation, edge, or snapshot"
  else .error "circuit entry is outside the finite control bank"

/-- Memory sizes are interface bounds, just as input array lengths are part
of the source layout. Initial private snapshot banks may be empty. -/
def Artifact.InputFits (a : Artifact) (s : State) : Prop :=
  ∀ n, a.storageShape.hasMemory n → (s.arrays n).size ≤ a.storageShape.memorySize n

theorem storage_reachable (certificate : StorageCertificate a)
    (valid : validInvariant a table = true) (inputs : 2 ≤ a.wires.size)
    (s : HybridWord.State) (x y : HybridWord.Word) (fits : a.InputFits s.encode) (cycles : Nat) :
    StorageBound a.storageShape (a.machine.run cycles (a.machine.start s.encode (HybridWord.encode x) (HybridWord.encode y))) := by
  have geometry := run_geometry certificate.closed certificate.entry (show MemoriesFit a.storageShape
    (a.machine.start s.encode (HybridWord.encode x) (HybridWord.encode y)) from fits) cycles
  have numeric := run_runtime_global valid (initial_table_bound valid inputs s x y) (initial_runtime_global valid inputs s x y) cycles
  have queues := initialized_queue_bound a.machine s.encode (HybridWord.encode x) (HybridWord.encode y) cycles
  refine ⟨geometry.1,numeric.data,geometry.2,?_,fun q _ => queues q,numeric.queues⟩
  intro n hn
  simpa only [Artifact.storageShape,StorageShape.wireRange,Frame.get,Array.getElem?_toList] using numeric.wires n

theorem finite_execution (certificate : StorageCertificate a)
    (valid : validInvariant a table = true) (inputs : 2 ≤ a.wires.size)
    (s : HybridWord.State) (x y : HybridWord.Word) (fits : a.InputFits s.encode) (cycles : Nat) :
    StorageAgreement a.storageShape
      (FiniteRuntime.run a.machine a.storageShape cycles
        (FiniteRuntime.pack a.storageShape (a.machine.start s.encode (HybridWord.encode x) (HybridWord.encode y)))).decode
      (a.machine.run cycles (a.machine.start s.encode (HybridWord.encode x) (HybridWord.encode y))) :=
  finiteRun_agrees certificate.closed (storage_reachable certificate valid inputs s x y fits)
    (fun n => reachable_widths valid inputs s x y n) cycles

end IRComparison.Circuit
