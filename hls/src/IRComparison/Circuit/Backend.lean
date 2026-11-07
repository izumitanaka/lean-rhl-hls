import IRComparison.Circuit.BitMachine
import IRComparison.Circuit.FIFO
import IRComparison.Circuit.Capacity
import IRComparison.Circuit.BlocksSound
import IRComparison.Circuit.CompactProducerSound
import IRComparison.Circuit.CompactReceiverSound
import IRComparison.Circuit.Layout
import IRComparison.Circuit.CommunicationCheck
import IRComparison.Circuit.BudgetCheck
import IRComparison.Circuit.StaticCapacity
import IRComparison.Circuit.ExpandedPipelineSound
import IRComparison.Circuit.QueueSafety
import IRComparison.Circuit.StorageCheck

namespace IRComparison.Circuit

/-- A circuit with a mechanically checked inductive width invariant.
Source preservation is supplied by `unified_pipeline_finishes`; this
certificate supplies the separate finite-width arithmetic guarantee. -/
structure Checked where
  artifact : Artifact
  table : InvariantTable
  valid : validInvariant artifact table = true
  inputs : 2 ≤ artifact.wires.size
  storage : StorageCertificate artifact

/-- Interval inference is untrusted search; acceptance checks the complete
inductive table. Failure is explicit and does not emit an unsafe circuit. -/
def certify (a : Artifact) : Except String Checked := do
  let storage ← checkStorage a
  if hsize : 2 ≤ a.wires.size then
    let table ← inferInvariant a
    if h : validInvariant a table = true then
      return ⟨a,table,h,hsize,storage⟩
    else throw "width invariant checker rejected inferred table"
  else throw "circuit is missing input holding registers"

def compile (layout : Array (Nat × Nat)) (code : HybridUnifiedPipeline.Code) : Except String Checked := do
  checkLayout layout code
  checkSendBudgets code
  checkCommunication code
  certify (lower layout code)

def Checked.emit (c : Checked) (outputs : List Nat) : Except String String :=
  IRComparison.Circuit.emit c.artifact outputs

/-- Every accepted circuit agrees with its integer cycle model at all cycle
counts, for arbitrary BV32 data. No test-vector premise is used. -/
theorem Checked.execution (c : Checked) (s : HybridWord.State) (x y : HybridWord.Word) (cycles : Nat) :
    c.artifact.machine.bitRun (fun n => c.artifact.wires[n]?.getD zeroRange) cycles
      (c.artifact.machine.start s.encode (HybridWord.encode x) (HybridWord.encode y)) =
    c.artifact.machine.run cycles
      (c.artifact.machine.start s.encode (HybridWord.encode x) (HybridWord.encode y)) :=
  bitRun_from_input c.valid c.inputs s x y cycles

end IRComparison.Circuit
