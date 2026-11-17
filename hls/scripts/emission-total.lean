import IRComparison.Examples.FixedMemoryExamples
import IRComparison.Examples.CertifiedHLSExamples

open IRComparison Circuit Circuit.Pipelining CertifiedHLS
open Circuit.SystemVerilog.Generation
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- Check that the general emission-success premises hold on actual HLS
artifacts. These cases are regression evidence, not the general source-grammar
or circuit-construction completeness proof. -/
def verifyArtifact (name : String) (a : Artifact) (outputs : List Nat) : IO Unit := do
  unless decide (ModuleReady a) do throw (IO.userError s!"{name}: module structure")
  for (n,i) in a.machine.nodes.toList.zipIdx do
    unless decide (NodeReady a n) do
      throw (IO.userError s!"{name}: node {i} is not emission-ready")
  unless decide (∀ n ∈ outputs, a.storageShape.hasMemory n) do
    throw (IO.userError s!"{name}: public outputs")
  let _ ← IO.ofExcept (Circuit.emit a outputs)
  pure ()

def verify {source : List Stage} {entry : Entry source} (name : String)
    (result : Except String (Compiled entry outputs sizes layout fuel)) : IO Unit := do
  let c ← IO.ofExcept result
  verifyArtifact name c.backend.artifact outputs
  match c.backend with
  | .structured built _ =>
    for (n,i) in built.graph.nodes.toList.zipIdx do
      unless decide (n.EmitReady built.artifact) do
        throw (IO.userError s!"{name}: simultaneous node {i} is not emission-ready")
    let _ ← IO.ofExcept (generateGraph built.artifact built.graph)
  | _ => pure ()
  IO.println s!"PASS {name}: {c.backend.route}, structural emission-success premises"

open FixedMemoryExamples in
private def fixedCases : IO Unit := do
  verify "independent-copy" (independentHLS.compile [0,1,2])
  verify "repeated-copy" (repeatedHLS.compile [0,1,2])
  verify "swap" (swapHLS.compile [0,1,2])
  verify "nested-branch" (nestedHLS.compile [0,1,2])
  verify "self-copy" (selfHLS.compile [0,1,2])
  verify "sparse" (sparseHLS.compile [7,11])
  verify "scalar" (scalarHLS.compile [])
  verify "empty" (emptyHLS.compile [7])
  verify "capture" (capturedHLS.compile [])
  verify "capture-loop" (capturedLoopHLS.compile [])

open CertifiedHLSExamples in
private def stageCases : IO Unit := do
  verify "filter" (filterHLS.compile 5 0 0 1 3 supply [1] sizes layout 4096)
  verify "filter-static" (filterHLS.compile 5 0 0 1 3 supply [1] sizes layout 4096 .staticExpansion)
  verify "reverse" (filterHLS.compile 5 0 2 (-1) 3 supply [1] sizes layout 4096)
  verify "fifo-chain" (CertifiedHLS.compile chainEntry [2] sizes layout 4096)
  verify "public-chain" (CertifiedHLS.compile chainEntry [1,2] sizes layout 4096)
  let original ← IO.ofExcept (filterHLS.compile 5 0 0 1 3 supply [1] sizes layout 4096)
  let serial ← IO.ofExcept (Circuit.compile layout (HybridUnifiedPipeline.lower original.plan))
  verifyArtifact "filter-sequential" serial.artifact [1]
  IO.println "PASS filter-sequential: sequential, structural emission-success premises"

def main : IO Unit := do
  fixedCases
  stageCases
