import IRComparison.Examples.HybridExamples
import IRComparison.Examples.UnifiedWorkloads
import IRComparison.Hybrid.HybridInputs
import IRComparison.Hybrid.HybridUnifiedPipeline
open IRComparison IRComparison.GlobalPipelineExamples

def check (name : String) (outputs : List Nat) (size : Nat) (ks : List HybridIR.Kernel) (legacyKs : List UnifiedPipeline.Kernel)
    (initial : State) (x y : Int) (expectedPolicy : List Nat) : IO Unit := do
  let some p := HybridIR.compileKernels outputs (fun _ => size) ks
    | throw (IO.userError s!"{name}: hybrid compilation failed")
  unless p.policy == expectedPolicy do throw (IO.userError s!"{name}: policy {p.policy}")
  let observe := fun s : State => (outputs.map s.arrays,s.regs 0,s.regs 2)
  let source := HybridIR.source x y ks initial
  let result := HybridIR.Program.eval p x y initial
  unless result.isSome && result.map observe == source.map observe do
    throw (IO.userError s!"{name}: hybrid/source mismatch")
  let legacy := UnifiedPipeline.compile outputs (fun _ => size) legacyKs
  unless result.map observe == (legacy.eval x y initial).map observe do
    throw (IO.userError s!"{name}: hybrid/existing mismatch")
  let some state := result | throw (IO.userError "missing result")
  for a in expectedPolicy do
    unless (state.arrays a).isEmpty do throw (IO.userError s!"{name}: intermediate {a} retained")
  match HybridControl.run x y 100000 (.start (HybridIR.Program.code p) initial (fun _ => [])) with
  | .stopped actual => unless actual.map observe == result.map observe do
      throw (IO.userError s!"{name}: hybrid control mismatch")
  | _ => throw (IO.userError s!"{name}: hybrid control did not finish")
  let some unified := HybridUnifiedPipeline.compile outputs (fun _ => size) ks
    | throw (IO.userError s!"{name}: unified compilation failed")
  unless (unified.eval x y initial).map observe == result.map observe do
    throw (IO.userError s!"{name}: unified result mismatch")
  match HybridUnifiedPipeline.run x y 100000 (HybridUnifiedPipeline.start (HybridUnifiedPipeline.lower unified) initial) with
  | .stopped actual => unless actual.map observe == result.map observe do
      throw (IO.userError s!"{name}: unified control mismatch")
  | _ => throw (IO.userError s!"{name}: unified control did not finish")
  if name == "interleaved/false/0" then
    IO.FS.writeFile "artifacts/hybrid/interleaved.txt" (reprStr (HybridIR.Program.code p))
  IO.println s!"{name}: FIFO={p.policy}; source, existing target, hybrid target and hybrid control agree"

def main : IO Unit := do
  IO.FS.createDirAll "artifacts/hybrid"
  IO.FS.writeFile "artifacts/hybrid/explicit-reads.txt" (reprStr (HybridIR.extract HybridExamples.sample))
  for functional in [false,true] do
    let branchKs := [HybridInputs.AlternativeExamples.native.hybridKernel 4 0 0 1 1 (fun _ => []),
      HybridInputs.GlobalPipelineExamples.independentKernel functional,
      HybridInputs.AlternativePipelineExamples.sink.hybridKernel 4 1 0 1 1 (fun _ => [0,3])]
    let legacyBranch := [UnifiedPipelineExamples.branchKernels[0]'(by decide), independentKernel false,
      UnifiedPipelineExamples.branchKernels[1]'(by decide)]
    for (name,outputs,ks,legacy,expected) in [
      ("nonadjacent",[2,3],HybridInputs.GlobalPipelineExamples.separated functional,separated functional,[1]),
      ("interleaved",[2,3,6],HybridInputs.GlobalPipelineExamples.kernels functional,kernels functional,[1,5]),
      ("intervening-read",[2,3],HybridInputs.GlobalPipelineExamples.readBetween functional,readBetween functional,[]),
      ("public-output",[1,2,3],HybridInputs.GlobalPipelineExamples.publicOutput functional,publicOutput functional,[]),
      ("read-before-producer",[6],HybridInputs.GlobalPipelineExamples.beforeProducer functional,beforeProducer functional,[1]),
      ("nonadjacent-branch",[2,3],branchKs,legacyBranch,[1])] do
      for flag in [0,1] do
        check s!"{name}/{functional}/{flag}" outputs 4 ks legacy initial 10 flag expected
  for (w,legacy) in HybridInputs.UnifiedWorkloads.workloads.zip UnifiedWorkloads.workloads do
    for (ks,label) in [(legacy.imperative,"imperative"),(legacy.functional,"functional")] do
      check s!"{w.name}/{label}" [4] 64 w.imperative ks WindowWorkloads.initial 0 0 [1,2,3]
