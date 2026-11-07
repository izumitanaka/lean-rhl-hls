import IRComparison.Examples.UnifiedWorkloads
open IRComparison

def main : IO Unit := do
  for (w,n) in UnifiedWorkloads.workloads.zipIdx do
    for (ks,route) in [(w.imperative,"imperative"),(w.functional,"functional")] do
      let plan ← UnifiedPipeline.compileWithSMT [4] (fun _ => 64) ks
        (System.FilePath.mk "artifacts/unified-smt" / toString n / route)
      UnifiedWorkloads.checkPlan (w.name ++ "/" ++ route) ks plan
  let large ← UnifiedPipeline.compileWithSMT [4] (fun _ => 1000000004)
    UnifiedPipelineExamples.billionKernels "artifacts/unified-smt/billion"
  unless UnifiedPipelineExamples.isCompact large do throw (IO.userError "large pipeline was expanded")
  let branched ← UnifiedPipeline.compileWithSMT [2] (fun _ => 4)
    UnifiedPipelineExamples.branchKernels "artifacts/unified-smt/branch"
  unless (branched.eval 10 0 AlternativeExamples.initial).map (fun s => (s.arrays 1,s.arrays 2)) ==
      some (#[],#[23,0,0,0]) do throw (IO.userError "branch fallback lost FIFO optimization")
  IO.println "Real SMT unified compiler: 8 kernels x 2 IRs x 3 channel queries, four-stage execution/control passed; billion-count compilation and branched fallback passed"
