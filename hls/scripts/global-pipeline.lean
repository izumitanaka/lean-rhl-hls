import IRComparison.Examples.GlobalPipelineExamples
open IRComparison IRComparison.GlobalPipelineExamples

def main : IO Unit := do
  for functional in [false,true] do
    let branchKs := if functional then [
      AlternativeExamples.native.functionalKernel 4 0 0 1 1 (fun _ => []), independentKernel true,
      AlternativePipelineExamples.sink.functionalKernel 4 1 0 1 1 (fun _ => [0,3])]
      else [UnifiedPipelineExamples.branchKernels[0]'(by decide), independentKernel false,
        UnifiedPipelineExamples.branchKernels[1]'(by decide)]
    for (name,outputs,ks,expected) in [
      ("nonadjacent",[2,3],separated functional,[1]),
      ("interleaved",[2,3,6],kernels functional,[1,5]),
      ("intervening-read",[2,3],readBetween functional,[]),
      ("public-output",[1,2,3],publicOutput functional,[]),
      ("read-before-producer",[6],beforeProducer functional,[1]),
      ("nonadjacent-branch",[2,3],branchKs,[1])] do
      let p ← UnifiedPipeline.compileWithSMT outputs (fun _ => 4) ks
        (System.FilePath.mk s!"artifacts/global-pipeline/{name}/{functional}")
      unless policy p == expected do throw (IO.userError s!"{name}: policy {policy p}, expected {expected}")
      for flag in [0,1] do
        let original := CompactStage.source 10 flag (UnifiedPipeline.compactStages ks) initial
        let result := p.eval 10 flag initial
        unless result.map (fun s => outputs.map s.arrays) == original.map (fun s => outputs.map s.arrays) do
          throw (IO.userError s!"{name}: output mismatch")
        let some state := result | throw (IO.userError s!"{name}: failed")
        for a in expected do
          unless (state.arrays a).isEmpty do throw (IO.userError s!"{name}: array {a} retained")
        match UnifiedPipeline.run 10 flag 20000 (UnifiedPipeline.start (UnifiedPipeline.lower p) initial) with
        | .stopped actual =>
          unless actual.map (fun s => outputs.map s.arrays) == result.map (fun s => outputs.map s.arrays) do
            throw (IO.userError s!"{name}: control mismatch")
        | _ => throw (IO.userError s!"{name}: control did not finish")
      IO.println s!"{name}, functional={functional}: FIFO policy={policy p}; source/target/control agree for both branch outcomes"
