import IRComparison.Examples.StreamChainExamples
import IRComparison.Examples.StreamWorkloads

namespace IRComparison.StreamChainWorkloads
open WindowPipeline WindowWorkloads

#eval show IO Unit from do
  for (w,(start,stride,count)) in workloads.zip StreamWorkloads.traversals do
    let order := (List.range count).map (fun n => start + stride * Int.ofNat n)
    let sinkI := StreamWorkloads.sink.imperativeStage 64 1 start stride count order
    let sinkF := StreamWorkloads.sink.functionalStage 64 1 start stride count order
    let thirdI := AutoPipelineExamples.stage3.imperativeStage 64 2 start stride count order
    let thirdF := AutoPipelineExamples.stage3.functionalStage 64 2 start stride count order
    let fourthI := AutoPipelineExamples.stage4.imperativeStage 64 3 start stride count order
    let fourthF := AutoPipelineExamples.stage4.functionalStage 64 3 start stride count order
    let pi := PipelineCompiler.compile [4] (fun _ => 64) [w.imperative,sinkI,thirdI,fourthI]
    let pf := PipelineCompiler.compile [4] (fun _ => 64) [w.functional,sinkF,thirdF,fourthF]
    unless pi.channels == [(0,1),(1,2),(2,3)] && pf.channels == pi.channels do
      throw (IO.userError s!"{w.name}: automatic decisions differ or channel missed")
    let expected := (source 0 0 [w.imperative,sinkI,thirdI,fourthI] initial).map (fun s => (#[],#[],#[],s.arrays 4))
    unless expected.isSome do throw (IO.userError s!"{w.name}: invalid reference")
    unless (pi.eval 0 0 initial).map (fun s => (s.arrays 1,s.arrays 2,s.arrays 3,s.arrays 4)) == expected &&
        (pf.eval 0 0 initial).map (fun s => (s.arrays 1,s.arrays 2,s.arrays 3,s.arrays 4)) == expected do
      throw (IO.userError s!"{w.name}: automatic pipeline output mismatch")
    for plan in [PipelineCompilerControl.lower pi,PipelineCompilerControl.lower pf] do
      match PipelineCompilerControl.run 0 0 40000 (.start plan initial) with
      | .stopped result =>
        unless result.map (fun s => (s.arrays 1,s.arrays 2,s.arrays 3,s.arrays 4)) == expected do
          throw (IO.userError s!"{w.name}: automatic control mismatch")
      | _ => throw (IO.userError s!"{w.name}: insufficient execution steps")
  IO.println "8 reference kernels x 2 IRs: four-stage chain, all three intermediate arrays erased, public outputs and control passed"

end IRComparison.StreamChainWorkloads
