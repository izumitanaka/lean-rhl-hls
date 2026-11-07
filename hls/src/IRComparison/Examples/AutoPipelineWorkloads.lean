import IRComparison.Examples.AutoPipelineExamples
import IRComparison.Examples.StreamWorkloads

namespace IRComparison.AutoPipelineWorkloads
open WindowPipeline WindowWorkloads

#eval show IO Unit from do
  for (w,(start,stride,count)) in workloads.zip StreamWorkloads.traversals do
    let order := (List.range count).map (fun n => start + stride * Int.ofNat n)
    let sinkI := StreamWorkloads.sink.imperativeStage 64 1 start stride count order
    let sinkF := StreamWorkloads.sink.functionalStage 64 1 start stride count order
    let pi := AutoPipeline.compile [2] (fun _ => 64) [w.imperative,sinkI]
    let pf := AutoPipeline.compile [2] (fun _ => 64) [w.functional,sinkF]
    unless pi.channels == [(0,1)] && pf.channels == pi.channels do
      throw (IO.userError s!"{w.name}: automatic decisions differ or channel missed")
    let expected := (source 0 0 [w.imperative,sinkI] initial).map (fun s => s.arrays 2)
    unless expected.isSome do throw (IO.userError s!"{w.name}: invalid reference")
    unless (pi.eval 0 0 initial).map (fun s => s.arrays 2) == expected &&
        (pf.eval 0 0 initial).map (fun s => s.arrays 2) == expected do
      throw (IO.userError s!"{w.name}: automatic pipeline output mismatch")
    for plan in [AutoPipelineControl.lower pi,AutoPipelineControl.lower pf] do
      match AutoPipelineControl.run 0 0 40000 (.start plan initial) with
      | .stopped result =>
        unless result.map (fun s => s.arrays 2) == expected do
          throw (IO.userError s!"{w.name}: automatic control mismatch")
      | _ => throw (IO.userError s!"{w.name}: insufficient execution steps")
  IO.println "8 reference kernels x 2 IRs: automatic pair/channel discovery, public outputs and control passed"

end IRComparison.AutoPipelineWorkloads
