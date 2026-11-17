import IRComparison.Examples.CompactFusionExamples
import IRComparison.Memory.CompactFusionControl
open IRComparison IRComparison.CompactFusionExamples IRComparison.NativeWindowExamples

def main : IO Unit := do
  for ((producer,consumer),n) in [(firstI,secondI),(firstF,secondF)].zipIdx do
    let selected ← CompactFusion.selectWithSMT 0 1 13 producer consumer
      (System.FilePath.mk "artifacts/compact-fusion" / toString n)
    let .fifo plan := selected | throw (IO.userError "expected compact FIFO fusion")
    unless (selected.eval 0 0 initial).map (fun s => (s.arrays 1,s.arrays 2)) ==
        some (#[],#[21,27,0,0,0,0,0,0,0,0,0,0,0]) do throw (IO.userError "fused output differs")
    let control := CompactFusionControl.run 1 plan.sender.code plan.receiver.code
      (arrayInput (initial.arrays 0)) 0 0 10000 (.producer (.start (StreamConsumer.erase 1 initial)))
    match control with
    | .stopped result =>
      unless result.map (fun s => (s.arrays 1,s.arrays 2)) ==
          some (#[],#[21,27,0,0,0,0,0,0,0,0,0,0,0]) do throw (IO.userError "fused control differs")
    | _ => throw (IO.userError "fused control did not finish")
  let large ← CompactFusion.selectWithSMT 0 1 1000000004 largeI largeConsumer "artifacts/compact-fusion/billion"
  let .fifo large := large | throw (IO.userError "billion-count fusion did not compile")
  unless large.sender.code.refill.length == 5 && large.receiver.code.refill.length == 2 do
    throw (IO.userError "unexpected compact code size")
  IO.println "2 IRs -> compact producer -> real SMT candidate -> compact consumer -> erased middle array -> control passed; billion-iteration whole fusion compiled without expansion"
