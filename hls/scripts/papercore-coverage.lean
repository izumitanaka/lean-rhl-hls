import IRComparison.Examples.UnifiedPipelineExamples

open IRComparison
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def produce (i _x _y : Int) (s : State) : Option State := s.write 1 i (i*i)
def marker (_i _x _y : Int) (s : State) : Option State := s.write 3 0 7
def consume (i _x _y : Int) (s : State) : Option State := do
  let v ← (s.arrays 1)[i.toNat]?
  s.write 2 i v
hls_window produce as producer
hls_window marker as independent
hls_window consume as consumer

def initial : State := ⟨fun _ => 0, fun _ => Array.replicate 3 0⟩
def main : IO Unit := do
  for functional in [false,true] do
    let p := if functional then producer.functionalKernel 3 0 0 1 3 (fun _ => [])
      else producer.imperativeKernel 3 0 0 1 3 (fun _ => [])
    let m := if functional then independent.functionalKernel 3 0 0 1 1 (fun _ => [])
      else independent.imperativeKernel 3 0 0 1 1 (fun _ => [])
    let c := if functional then consumer.functionalKernel 3 1 0 1 3 (fun _ => [0,1,2])
      else consumer.imperativeKernel 3 1 0 1 3 (fun _ => [0,1,2])
    for separated in [false,true] do
      let ks := if separated then [p,m,c] else [p,c]
      let plan ← UnifiedPipeline.compileWithSMT [2,3] (fun _ => 3) ks
        (System.FilePath.mk s!"artifacts/papercore-coverage/{functional}/{separated}")
      let some result := plan.eval 0 0 initial | throw (IO.userError "execution failed")
      unless result.arrays 2 == #[0,1,4] do throw (IO.userError "output mismatch")
      unless !separated || result.arrays 3 == #[7,0,0] do throw (IO.userError "side effect lost")
      let eliminated := (result.arrays 1).isEmpty
      unless eliminated do throw (IO.userError "coverage expectation changed")
      IO.println s!"functional={functional}, separated={separated}: private array eliminated={eliminated}; outputs correct"
