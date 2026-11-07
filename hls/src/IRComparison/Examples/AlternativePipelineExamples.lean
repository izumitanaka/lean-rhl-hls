import IRComparison.Memory.PipelineCompilerControl
import IRComparison.Examples.AlternativeExamples

namespace IRComparison.AlternativePipelineExamples
open AlternativeExamples
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def consume (_i _x _y : Int) (s : State) : Option State := do
  let a ← (s.arrays 1)[0]?
  let b ← (s.arrays 1)[3]?
  s.write 2 0 (a+b)
hls_window consume as sink

def firstI := native.imperativeStage 4 0 0 1 1 []
def firstF := native.functionalStage 4 0 0 1 1 []
def lastI := sink.imperativeStage 4 1 0 1 1 [0,3]
def lastF := sink.functionalStage 4 1 0 1 1 [0,3]
def optimizedI := PipelineCompiler.compile [2] (fun _ => 4) [firstI,lastI]
def optimizedF := PipelineCompiler.compile [2] (fun _ => 4) [firstF,lastF]

example : optimizedI.channels = [(0,1)] := by decide +kernel
example : optimizedF.channels = [(0,1)] := by decide +kernel
example : (optimizedI.eval 10 0 initial).map (fun s => (s.arrays 1,s.arrays 2)) = some (#[],#[23,0,0,0]) := by decide +kernel
example : (optimizedI.eval 10 1 initial).map (fun s => (s.arrays 1,s.arrays 2)) = some (#[],#[23,0,0,0]) := by decide +kernel
example : (optimizedF.eval 10 0 initial).map (fun s => (s.arrays 1,s.arrays 2)) = some (#[],#[23,0,0,0]) := by decide +kernel
example : (optimizedF.eval 10 1 initial).map (fun s => (s.arrays 1,s.arrays 2)) = some (#[],#[23,0,0,0]) := by decide +kernel

def observeControl : PipelineCompilerControl.Config → Option (Option (Array Int × Array Int))
  | .stopped r => some (r.map (fun s => (s.arrays 1,s.arrays 2)))
  | _ => none
#eval show IO Unit from do
  for code in [PipelineCompilerControl.lower optimizedI,PipelineCompilerControl.lower optimizedF] do
    for branch in [0,1] do
      unless observeControl (PipelineCompilerControl.run 10 branch 1000
          (.start code initial)) == some (some (#[],#[23,0,0,0])) do
        throw (IO.userError "global alternative control mismatch")

theorem native_correct (s : State) (layout : PipelineShapes.Layout (fun _ => 4) s)
    (ready : WindowPipeline.Ready x y [firstI,lastI] s) :
    (optimizedI.eval x y s).map (PipelineUse.observe [2]) =
      (WindowPipeline.source x y [firstI,lastI] s).map (PipelineUse.observe [2]) :=
  optimizedI.correct s layout ready

end IRComparison.AlternativePipelineExamples
