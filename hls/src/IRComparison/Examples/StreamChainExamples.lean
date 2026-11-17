import IRComparison.Memory.PipelineCompilerControl
import IRComparison.Examples.AutoPipelineExamples

namespace IRComparison.StreamChainExamples
open AutoPipelineExamples NativeWindowExamples WindowPipelineExamples
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def chainI := PipelineCompiler.compile [4] sizes pipelineI
def chainF := PipelineCompiler.compile [4] sizes pipelineF
example : chainI.channels = [(0,1),(1,2),(2,3)] := by decide +kernel
example : chainF.channels = [(0,1),(1,2),(2,3)] := by decide +kernel
example : (chainI.eval 0 0 initial).map (fun s => (s.arrays 1,s.arrays 2,s.arrays 3,s.arrays 4)) =
    some (#[],#[],#[],#[62,74,0,0,0,0,0,0,0,0,0,0,0]) := by decide +kernel
example : (chainF.eval 0 0 initial).map (fun s => (s.arrays 1,s.arrays 2,s.arrays 3,s.arrays 4)) =
    some (#[],#[],#[],#[62,74,0,0,0,0,0,0,0,0,0,0,0]) := by decide +kernel

def three := PipelineCompiler.compile [3] sizes [firstI,secondI,thirdI]
example : three.channels = [(0,1),(1,2)] := by decide +kernel
example : (PipelineCompiler.compile [2,3] sizes [firstI,secondI,extraReader]).channels = [] := by decide +kernel
example : (PipelineCompiler.compile [1,4] sizes pipelineI).channels = [(1,2),(2,3)] := by decide +kernel
example : (PipelineCompiler.compile [3] sizes [firstI,secondI,indirectUser]).channels = [(1,2)] := by decide +kernel

theorem both_correct (s : State) (layout : PipelineShapes.Layout sizes s)
    (hi : WindowPipeline.Ready x y pipelineI s) (hf : WindowPipeline.Ready x y pipelineF s) :
    (chainI.eval x y s).map (PipelineUse.observe [4]) = (chainF.eval x y s).map (PipelineUse.observe [4]) := by
  rw [chainI.correct s layout hi,chainF.correct s layout hf]
  rfl

def observeControl : PipelineCompilerControl.Config → Option (Option (Array Int × Array Int × Array Int × Array Int))
  | .stopped r => some (r.map (fun s => (s.arrays 1,s.arrays 2,s.arrays 3,s.arrays 4)))
  | _ => none
-- Run concrete control traces as executable regression tests. The general
-- control correctness theorem is checked independently by the Lean kernel.
#eval show IO Unit from do
  for code in [PipelineCompilerControl.lower chainI,PipelineCompilerControl.lower chainF] do
    unless observeControl (PipelineCompilerControl.run 0 0 5000
        (.start code initial)) ==
        some (some (#[],#[],#[],#[62,74,0,0,0,0,0,0,0,0,0,0,0])) do
      throw (IO.userError "global chain control mismatch")

end IRComparison.StreamChainExamples
