import IRComparison.Memory.CompactChain
import IRComparison.Examples.AutoPipelineExamples

namespace IRComparison.CompactChainExamples
open NativeWindowExamples WindowPipelineExamples AutoPipelineExamples
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def firstI := taps.imperativeCompactStage 13 0 0 1 3
def secondI := downstream.imperativeCompactStage 13 1 0 1 2
def thirdI := stage3.imperativeCompactStage 13 2 0 1 2
def fourthI := stage4.imperativeCompactStage 13 3 0 1 2
def firstF := taps.functionalCompactStage 13 0 0 1 3
def secondF := downstream.functionalCompactStage 13 1 0 1 2
def thirdF := stage3.functionalCompactStage 13 2 0 1 2
def fourthF := stage4.functionalCompactStage 13 3 0 1 2

def planI := (CompactChain.compile [4] sizes firstI secondI [thirdI,fourthI]).get (by decide +kernel)
def planF := (CompactChain.compile [4] sizes firstF secondF [thirdF,fourthF]).get (by decide +kernel)
example : (planI.eval 0 0 initial).map (fun s => (s.arrays 1,s.arrays 2,s.arrays 3,s.arrays 4)) =
    some (#[],#[],#[],#[62,74,0,0,0,0,0,0,0,0,0,0,0]) := by decide +kernel
example : (planF.eval 0 0 initial).map (fun s => (s.arrays 1,s.arrays 2,s.arrays 3,s.arrays 4)) =
    some (#[],#[],#[],#[62,74,0,0,0,0,0,0,0,0,0,0,0]) := by decide +kernel

def hugeFirst := taps.imperativeCompactStage 1000000004 0 0 1 1000000000
def hugeSecond := downstream.imperativeCompactStage 1000000004 1 0 1 999999999
def hugeThird := stage3.imperativeCompactStage 1000000004 2 0 1 999999999
def hugeFourth := stage4.imperativeCompactStage 1000000004 3 0 1 999999999
def billion := (CompactChain.compile [4] (fun _ => 1000000004) hugeFirst hugeSecond [hugeThird,hugeFourth]).get (by decide +kernel)
example : billion.sender.code.refill.length = 5 := by decide +kernel

theorem both_correct (s : State) (layout : PipelineShapes.Layout sizes s) (x y : Int) :
    (planI.eval x y s).map (PipelineUse.observe [4]) = (planF.eval x y s).map (PipelineUse.observe [4]) := by
  rw [planI.correct s layout,planF.correct s layout]
  rfl

-- Public and later-used arrays are not silently removed.
example : (CompactChain.compile [1,4] sizes firstI secondI [thirdI,fourthI]).isSome = false := by decide +kernel
example : (CompactChain.compile [3] sizes firstI secondI [shared.imperativeCompactStage 13 1 0 1 2]).isSome = false := by decide +kernel

end IRComparison.CompactChainExamples
