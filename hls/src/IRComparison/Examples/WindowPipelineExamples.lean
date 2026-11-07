import IRComparison.Examples.NativeWindowExamples
import IRComparison.Memory.WindowPipeline

namespace IRComparison.WindowPipelineExamples
open NativeWindowExamples WindowPipeline
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- The second stage consumes the first stage's output, not the original input. -/
def consumer (i _x _y : Int) (s : State) : Option State := do
  let a ← (s.arrays 1)[i.toNat]?
  let b ← (s.arrays 1)[(i+1).toNat]?
  s.write 2 i (a+b)

hls_window consumer as downstream

def firstI := taps.imperativeStage 13 0 0 1 3 ascending
def secondI := downstream.imperativeStage 13 1 0 1 2 [0,1,2]
def firstF := taps.functionalStage 13 0 0 1 3 ascending
def secondF := downstream.functionalStage 13 1 0 1 2 [0,1,2]

def stagesI := [firstI,secondI]
def stagesF := [firstF,secondF]

example : (eval 0 0 stagesI initial).map (fun s => s.arrays 2) =
    some #[21,27,0,0,0,0,0,0,0,0,0,0,0] := by decide +kernel
example : (eval 0 0 stagesF initial).map (fun s => s.arrays 2) =
    some #[21,27,0,0,0,0,0,0,0,0,0,0,0] := by decide +kernel

-- Boundary queues are computed from initialized arrays, not hand-provided values.
example : firstI.queue initial = some [1,2,3,4,5,6,7,8,9,10,11,12,13] := by decide +kernel
example : firstI.Ready initial := by unfold Stage.Ready; decide +kernel
example : firstF.Ready initial := by unfold Stage.Ready; decide +kernel

def middle := (firstI.source 0 0 initial).get (by decide +kernel)
example : secondI.queue middle = some [9,12,15] := by decide +kernel
example : secondI.Ready middle := by unfold Stage.Ready; decide +kernel

theorem stages_ready : Ready 0 0 stagesI initial := by
  constructor
  · exact (by unfold Stage.Ready; decide +kernel : firstI.Ready initial)
  · intro t ht
    have hm : firstI.source 0 0 initial = some middle := rfl
    rw [hm] at ht
    cases ht
    constructor
    · exact (by unfold Stage.Ready; decide +kernel : secondI.Ready middle)
    · intro _ _; trivial

theorem stages_correct : eval 0 0 stagesI initial = source 0 0 stagesI initial :=
  eval_correct stagesI initial stages_ready

-- Incompatible FIFO order retains the window; the following stage still executes.
def retained := imperative (backwards.imperativeWindow 13 0 0 1 3 ascending)
example : retained.fifo = false := by decide +kernel
example : (eval 0 0 [retained,secondI] initial).map (fun s => s.arrays 2) =
    some #[63,57,0,0,0,0,0,0,0,0,0,0,0] := by decide +kernel

end IRComparison.WindowPipelineExamples
