import IRComparison.Memory.AutoPipelineControl
import IRComparison.Examples.StreamFusionExamples

namespace IRComparison.AutoPipelineExamples
open WindowPipelineExamples NativeWindowExamples WindowPipeline
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def sizes : Nat → Nat := fun _ => 13

def third (i _x _y : Int) (s : State) : Option State := do
  let v ← (s.arrays 2)[i.toNat]?
  s.write 3 i (v+10)
def fourth (i _x _y : Int) (s : State) : Option State := do
  let v ← (s.arrays 3)[i.toNat]?
  s.write 4 i (v*2)
def marker (_i _x _y : Int) (s : State) : Option State := s.write 5 0 5
def anotherReader (i _x _y : Int) (s : State) : Option State := do
  let v ← (s.arrays 1)[i.toNat]?
  s.write 3 i (v+100)
hls_window third as stage3
hls_window fourth as stage4
hls_window marker as markerCode
hls_window anotherReader as shared

def thirdI := stage3.imperativeStage 13 2 0 1 2 [0,1]
def fourthI := stage4.imperativeStage 13 3 0 1 2 [0,1]
def thirdF := stage3.functionalStage 13 2 0 1 2 [0,1]
def fourthF := stage4.functionalStage 13 3 0 1 2 [0,1]
def prefixI := markerCode.imperativeStage 13 0 0 1 1 []
def extraReader := shared.imperativeStage 13 1 0 1 2 [0,1,2]

def pipelineI := [firstI,secondI,thirdI,fourthI]
def pipelineF := [firstF,secondF,thirdF,fourthF]
-- Only the public output and allocation layout are specified. No pair or
-- private-array annotation is supplied to the pass.
def optimizedI := AutoPipeline.compile [4] sizes pipelineI
def optimizedF := AutoPipeline.compile [4] sizes pipelineF

example : optimizedI.channels = [(0,1),(2,3)] := by decide +kernel
example : optimizedF.channels = [(0,1),(2,3)] := by decide +kernel
example : (optimizedI.eval 0 0 initial).map (fun s => (s.arrays 1,s.arrays 3,s.arrays 4)) =
    some (#[],#[],#[62,74,0,0,0,0,0,0,0,0,0,0,0]) := by decide +kernel
example : (optimizedF.eval 0 0 initial).map (fun s => (s.arrays 1,s.arrays 3,s.arrays 4)) =
    some (#[],#[],#[62,74,0,0,0,0,0,0,0,0,0,0,0]) := by decide +kernel

-- Discovery need not start at stage 0.
def later := AutoPipeline.compile [2,5] sizes [prefixI,firstI,secondI]
example : later.channels = [(1,1)] := by decide +kernel
example : (later.eval 0 0 initial).map (fun s => ((s.arrays 5)[0]?,s.arrays 2)) =
    some (some 5,#[21,27,0,0,0,0,0,0,0,0,0,0,0]) := by decide +kernel

-- A publicly returned intermediate array must remain materialized.
def publicIntermediate := AutoPipeline.compile [1,2] sizes [firstI,secondI]
example : publicIntermediate.channels = [] := by decide +kernel
example : (publicIntermediate.eval 0 0 initial).map (fun s => s.arrays 1) =
    some #[9,12,15,0,0,0,0,0,0,0,0,0,0] := by decide +kernel

-- A third reader is detected even though its reads have already become FIFO loads.
def sharedIntermediate := AutoPipeline.compile [2,3] sizes [firstI,secondI,extraReader]
example : sharedIntermediate.channels = [] := by decide +kernel
example : (sharedIntermediate.eval 0 0 initial).map (fun s => s.arrays 3) =
    some #[109,112,0,0,0,0,0,0,0,0,0,0,0] := by decide +kernel

-- The automatic pass inherits conservative communication-order checking.
def incompatible := AutoPipeline.compile [2] sizes [StreamFusionExamples.reverseProducer,secondI]
example : incompatible.channels = [] := by decide +kernel

-- A non-primary read in another stage's body must also block elimination.
def readsBoth (i _x _y : Int) (s : State) : Option State := do
  let a ← (s.arrays 2)[i.toNat]?
  let b ← (s.arrays 1)[i.toNat]?
  s.write 3 i (a+b)
hls_window readsBoth as both

def indirectUser := both.imperativeStage 13 2 0 1 2 [0,1]
def sharedBody := AutoPipeline.compile [3] sizes [firstI,secondI,indirectUser]
example : sharedBody.channels = [(1,2)] := by decide +kernel
example : publicIntermediate.decisions.head? = some (0,.publicArray 1) := by decide +kernel
example : sharedBody.decisions.head? = some (0,.suffixNotProvedUnused 1) := by decide +kernel

/-- General correctness for this pipeline: arbitrary data, not just fixtures. -/
theorem pipeline_correct (s : State) (layout : PipelineShapes.Layout sizes s)
    (ready : Ready x y pipelineI s) :
    (optimizedI.eval x y s).map (PipelineUse.observe [4]) =
      (WindowPipeline.source x y pipelineI s).map (PipelineUse.observe [4]) :=
  optimizedI.correct s layout ready

theorem two_routes_agree (s : State) (layout : PipelineShapes.Layout sizes s)
    (ri : Ready x y pipelineI s) (rf : Ready x y pipelineF s) :
    (optimizedI.eval x y s).map (PipelineUse.observe [4]) =
      (optimizedF.eval x y s).map (PipelineUse.observe [4]) := by
  rw [optimizedI.correct s layout ri,optimizedF.correct s layout rf]
  rfl

def observedControl : AutoPipelineControl.Config → Option (Option (Array Int))
  | .stopped r => some (r.map (fun s => s.arrays 4))
  | _ => none

example : observedControl (AutoPipelineControl.run 0 0 5000
    (.start (AutoPipelineControl.lower optimizedI) initial)) =
    some (some #[62,74,0,0,0,0,0,0,0,0,0,0,0]) := by decide +kernel
example : observedControl (AutoPipelineControl.run 0 0 5000
    (.start (AutoPipelineControl.lower optimizedF) initial)) =
    some (some #[62,74,0,0,0,0,0,0,0,0,0,0,0]) := by decide +kernel

end IRComparison.AutoPipelineExamples
