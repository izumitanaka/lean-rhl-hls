import IRComparison.Memory.CompactFusionControl
import IRComparison.Memory.PipelineShapes
import IRComparison.Examples.WindowPipelineExamples

namespace IRComparison.CompactFusionExamples
open NativeWindowExamples WindowPipelineExamples
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def firstI := (taps.imperativeCompactWindow 13 0 0 1 3).code
def secondI := (downstream.imperativeCompactWindow 13 1 0 1 2).code
def firstF := (taps.functionalCompactWindow 13 0 0 1 3).code
def secondF := (downstream.functionalCompactWindow 13 1 0 1 2).code

def planI := (CompactFusion.compile 0 1 13 firstI secondI).get (by decide +kernel)
def planF := (CompactFusion.compile 0 1 13 firstF secondF).get (by decide +kernel)
example : (planI.eval 0 0 initial).map (fun s => (s.arrays 1,s.arrays 2)) =
    some (#[],#[21,27,0,0,0,0,0,0,0,0,0,0,0]) := by decide +kernel
example : (planF.eval 0 0 initial).map (fun s => (s.arrays 1,s.arrays 2)) =
    some (#[],#[21,27,0,0,0,0,0,0,0,0,0,0,0]) := by decide +kernel

-- This compiles the complete two-stage memory-eliminating transform without
-- allocating a list of iterations, writes, or channel addresses.
def largeI := (taps.imperativeCompactWindow 1000000004 0 0 1 1000000000).code
def largeConsumer := (downstream.imperativeCompactWindow 1000000004 1 0 1 999999999).code
def billion := (CompactFusion.compile 0 1 1000000004 largeI largeConsumer).get (by decide +kernel)
example : (billion.sender.code.count,billion.receiver.code.count,billion.sender.code.refill.length,billion.receiver.code.refill.length) =
    (1000000000,999999999,5,2) := by decide +kernel

-- Repeated writes cannot silently be turned into a FIFO stream.
example : (SymbolicProducerLoop.compile 1 13
    (SymbolicWindowLoop.direct (.store 1 (.lit 0) .index) 0 1 3)).isSome = false := by decide +kernel

-- A constant output address is valid for a single iteration.
example : (SymbolicProducerLoop.compile 1 13
    (SymbolicWindowLoop.direct (.store 1 (.lit 0) .index) 0 1 1)).isSome = true := by decide +kernel

theorem native_correct (s : State) (h0 : (s.arrays 0).size = 13) (h1 : (s.arrays 1).size = 13) (x y : Int) :
    planI.eval x y s = (do
      let t ← Source.iterate (fun i => dilated i x y) 1 3 0 s
      Source.iterate (fun i => consumer i x y) 1 2 0 t).map (StreamConsumer.erase 1) := by
  rw [planI.correct s h1 x y]
  unfold CompactFusion.source
  have hp := taps.imperativeCompactWindow_correct 13 0 0 1 3 s h0 x y
  change firstI.eval (arrayInput (s.arrays 0)) x y s = _ at hp
  rw [hp]
  cases hs : Source.iterate (fun i => dilated i x y) 1 3 0 s with
  | none => rfl
  | some t =>
    have hsize : (t.arrays 1).size = 13 := by
      have shape := PipelineShapes.stage_same WindowPipelineExamples.firstI
        ⟨h0,by intro _; decide +kernel⟩ hs
      exact (shape 1).symm.trans h1
    simp only [bind,Option.bind]
    rw [show secondI.eval (arrayInput (t.arrays 1)) x y t = Source.iterate (fun i => consumer i x y) 1 2 0 t from
      downstream.imperativeCompactWindow_correct 13 1 0 1 2 t hsize x y]

end IRComparison.CompactFusionExamples
