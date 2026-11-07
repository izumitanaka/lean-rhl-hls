import IRComparison.Memory.StreamFusionControl
import IRComparison.Examples.WindowPipelineExamples

namespace IRComparison.StreamFusionExamples
open WindowPipelineExamples NativeWindowExamples WindowPipeline
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def fusedI := (StreamFusion.compile firstI secondI 1 13).get (by decide +kernel)
def fusedF := (StreamFusion.compile firstF secondF 1 13).get (by decide +kernel)

-- Actual deletion: no materialized values remain in intermediate array 1.
-- Array 2 is the public output; array 1 is private to this two-stage region.
example : (fusedI.eval 0 0 initial).map (fun s => (s.arrays 1,s.arrays 2)) =
    some (#[],#[21,27,0,0,0,0,0,0,0,0,0,0,0]) := by decide +kernel
example : (fusedF.eval 0 0 initial).map (fun s => (s.arrays 1,s.arrays 2)) =
    some (#[],#[21,27,0,0,0,0,0,0,0,0,0,0,0]) := by decide +kernel

/-- Whole-region guarantee for arbitrary inputs satisfying size/initialization,
    including failures. The only hidden component is the private channel array. -/
theorem whole_region (s : State) (ready : firstI.Ready s) (size : (s.arrays 1).size = 13) (x y : Int) :
    fusedI.eval x y s = ((do secondI.source x y (← firstI.source x y s))).map (StreamConsumer.erase 1) :=
  fusedI.correct s ready size x y

-- A producer using memory for its input can still stream its output directly.
def reverseProducer := imperative (taps.imperativeWindow 13 0 2 (-1) 3 ascending)
def reverseConsumer := imperative (downstream.imperativeWindow 13 1 1 (-1) 2 [2,1,0])
def reverse := (StreamFusion.compile reverseProducer reverseConsumer 1 13).get (by decide +kernel)
example : reverseProducer.fifo = false := by decide +kernel
example : reverse.producerCode.after = [2,1,0] := by decide +kernel
example : (reverse.eval 0 0 initial).map (fun s => (s.arrays 1,s.arrays 2)) =
    some (#[],#[21,27,0,0,0,0,0,0,0,0,0,0,0]) := by decide +kernel

-- No partial conversion when the supplied consumer order is incompatible.
example : (StreamFusion.compile reverseProducer secondI 1 13).isSome = false := by decide +kernel

-- Data-dependent branches may emit different values but agree on channel order.
def branchProducer := imperative (branched.imperativeWindow 13 0 0 1 3 ascending)
def branch := (StreamFusion.compile branchProducer secondI 1 13).get (by decide +kernel)
example : (branch.eval 0 0 initial).map (fun s => s.arrays 2) =
    some #[7,9,0,0,0,0,0,0,0,0,0,0,0] := by decide +kernel
example : (branch.eval 1 0 initial).map (fun s => s.arrays 2) =
    some #[14,18,0,0,0,0,0,0,0,0,0,0,0] := by decide +kernel

-- Duplicate writes cannot be claimed to match the final source array as a FIFO.
example : (StreamProducer.compile 0 1 13 []
    (.seq (.store 1 (.lit 0) (.lit 10)) (.store 1 (.lit 0) (.lit 20)))).isSome = false := by decide +kernel
-- A read of the eliminated array is not silently replaced with stale memory.
example : (StreamProducer.compile 0 1 13 []
    (.store 1 (.lit 0) (.read 1 (.lit 1)))).isSome = false := by decide +kernel
-- Out-of-bounds source writes cannot become successful sends.
example : (StreamProducer.compile 0 1 2 [] (.store 1 (.lit 2) (.lit 10))).isSome = false := by decide +kernel

example : (StreamFusion.select reverseProducer secondI 1 13).isFIFO = false := by decide +kernel
example : ((StreamFusion.select reverseProducer secondI 1 13).eval 0 0 initial).map (fun s => s.arrays 2) =
    some #[21,27,0,0,0,0,0,0,0,0,0,0,0] := by decide +kernel

def observeControl : StreamFusionControl.Config → Option (Option (Array Int × Array Int))
  | .stopped r => some (r.map fun s => (s.arrays 1,s.arrays 2))
  | _ => none

example : observeControl (StreamFusionControl.run 1 secondI.code (arrayInput (initial.arrays 0)) 0 0 2000
    (.producer (.start fusedI.producerCode.code [] (StreamConsumer.erase 1 initial) (initial.arrays 0).toList []))) =
    some (some (#[],#[21,27,0,0,0,0,0,0,0,0,0,0,0])) := by decide +kernel
example : observeControl (StreamFusionControl.run 1 secondF.code (arrayInput (initial.arrays 0)) 0 0 2000
    (.producer (.start fusedF.producerCode.code [] (StreamConsumer.erase 1 initial) (initial.arrays 0).toList []))) =
    some (some (#[],#[21,27,0,0,0,0,0,0,0,0,0,0,0])) := by decide +kernel

-- Several output writes per iteration: no single-send/filter pattern assumption.
def twoOutputs (i _x _y : Int) (s : State) : Option State := do
  let v ← (s.arrays 0)[i.toNat]?
  let t ← s.write 1 (2*i) v
  t.write 1 (2*i+1) (v+10)
def oneInput (i _x _y : Int) (s : State) : Option State := do
  let v ← (s.arrays 1)[i.toNat]?
  s.write 2 i (2*v)
hls_window twoOutputs as multi
hls_window oneInput as single

def multiProducer := multi.imperativeStage 13 0 0 1 3 ascending
def multiConsumer := single.imperativeStage 13 1 0 1 6 [0,1,2,3,4,5]
def multiFused := (StreamFusion.compile multiProducer multiConsumer 1 13).get (by decide +kernel)
example : multiFused.producerCode.after = [0,1,2,3,4,5] := by decide +kernel
example : (multiFused.eval 0 0 initial).map (fun s => (s.arrays 1,s.arrays 2)) =
    some (#[],#[2,22,4,24,6,26,0,0,0,0,0,0,0]) := by decide +kernel

-- Failure in the consumer must remain failure after the producer has sent.
def shortOutput : State := {initial with arrays := fun a => if a = 2 then #[] else initial.arrays a}
example : (fusedI.eval 0 0 shortOutput).isNone = true := by decide +kernel
example : (fusedF.eval 0 0 shortOutput).isNone = true := by decide +kernel
example : (StreamProducer.compile 0 1 13 [] (.branch .left
    (.store 1 (.lit 0) (.lit 10)) (.store 1 (.lit 1) (.lit 20)))).isSome = false := by decide +kernel

/-- The theorem states public output equality directly in terms of the
    original named Lean functions, for arbitrary input values and arguments. -/
theorem public_output_correct (s : State) (ready : firstI.Ready s)
    (size : (s.arrays 1).size = 13) (x y : Int) :
    (fusedI.eval x y s).map (fun t => t.arrays 2) =
      ((do
        let t ← Source.iterate (fun i => dilated i x y) 1 3 0 s
        Source.iterate (fun i => WindowPipelineExamples.consumer i x y) 1 2 0 t)).map (fun (t : State) => t.arrays 2) :=
  fusedI.observe_correct s ready size x y (fun t => t.arrays 2) (by intro t; rfl)

end IRComparison.StreamFusionExamples
