import IRComparison.Memory.WindowTransport
import IRComparison.Frontend.LeanWindowCommand

namespace IRComparison.NativeWindowExamples
open Lean Elab Command
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

def dilated (i _x _y : Int) (s : State) : Option State := do
  let a ← (s.arrays 0)[i.toNat]?
  let b ← (s.arrays 0)[(i+2).toNat]?
  let c ← (s.arrays 0)[(i+4).toNat]?
  s.write 1 i (a+b+c)

def negativeScale (i _x _y : Int) (s : State) : Option State := do
  let a ← (s.arrays 0)[(8-i).toNat]?
  let b ← (s.arrays 0)[(10-i).toNat]?
  let c ← (s.arrays 0)[(12-i).toNat]?
  s.write 1 i (a+b+c)

def pair (i _x _y : Int) (s : State) : Option State := do
  let a ← (s.arrays 0)[i.toNat]?
  let b ← (s.arrays 0)[(i+2).toNat]?
  s.write 1 i (a+b)

def conditional (i flag _y : Int) (s : State) : Option State := do
  if flag != 0 then
    let a ← (s.arrays 0)[i.toNat]?
    let b ← (s.arrays 0)[(i+4).toNat]?
    s.write 1 i (a+b)
  else
    let a ← (s.arrays 0)[(i+2).toNat]?
    s.write 1 i a

hls_window dilated as taps
hls_window negativeScale as backwards
hls_window pair as sparse
hls_window conditional as branched

def initial : State := ⟨fun _ => 0,fun a => if a = 0 then #[1,2,3,4,5,6,7,8,9,10,11,12,13] else Array.replicate 13 0⟩
def ascending : List Int := (List.range 13).map Int.ofNat

def plan := (NativeWindowPlan.prepare 13 0 taps.imperativeBody 1 3 0 []).get (by decide +kernel)
example : plan.reads = [0,1,2,3,4,5,6] := by decide +kernel
example : (NativeWindowPlan.evalI (arrayInput (initial.arrays 0)) 0 0 plan.imperative [] initial).map (fun s => s.arrays 1) =
    some #[9,12,15,0,0,0,0,0,0,0,0,0,0] := by decide +kernel
example : (NativeWindowPlan.evalF (arrayInput (initial.arrays 0)) 0 0 plan.functional [] initial).map (fun s => s.arrays 1) =
    some #[9,12,15,0,0,0,0,0,0,0,0,0,0] := by decide +kernel

def channel := WindowTransport.compile 13 0 taps.imperativeBody 1 3 0 ascending
example : channel.isFIFO = true := by decide +kernel
example : channel.hasBuffer = true := by decide +kernel
example : (channel.eval (initial.arrays 0) 0 0 initial (initial.arrays 0).toList).map (fun s => s.arrays 1) =
    some #[9,12,15,0,0,0,0,0,0,0,0,0,0] := by decide +kernel

-- Retained windows with a two-element refill rather than one.
def strided := (NativeWindowPlan.prepare 13 0 taps.imperativeBody 2 3 0 []).get (by decide +kernel)
example : strided.reads = [0,1,2,3,4,5,6,7,8] := by decide +kernel

-- Negative traversal and a negative address coefficient both produce descending reads.
def reversePlan := (NativeWindowPlan.prepare 13 0 taps.imperativeBody (-1) 3 2 []).get (by decide +kernel)
example : reversePlan.reads = [6,5,4,3,2,1,0] := by decide +kernel
def negativePlan := (NativeWindowPlan.prepare 13 0 backwards.imperativeBody 1 3 0 []).get (by decide +kernel)
example : negativePlan.reads = [12,11,10,9,8,7,6] := by decide +kernel
def incompatible := WindowTransport.compile 13 0 backwards.imperativeBody 1 3 0 ascending
example : incompatible.isFIFO = false := by decide +kernel
example : incompatible.hasBuffer = true := by decide +kernel

-- No reuse: omit the contiguous window and explicitly discard skipped FIFO tokens.
def direct := WindowTransport.compile 13 0 sparse.imperativeBody 4 3 0 ascending
example : direct.isFIFO = true := by decide +kernel
example : direct.hasBuffer = false := by decide +kernel
example : (direct.eval (initial.arrays 0) 0 0 initial (initial.arrays 0).toList).map (fun s => s.arrays 1) =
    some #[4,0,0,0,12,0,0,0,20,0,0,0,0] := by decide +kernel
example : (WindowFIFO.route [.memory 0,.memory 2,.memory 4] [0,1,2,3,4,5]).map
    (fun r => (r.code,r.remaining)) = some ([.take 0,.take 1,.take 1],[5]) := by decide +kernel

-- Same arbitrary branch body, with all speculative window cells proved in bounds.
def branchPlan := (NativeWindowPlan.prepare 13 0 branched.imperativeBody 1 3 0 []).get (by decide +kernel)
example : (NativeWindowPlan.evalI (arrayInput (initial.arrays 0)) 0 0 branchPlan.imperative [] initial).map (fun s => s.arrays 1) =
    some #[3,4,5,0,0,0,0,0,0,0,0,0,0] := by decide +kernel
example : (NativeWindowPlan.evalI (arrayInput (initial.arrays 0)) 1 0 branchPlan.imperative [] initial).map (fun s => s.arrays 1) =
    some #[6,8,10,0,0,0,0,0,0,0,0,0,0] := by decide +kernel
-- Coverage failure is not a source-program rejection.
example : (NativeWindowPlan.prepare 3 0 taps.imperativeBody 1 3 0 []).isSome = false := by decide +kernel

/-- This general theorem uses the actual named Lean source, not a hand-written
    replacement specification for the example. -/
theorem dilated_correct (size count : Nat) (start stride : Int) (producer : List Int)
    (s : State) (x y : Int) (values : List Int) (hs : (s.arrays 0).size = size)
    (hc : (WindowTransport.compile size 0 taps.imperativeBody stride count start producer).Contract (s.arrays 0) values) :
    (WindowTransport.compile size 0 taps.imperativeBody stride count start producer).eval (s.arrays 0) x y s values =
      Source.iterate (fun i => dilated i x y) stride count start s := by
  rw [WindowTransport.Selected.correct _ s hs x y values hc]
  exact Source.iterate_congr _ _ (fun i t => taps.imperativeBody_correct i x y t) stride count start s

def observe : WindowControl.Config → Option (Option (Array Int))
  | .stopped result _ => some (result.map (fun s => s.arrays 1))
  | _ => none

example : observe (WindowControl.run (arrayInput (initial.arrays 0)) 0 0 1000
    (.start (WindowControl.lower channel.code) [] initial (initial.arrays 0).toList)) =
    some (some #[9,12,15,0,0,0,0,0,0,0,0,0,0]) := by decide +kernel
example : observe (WindowControl.run (arrayInput (initial.arrays 0)) 0 0 1000
    (.start (WindowControl.lower direct.code) [] initial (initial.arrays 0).toList)) =
    some (some #[4,0,0,0,12,0,0,0,20,0,0,0,0]) := by decide +kernel
example : WindowControl.lower (taps.imperativeWindow 13 0 0 1 3 ascending).code =
    WindowControl.lower (taps.functionalWindow 13 0 0 1 3 ascending).code := by rfl
example : WindowControl.lower (branched.imperativeWindow 13 0 0 1 3 ascending).code =
    WindowControl.lower (branched.functionalWindow 13 0 0 1 3 ascending).code := by rfl

example : (WindowTransport.compileWithReason 13 0 backwards.imperativeBody 1 3 0 ascending).2 =
    .supplyOrderMismatch true := by decide +kernel
example : (WindowTransport.compileWithReason 3 0 taps.imperativeBody 1 3 0 ascending).2 =
    .windowUnavailable := by decide +kernel

end IRComparison.NativeWindowExamples
