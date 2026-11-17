import IRComparison.Memory.FunctionalSymbolicLoop
import IRComparison.Examples.NativeWindowExamples

namespace IRComparison.SymbolicWindowExamples
open NativeWindowExamples
set_option maxRecDepth 16384

def forward := (SymbolicWindowLoop.compile 13 0 taps.imperativeBody 0 1 3).get (by decide +kernel)
def reverse := (SymbolicWindowLoop.compile 13 0 taps.imperativeBody 2 (-1) 3).get (by decide +kernel)
def strided := (SymbolicWindowLoop.compile 13 0 taps.imperativeBody 0 2 3).get (by decide +kernel)
def negative := (SymbolicWindowLoop.compile 13 0 backwards.imperativeBody 0 1 3).get (by decide +kernel)
def direct := (SymbolicWindowLoop.compile 13 0 sparse.imperativeBody 0 4 3).get (by decide +kernel)

example : (forward.code.eval (arrayInput (initial.arrays 0)) 0 0 initial).map (fun s => s.arrays 1) =
    some #[9,12,15,0,0,0,0,0,0,0,0,0,0] := by decide +kernel
example : (reverse.code.eval (arrayInput (initial.arrays 0)) 0 0 initial).map (fun s => s.arrays 1) =
    some #[9,12,15,0,0,0,0,0,0,0,0,0,0] := by decide +kernel
example : (strided.code.eval (arrayInput (initial.arrays 0)) 0 0 initial).map (fun s => s.arrays 1) =
    some #[9,0,15,0,21,0,0,0,0,0,0,0,0] := by decide +kernel
example : direct.buffered = false := by decide +kernel
example : negative.code.refill.length = 5 := by decide +kernel

-- Constructing this plan does not allocate one billion iteration blocks.
def billion := (SymbolicWindowLoop.compile 1000000004 0 taps.imperativeBody 0 1 1000000000).get (by decide +kernel)
example : (billion.code.count,billion.code.initial.length,billion.code.refill.length) =
    (1000000000,5,5) := by decide +kernel

-- A clamp crossing zero is not silently interpreted as affine arithmetic.
example : (SymbolicWindowLoop.compile 13 0 taps.imperativeBody (-1) 1 3).isSome = false := by decide +kernel

def functional := (FunctionalSymbolicLoop.compile 13 0 taps.functionalBody 0 1 3).get (by decide +kernel)
example : (functional.plan.code.eval (arrayInput (initial.arrays 0)) 0 0 initial).map (fun s => s.arrays 1) =
    some #[9,12,15,0,0,0,0,0,0,0,0,0,0] := by decide +kernel
example : functional.plan.code.initial = forward.code.initial := rfl
example : functional.plan.code.refill = forward.code.refill := rfl

def functionalBillion := (FunctionalSymbolicLoop.compile 1000000004 0 taps.functionalBody 0 1 1000000000).get (by decide +kernel)
example : (functionalBillion.plan.code.initial.length,functionalBillion.plan.code.refill.length) = (5,5) := by decide +kernel

-- The public entry proves correspondence to the actual named Lean function.
theorem native_correct (s : State) (sized : (s.arrays 0).size = 13) (x y : Int) :
    (taps.imperativeCompactWindow 13 0 0 1 3).code.eval (arrayInput (s.arrays 0)) x y s =
      Source.iterate (fun i => dilated i x y) 1 3 0 s :=
  taps.imperativeCompactWindow_correct 13 0 0 1 3 s sized x y

theorem routes_agree (size array : Nat) (start stride : Int) (count : Nat)
    (s : State) (sized : (s.arrays array).size = size) (x y : Int) :
    (taps.imperativeCompactWindow size array start stride count).code.eval (arrayInput (s.arrays array)) x y s =
    (taps.functionalCompactWindow size array start stride count).code.eval (arrayInput (s.arrays array)) x y s := by
  rw [taps.imperativeCompactWindow_correct size array start stride count s sized x y,
      taps.functionalCompactWindow_correct size array start stride count s sized x y]

example : SymbolicWindowControl.run forward.code (arrayInput (initial.arrays 0)) 0 0 1000 (.start initial) =
    .stopped (Source.iterate (fun i => dilated i 0 0) 1 3 0 initial) := by
  -- Config contains State functions: reduce the finite machine, then reflexivity.
  rfl

example : (taps.imperativeCompactWindow 13 0 (-1) 1 3).code.eval (arrayInput (initial.arrays 0)) 0 0 initial =
    Source.iterate (fun i => dilated i 0 0) 1 3 (-1) initial := by
  exact taps.imperativeCompactWindow_correct 13 0 (-1) 1 3 initial (by rfl) 0 0

end IRComparison.SymbolicWindowExamples
