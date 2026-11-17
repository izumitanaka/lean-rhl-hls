import IRComparison.Frontend.LeanOptimizedControlCommand
import IRComparison.Examples.ControlWorkloads

namespace IRComparison.OptimizedControlExamples
open Lean Elab Command
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- Adjacent-input filter with an output write on each iteration. -/
def filter (i x y : Int) (s : State) : Option State := s.write 0 i (x+y)
hls_optimized_control filter as filtered
hls_optimized_control LeanReadExamples.accumulate as accumulated
hls_optimized_control ControlWorkloads.branchJoin as joined

/-- Equal control code for all starts, strides, counts and offsets, including
    the branch where the optimizer retains two independent reads. -/
theorem filter_controls_agree (i d : Int) (n : Nat) (l r : Int) :
    filtered.imperativeOptimizedControl i d n l r = filtered.functionalOptimizedControl i d n l r := by
  exact ProgramControlIR.lower_optimizedLoop filtered.imperativeBody i d n l r

theorem accumulate_controls_agree (i d : Int) (n : Nat) (l r : Int) :
    accumulated.imperativeOptimizedControl i d n l r = accumulated.functionalOptimizedControl i d n l r := by
  exact ProgramControlIR.lower_optimizedLoop accumulated.imperativeBody i d n l r

theorem branch_controls_agree (i d : Int) (n : Nat) (l r : Int) :
    joined.imperativeOptimizedControl i d n l r = joined.functionalOptimizedControl i d n l r := by
  exact ProgramControlIR.lower_optimizedLoop joined.imperativeBody i d n l r

def initial : State := ⟨fun _ => 0,fun _ => #[0,0,0,0,0]⟩
def observe : ProgramControlIR.Config → Option (Option (Array Int))
  | .stopped r => some (r.map fun s => s.arrays 0)
  | _ => none

def simulate (code : List ProgramControlIR.Instr) (input : Array Int) (s : State := initial) :=
  observe (ProgramControlIR.run (arrayInput input) 500 (.running code s ProgramControlIR.initial))

example : simulate (filtered.imperativeOptimizedControl 0 1 3 0 1) #[1,2,3,4] =
    some (some #[3,5,7,0,0]) := by decide +kernel
example : simulate (filtered.functionalOptimizedControl 3 (-1) 3 0 (-1)) #[1,2,3,4] =
    some (some #[0,3,5,7,0]) := by decide +kernel
example : simulate (filtered.functionalOptimizedControl 0 2 2 0 2) #[1,2,3,4,5] =
    some (some #[4,0,8,0,0]) := by decide +kernel
example : simulate (filtered.imperativeOptimizedControl 0 0 3 0 0) #[7] =
    some (some #[14,0,0,0,0]) := by decide +kernel
-- No overlap: still two reads per iteration, and still certified.
example : simulate (filtered.imperativeOptimizedControl 0 1 2 0 2) #[1,2,3,4] =
    some (some #[4,6,0,0,0]) := by decide +kernel
-- Zero iterations perform no input read, even if the initial index is invalid.
example : simulate (filtered.functionalOptimizedControl (-5) (-2) 0 7 5) #[] =
    some (some #[0,0,0,0,0]) := by decide +kernel
-- First-read failure and refill failure remain failures.
example : simulate (filtered.imperativeOptimizedControl 0 1 3 0 1) #[] = some none := by decide +kernel
example : simulate (filtered.functionalOptimizedControl 0 1 3 0 1) #[1,2] = some none := by decide +kernel
-- Body failure: output memory is too short even though input reads succeed.
example : simulate (filtered.functionalOptimizedControl 0 1 3 0 1) #[1,2,3,4]
    ⟨fun _ => 0,fun _ => #[]⟩ = some none := by decide +kernel
-- A body may update the same array location on every iteration.
example : simulate (accumulated.imperativeOptimizedControl 0 1 3 0 1) #[1,2,3,4] =
    some (some #[6,0,0,0,0]) := by decide +kernel

/-- Observe reads made by the actual transition function, not by an IR evaluator. -/
def readTrace (input : Input) : Nat → ProgramControlIR.Config → List Int
  | 0,_ => []
  | fuel+1,c =>
    let here := match c with
      | .running (.readLeft o :: _) _ f => [f.index+o]
      | .running (.readRight o :: _) _ f => [f.index+o]
      | _ => []
    here ++ readTrace input fuel (ProgramControlIR.step input c)

example : readTrace (arrayInput #[1,2,3,4]) 500
    (.running (filtered.imperativeOptimizedControl 0 1 3 0 1) initial ProgramControlIR.initial) =
    [0,1,2,3] := by decide +kernel
example : readTrace (arrayInput #[1,2,3,4]) 500
    (.running (ProgramControlIR.lower (.loop 0 1 3 0 1 filtered.imperativeBody)) initial ProgramControlIR.initial) =
    [0,1,1,2,2,3] := by decide +kernel
example : readTrace (arrayInput #[1,2,3,4]) 500
    (.running (filtered.functionalOptimizedControl 3 (-1) 3 0 (-1)) initial ProgramControlIR.initial) =
    [3,2,1,0] := by decide +kernel
example : readTrace (arrayInput #[]) 500
    (.running (filtered.imperativeOptimizedControl 0 1 0 0 1) initial ProgramControlIR.initial) =
    [] := by decide +kernel
-- The successor iteration is not entered after a body failure.
example : readTrace (arrayInput #[1,2,3,4]) 500
    (.running (filtered.functionalOptimizedControl 0 1 3 0 1)
      ⟨fun _ => 0,fun _ => #[]⟩ ProgramControlIR.initial) = [0,1] := by decide +kernel

/-- Source register 0 is not the private retained value. Also checks program
    sequencing/branching around an optimized loop. -/
def composite : Imperative.Program := .seq (.effect (.assign 0 (.lit 1)))
  (.branch 0
    (.loop 0 1 3 0 1 (.seq (.assign 0 (.lit 99)) (.store 0 .index (.add .left .right))))
    (.effect (.store 0 (.lit 0) (.lit (-1)))))

example : simulate (ProgramControlIR.lower (Imperative.transform composite)) #[1,2,3,4] =
    some (some #[3,5,7,0,0]) := by decide +kernel
example : (match ProgramControlIR.run (arrayInput #[1,2,3,4]) 500
    (.running (ProgramControlIR.lower (Imperative.transform composite)) initial ProgramControlIR.initial) with
    | .stopped r => r.map fun s => s.regs 0 | _ => none) = some 99 := by decide +kernel
example : observe (ProgramControlIR.run (arrayInput #[1,2,3,4]) 1
    (.running (filtered.imperativeOptimizedControl 0 1 3 0 1) initial ProgramControlIR.initial)) =
    none := by decide +kernel

run_cmd do
  for name in [``filtered.imperativeOptimizedControl_correct, ``filtered.functionalOptimizedControl_correct,
      ``filtered.imperativeOptimizedControl_result_correct, ``filtered.functionalOptimizedControl_result_correct,
      ``accumulated.imperativeOptimizedControl_correct, ``accumulated.functionalOptimizedControl_correct,
      ``joined.imperativeOptimizedControl_correct, ``joined.functionalOptimizedControl_correct,
      ``filter_controls_agree, ``accumulate_controls_agree, ``branch_controls_agree] do
    for ax in (← collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected optimized controller assumption {ax} in {name}"

end IRComparison.OptimizedControlExamples
