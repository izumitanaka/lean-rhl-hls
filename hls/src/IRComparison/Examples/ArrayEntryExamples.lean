import IRComparison.Frontend.LeanArrayCommand

namespace IRComparison.ArrayEntryExamples
open Lean Elab Command

def squares (a : Array Int) : Array Int := a.map (fun z => z*z)
def localFunction (a : Array Int) : Array Int := a.map (fun z =>
  let square := fun n : Int => n*n
  square (z+1))
def conditional (a : Array Int) : Array Int := a.map (fun z => if z != 0 then z+3 else 9)

/-- Two elementwise processing stages, written without manually fusing maps. -/
def pipeline (a : Array Int) : Array Int :=
  (a.map (fun z => z-2)).map (fun z => z*z)
def threeStages (a : Array Int) : Array Int :=
  let shifted := a.map (fun z => z+1)
  let squared := shifted.map (fun z => z*z)
  squared.map (fun z => if z != 0 then z/2 else 7)

hls_array pipeline as pipelined
hls_array threeStages as staged
hls_array squares as squared
hls_array localFunction as shifted
hls_array conditional as branched

example : squared.imperative.eval #[-2,0,3] = some #[4,0,9] := by decide +kernel
example : squared.functional.eval #[-2,0,3] = some #[4,0,9] := by decide +kernel
example : shifted.imperative.eval #[-2,0,3] = some #[1,1,16] := by decide +kernel
example : branched.functional.eval #[-2,0,3] = some #[1,9,6] := by decide +kernel
example : squared.imperative.eval #[] = some #[] := by decide +kernel

example : squared.imperativeControl = squared.functionalControl := rfl
example : shifted.imperativeControl = shifted.functionalControl := rfl
example : branched.imperativeControl = branched.functionalControl := rfl

def observe : ArrayControlIR.Config → Option (Option ArrayControlIR.Result)
  | .stopped r => some r
  | _ => none

example : observe (ArrayControlIR.run 5 (.ready squared.imperativeControl #[-2,0,3])) =
    some (some (.array #[4,0,9])) := by decide +kernel
example : observe (ArrayControlIR.run 5 (.ready branched.functionalControl #[-2,0,3])) =
    some (some (.array #[1,9,6])) := by decide +kernel
example : observe (ArrayControlIR.run 2 (.ready shifted.functionalControl #[])) =
    some (some (.array #[])) := by decide +kernel
-- A deliberately invalid IR expression checks that controller failure is preserved.
example : observe (ArrayControlIR.run 5 (.ready (.map (.local 0)) #[1,2,3])) =
    some none := by decide +kernel
example : observe (ArrayControlIR.run 1 (.ready squared.imperativeControl #[1,2,3])) =
    none := by decide +kernel

example : pipelined.imperativeControl = pipelined.functionalControl := rfl
example : staged.imperativeControl = staged.functionalControl := rfl
example : observe (ArrayControlIR.run 5 (.ready pipelined.imperativeControl #[-1,2,5])) =
    some (some (.array #[9,0,9])) := by decide +kernel
example : observe (ArrayControlIR.run 5 (.ready staged.functionalControl #[-1,0,3])) =
    some (some (.array #[7,0,8])) := by decide +kernel
example : observe (ArrayControlIR.run 2 (.ready pipelined.functionalControl #[])) =
    some (some (.array #[])) := by decide +kernel

run_cmd do
  for name in [``pipelined.imperativeControl_correct, ``pipelined.functionalControl_correct,
      ``staged.imperativeControl_correct, ``staged.functionalControl_correct,
      ``squared.imperativeControl_correct, ``squared.functionalControl_correct,
      ``shifted.imperativeControl_correct, ``shifted.functionalControl_correct,
      ``branched.imperativeControl_correct, ``branched.functionalControl_correct,
      ``squared.imperative_correct, ``squared.functional_correct,
      ``shifted.imperative_correct, ``shifted.functional_correct,
      ``branched.imperative_correct, ``branched.functional_correct] do
    for ax in (← collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected array entry assumption {ax} in {name}"

end IRComparison.ArrayEntryExamples
