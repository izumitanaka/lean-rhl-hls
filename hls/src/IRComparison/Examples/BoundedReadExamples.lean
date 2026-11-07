import IRComparison.Frontend.LeanBoundedReadCommand

namespace IRComparison.BoundedReadExamples
open Lean Elab Command

def get (a : Array Int) (i : Fin a.size) : Int := a[i]
hls_get get as bounded
example : bounded.imperative.eval #[10,20,30] 1 = some 20 := by decide
example : bounded.functional.eval #[10,20,30] 1 = some 20 := by decide
-- The raw target permits arbitrary Nat inputs; the source theorem assumes Fin.
example : bounded.imperative.eval #[] 0 = none := by decide

example : bounded.imperativeControl = bounded.functionalControl := rfl
example : ArrayControlIR.run 1 (.ready (bounded.imperativeControl 1) #[10,20,30]) =
    .stopped (some (.scalar 20)) := rfl
example : ArrayControlIR.run 1 (.ready (bounded.functionalControl 0) #[]) =
    .stopped none := rfl

run_cmd do
  for name in [``bounded.imperativeControl_correct, ``bounded.functionalControl_correct,
      ``bounded.imperative_correct, ``bounded.functional_correct] do
    for ax in (← collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected bounded entry assumption {ax} in {name}"

end IRComparison.BoundedReadExamples
