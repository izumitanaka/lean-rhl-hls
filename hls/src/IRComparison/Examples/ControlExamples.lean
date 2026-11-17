import IRComparison.Frontend.LeanControlCommand
import IRComparison.Examples.LeanReadExamples

namespace IRComparison.ControlExamples
open Lean Elab Command

hls_control LeanReadExamples.captured as captured
hls_control LeanReadExamples.dependentRead as dependent
hls_control LeanReadExamples.conditionalRead as guarded
hls_control LeanReadExamples.accumulate as accumulate

-- The additional functional-state pass emits the same controller here;
-- its proof obligation does not imply an extra memory or runtime copy.
example : captured.imperativeControl = captured.functionalControl := rfl
example : dependent.imperativeControl = dependent.functionalControl := rfl
example : guarded.imperativeControl = guarded.functionalControl := rfl
example : accumulate.imperativeControl = accumulate.functionalControl := rfl

def observe (a : Nat) : ControlIR.Config → Option (Option (Array Int))
  | .running .. | .inSnapshots .. => none
  | .stopped r => some (r.map fun s => s.arrays a)

-- Values captured before updates survive, on both paths.
example : observe 1 (ControlIR.run 0 99 3 40 (.running captured.imperativeControl LeanReadExamples.initial [])) =
    some (some #[13,0]) := by decide
example : observe 1 (ControlIR.run 0 99 3 40 (.running captured.functionalControl LeanReadExamples.initial [])) =
    some (some #[13,0]) := by decide
example : observe 1 (ControlIR.run 0 99 3 40 (.running dependent.functionalControl LeanReadExamples.indirectInitial [])) =
    some (some #[24,0]) := by decide
-- An unselected read must not be speculatively performed.
example : observe 0 (ControlIR.run 0 0 0 40 (.running guarded.imperativeControl LeanReadExamples.empty [])) =
    some (some #[]) := by decide
example : observe 0 (ControlIR.run 0 1 0 40 (.running guarded.functionalControl LeanReadExamples.empty [])) =
    some none := by decide
-- Running out of simulation fuel is not represented as source failure.
example : observe 0 (ControlIR.run 0 0 0 0 (.running guarded.imperativeControl LeanReadExamples.empty [])) = none := by decide

-- Counted nested loops compile without expanding the iteration count into code.
def loopBody : Imperative.Cmd := .repeat 3 (.repeat 2 accumulate.imperativeBody)
example : observe 0 (ControlIR.run 0 1 0 80 (.running (ControlIR.lower loopBody) LeanReadExamples.initial [])) =
    some (some #[16,20]) := by decide
example : ControlIR.lower (.repeat 0 (.store 0 (.lit (-1)) (.lit 2))) =
    [.repeat 0 [.store 0 (.lit (-1)) (.lit 2)]] := rfl

-- A real use of an earlier state cannot be erased by the allocation pass.
def oldVersion : Functional.Term := .letWrite 0 0 (.lit 0) (.lit 99) (.yield 1)
example : StateLowering.lower oldVersion = none := rfl
example : (oldVersion.eval 0 0 0 [LeanReadExamples.initial]).map (fun s => s.arrays 0) = some #[10,20] := by decide

run_cmd do
  for name in [``StateLowering.lower_correct, ``ControlIR.lower_correct,
      ``ControlIR.lower_finishes, ``ControlIR.lowerFunctional_finishes,
      ``captured.imperativeControl_correct, ``captured.functionalControl_correct,
      ``dependent.imperativeControl_correct, ``dependent.functionalControl_correct,
      ``guarded.imperativeControl_correct, ``guarded.functionalControl_correct,
      ``accumulate.imperativeControl_correct, ``accumulate.functionalControl_correct] do
    for ax in (← collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected control proof assumption {ax} in {name}"

end IRComparison.ControlExamples
