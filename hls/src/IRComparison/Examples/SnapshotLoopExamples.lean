import IRComparison.Frontend.LeanSnapshotCommand

namespace IRComparison.SnapshotLoopExamples
open Lean Elab Command
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

/-- Every iteration reads the original array, despite overwriting the same array. -/
def originalAcrossLoop (n x _y : Int) (s : State) : Option State := do
  let mut current := s
  for k in List.range n.toNat do
    let old ← (s.arrays 0)[0]?
    current ← current.write 0 0 (old + x + (k : Int))
  let old ← (s.arrays 0)[0]?
  current.write 1 0 old

/-- The inner loop captures both the entry state and the outer iteration's snapshot. -/
def nestedVersions (n x _y : Int) (s : State) : Option State := do
  let mut current := s
  for row in List.range n.toNat do
    let saved := current
    for col in List.range n.toNat do
      let original ← (s.arrays 0)[0]?
      let previous ← (saved.arrays 0)[0]?
      current ← current.write 0 0 (original + previous + x + (row : Int) + (col : Int))
  return current

/-- An update determines an index into the immutable entry snapshot. -/
def dynamicOldIndex (n x _y : Int) (s : State) : Option State := do
  let mut current := s
  for k in List.range n.toNat do
    current ← current.write 0 0 (x + (k : Int))
    let j ← (current.arrays 0)[0]?
    let old ← (s.arrays 0)[j.toNat]?
    current ← current.write 1 0 old
  return current

hls_snapshots originalAcrossLoop as captured
hls_snapshots nestedVersions as nested
hls_snapshots dynamicOldIndex as dynamic

example : captured.imperativeControl = captured.functionalControl := rfl
example : nested.imperativeControl = nested.functionalControl := rfl
example : dynamic.imperativeControl = dynamic.functionalControl := rfl

def initial : State := ⟨fun _ => 0, fun a => if a = 0 then #[2,10,20] else #[0]⟩
def observe (a : Nat) : ControlIR.Config → Option (Option (Array Int))
  | .stopped r => some (r.map fun s => s.arrays a)
  | _ => none

example : observe 0 (ControlIR.run 3 5 0 1000 (.running captured.imperativeControl initial [])) =
    some (some #[9,10,20]) := by decide +kernel
example : observe 1 (ControlIR.run 3 5 0 1000 (.running captured.functionalControl initial [])) =
    some (some #[2]) := by decide +kernel
example : observe 0 (ControlIR.run 2 0 0 1000 (.running nested.imperativeControl initial [])) =
    some (some #[9,10,20]) := by decide +kernel
example : observe 1 (ControlIR.run 3 0 0 1000 (.running dynamic.functionalControl initial [])) =
    some (some #[20]) := by decide +kernel
example : observe 1 (ControlIR.run 4 0 0 1000 (.running dynamic.functionalControl initial [])) =
    some none := by decide +kernel
example : observe 0 (ControlIR.run 0 5 0 1000 (.running captured.imperativeControl initial [])) =
    some (some #[2,10,20]) := by decide +kernel
example : observe 0 (ControlIR.run (-1) 5 0 1000 (.running captured.imperativeControl initial [])) =
    some (some #[2,10,20]) := by decide +kernel

run_cmd do
  for name in [``captured.imperativeControl_correct, ``captured.functionalControl_correct,
      ``nested.imperativeControl_correct, ``nested.functionalControl_correct,
      ``dynamic.imperativeControl_correct, ``dynamic.functionalControl_correct,
      ``captured.imperativeOptimizedControl_correct, ``captured.functionalOptimizedControl_correct] do
    for ax in (← collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected captured-loop assumption {ax}"

end IRComparison.SnapshotLoopExamples
