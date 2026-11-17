import IRComparison.Frontend.LeanSnapshotCommand

namespace IRComparison.SnapshotEntryExamples
open Lean Elab Command

def dependent (i x _y : Int) (s : State) : Option State := do
  let next ← s.write 0 i x
  let j ← (next.arrays 0)[0]?
  let old ← (s.arrays 0)[j.toNat]?
  next.write 1 0 old

hls_snapshots dependent as dynamicOld

def threeVersions (i x _y : Int) (s : State) : Option State := do
  let middle ← s.write 0 i x
  let newest ← middle.write 0 i (x+1)
  let a ← (s.arrays 0)[i.toNat]?
  let b ← (middle.arrays 0)[i.toNat]?
  let c ← (newest.arrays 0)[i.toNat]?
  newest.write 1 0 (100*a+10*b+c)

def returnOld (i x _y : Int) (s : State) : Option State := do
  let _next ← s.write 0 i x
  return s

def selectedVersion (i x flag : Int) (s : State) : Option State := do
  let next ← if flag != 0 then s.write 0 i x else s.write 0 i (x+1)
  let j ← (next.arrays 0)[0]?
  if flag != 0 then do
    let v ← (s.arrays 0)[j.toNat]?
    next.write 1 0 v
  else do
    let v ← (next.arrays 0)[j.toNat]?
    s.write 1 0 v

hls_snapshots threeVersions as retained
hls_snapshots returnOld as original
hls_snapshots selectedVersion as chosen

example : dynamicOld.imperativeControl = dynamicOld.functionalControl := rfl
example : retained.imperativeControl = retained.functionalControl := rfl
example : original.imperativeControl = original.functionalControl := rfl
example : chosen.imperativeControl = chosen.functionalControl := rfl

def initial : State := ⟨fun _ => 0,fun a => if a = 0 then #[2,10,20] else #[0]⟩
def observe : ControlIR.Config → Option (Option (Array Int × Array Int))
  | .stopped r => some (r.map fun s => (s.arrays 0,s.arrays 1))
  | _ => none

def simulate (code : List ControlIR.Instr) (i x y : Int) :=
  observe (ControlIR.run i x y 200 (.running code initial []))

example : simulate dynamicOld.imperativeControl 0 0 0 = some (some (#[0,10,20],#[2])) := by decide +kernel
example : simulate dynamicOld.functionalControl 0 2 0 = some (some (#[2,10,20],#[20])) := by decide +kernel
example : simulate dynamicOld.functionalControl 0 (-1) 0 = some (some (#[-1,10,20],#[2])) := by decide +kernel
example : simulate dynamicOld.functionalControl 0 7 0 = some none := by decide +kernel
example : simulate dynamicOld.imperativeControl 9 0 0 = some none := by decide +kernel
example : simulate retained.imperativeControl 0 1 0 = some (some (#[2,10,20],#[212])) := by decide +kernel
example : simulate original.functionalControl 0 99 0 = some (some (#[2,10,20],#[0])) := by decide +kernel
example : simulate original.imperativeControl 9 99 0 = some none := by decide +kernel
example : simulate chosen.imperativeControl 0 0 1 = some (some (#[0,10,20],#[2])) := by decide +kernel
example : simulate chosen.functionalControl 0 0 0 = some (some (#[2,10,20],#[10])) := by decide +kernel

example (i d : Int) (n : Nat) (l r : Int) :
    dynamicOld.imperativeOptimizedControl i d n l r = dynamicOld.functionalOptimizedControl i d n l r := rfl

example : (match ProgramControlIR.run (arrayInput #[0,1,2]) 400
    (.running (dynamicOld.imperativeOptimizedControl 0 1 2 0 1) initial ProgramControlIR.initial) with
    | .stopped r => r.map fun s => (s.arrays 0,s.arrays 1)
    | _ => none) = some (#[0,1,20],#[0]) := by decide +kernel

run_cmd do
  for name in [``dynamicOld.imperativeOptimizedControl_correct, ``dynamicOld.functionalOptimizedControl_correct,
      ``dynamicOld.functional_correct, ``dynamicOld.imperative_correct,
      ``dynamicOld.functionalControl_correct, ``dynamicOld.imperativeControl_correct,
      ``retained.functionalControl_correct, ``retained.imperativeControl_correct,
      ``original.functionalControl_correct, ``original.imperativeControl_correct,
      ``chosen.functionalControl_correct, ``chosen.imperativeControl_correct] do
    for ax in (← collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected snapshot entry assumption {ax}"

end IRComparison.SnapshotEntryExamples
