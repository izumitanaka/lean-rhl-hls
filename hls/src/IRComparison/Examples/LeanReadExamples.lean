import IRComparison.Frontend.LeanBodyCommand
import IRComparison.Examples.NativeExamples

namespace IRComparison.LeanReadExamples
open Lean Elab Command

/-- The value read before a mutation must remain the old value. -/
def captured (i x y : Int) (s : State) : Option State := do
  let old ← (s.arrays 0)[i.toNat]?
  let s ← s.write 0 i x
  s.write 1 i (old + y)

/-- A read after a mutation observes the new state, unlike the captured read. -/
def updated (i x y : Int) (s : State) : Option State := do
  let s ← s.write 0 i x
  let fresh ← (s.arrays 0)[i.toNat]?
  s.write 1 i (fresh + y)

/-- Two simultaneous captured values, branching and further state updates. -/
def twoReads (i x y : Int) (s : State) : Option State := do
  let a ← (s.arrays 0)[0]?
  let b ← (s.arrays 0)[1]?
  let s ← s.write 0 0 x
  if a != 0 then s.write 1 i (a + b + y) else s.write 1 i b

/-- An unused optional read is still an effect that can fail. -/
def unused (i x _y : Int) (s : State) : Option State := do
  let _v ← (s.arrays 0)[i.toNat]?
  s.write 1 0 x

/-- Nat indexing in the source clamps negative integers, unlike signed writes. -/
def naturalIndex (i _x _y : Int) (s : State) : Option State := do
  let v ← (s.arrays 0)[(i - 1).toNat]?
  s.write 1 0 v

/-- Read failure in an unselected branch must not be introduced. -/
def conditionalRead (_i x _y : Int) (s : State) : Option State := do
  if x != 0 then
    let v ← (s.arrays 0)[0]?
    s.write 1 0 v
  else return s

/-- A captured value can be the index of another read across a mutation. -/
def dependentRead (_i x y : Int) (s : State) : Option State := do
  let index ← (s.arrays 0)[0]?
  let s ← s.write 0 0 x
  let value ← (s.arrays 0)[index.toNat]?
  s.write 1 0 (value + index + y)

/-- Reading an older array state is distinct from keeping a scalar value. -/
def oldRead (i x _y : Int) (s : State) : Option State := do
  let next ← s.write 0 i x
  let old ← (s.arrays 0)[0]?
  next.write 1 0 old

/-- A recurrence through the same array element across loop iterations. -/
def accumulate (_i x _y : Int) (s : State) : Option State := do
  let old ← (s.arrays 0)[0]?
  s.write 0 0 (old + x)

hls_body oldRead as previous
hls_body accumulate as recurrence
hls_body conditionalRead as guarded
hls_body dependentRead as dependent
hls_body captured as capture
hls_body updated as fresh
hls_body twoReads as pair
hls_body unused as mandatory
hls_body naturalIndex as natural
hls_body NativeExamples.updateBody as conditional

def initial : State := ⟨fun _ => 0, fun a => if a = 0 then #[10,20] else #[0,0]⟩
def observe (a : Nat) (result : Option State) : Option (Array Int) := result.map (fun s => s.arrays a)

example : observe 1 (capture.imperativeBody.eval 0 99 3 initial) = some #[13,0] := by decide
example : observe 1 (capture.functionalBody.eval 0 99 3 [initial]) = some #[13,0] := by decide
example : observe 0 (capture.imperativeBody.eval 0 99 3 initial) = some #[99,20] := by decide
example : observe 1 (fresh.imperativeBody.eval 0 99 3 initial) = some #[102,0] := by decide
example : observe 1 (fresh.functionalBody.eval 0 99 3 [initial]) = some #[102,0] := by decide
example : observe 1 (pair.imperativeBody.eval 0 99 3 initial) = some #[33,0] := by decide
example : observe 1 (pair.functionalBody.eval 0 99 3 [initial]) = some #[33,0] := by decide
example : observe 1 (mandatory.imperativeBody.eval 2 99 3 initial) = none := by decide
example : observe 1 (mandatory.functionalBody.eval 2 99 3 [initial]) = none := by decide
example : observe 1 (natural.imperativeBody.eval (-10) 0 0 initial) = some #[10,0] := by decide
example : observe 1 (natural.functionalBody.eval (-10) 0 0 [initial]) = some #[10,0] := by decide
-- The same compiled bodies remain connected to both optimized loop wrappers.
example : observe 1 ((capture.imperative 0 1 1 0 1).eval (arrayInput #[99,3]) initial) = some #[13,0] := by decide
example : observe 1 ((capture.functional 0 1 1 0 1).eval (arrayInput #[99,3]) initial) = some #[13,0] := by decide

def empty : State := ⟨fun _ => 0, fun _ => #[]⟩
def indirectInitial : State := ⟨fun _ => 0, fun a => if a = 0 then #[1,20] else #[0,0]⟩
example : observe 0 (guarded.imperativeBody.eval 0 0 0 empty) = some #[] := by decide
example : observe 0 (guarded.functionalBody.eval 0 0 0 [empty]) = some #[] := by decide
example : observe 0 (guarded.imperativeBody.eval 0 1 0 empty) = none := by decide
example : observe 0 (guarded.functionalBody.eval 0 1 0 [empty]) = none := by decide
example : observe 1 (dependent.imperativeBody.eval 0 99 3 indirectInitial) = some #[24,0] := by decide
example : observe 1 (dependent.functionalBody.eval 0 99 3 [indirectInitial]) = some #[24,0] := by decide

example : observe 0 ((recurrence.imperative 0 1 3 0 1).eval (arrayInput #[1,2,3,4]) initial) = some #[16,20] := by decide
example : observe 0 ((recurrence.functional 0 1 3 0 1).eval (arrayInput #[1,2,3,4]) initial) = some #[16,20] := by decide
example : observe 0 ((recurrence.imperative 3 (-1) 3 0 (-1)).eval (arrayInput #[1,2,3,4]) initial) = some #[19,20] := by decide
example : observe 0 ((recurrence.functional 3 (-1) 3 0 (-1)).eval (arrayInput #[1,2,3,4]) initial) = some #[19,20] := by decide

run_cmd do
  for name in [``recurrence.imperative_correct, ``recurrence.functional_correct, ``guarded.imperative_correct, ``guarded.functional_correct,
      ``dependent.imperative_correct, ``dependent.functional_correct, ``capture.imperative_correct, ``capture.functional_correct,
      ``fresh.imperative_correct, ``fresh.functional_correct,
      ``pair.imperative_correct, ``pair.functional_correct,
      ``mandatory.imperative_correct, ``mandatory.functional_correct,
      ``natural.imperative_correct, ``natural.functional_correct,
      ``conditional.imperative_correct, ``conditional.functional_correct] do
    for assumption in (← collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains assumption do
        throwError "unexpected read certificate assumption {assumption} in {name}"

  for name in [``previous.imperativeBody_correct, ``previous.functionalBody_correct] do
    for ax in (← collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected old-state certificate assumption {ax}"

end IRComparison.LeanReadExamples
