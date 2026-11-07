import IRComparison.Frontend.LeanBodyCommand
import IRComparison.Frontend.LeanCertificate
import IRComparison.Examples.NativeExamples

namespace IRComparison.LeanBodyExamples
open Lean Elab Command Lean4Lean LeanTyped LeanBodyQuotation LeanIREvaluation

/-- An output array other than zero, data-dependent address and nested integer
    computation. No bound is assumed; failed updates must remain failures. -/
def scatter (i x y : Int) (s : State) : Option State :=
  s.write 2 (i + x) (if y != 0 then let z := x - y; z * z else -i)

def letWrite (i x y : Int) (s : State) : Option State :=
  let x := x + y
  let y := x - i
  s.write 1 i (x * y)

def chooseWrite (i x y : Int) (s : State) : Option State :=
  if x != 0 then s.write 0 i (x + y) else s.write 1 (i - 1) (y / 2)

def sequential (i x y : Int) (s : State) : Option State := do
  let s ← s.write 0 i x
  s.write 1 (i+1) y

def conditionalSequence (i x y : Int) (s : State) : Option State := do
  let s ← if x != 0 then s.write 0 i x else s.write 1 i y
  let s ← s.write 2 i (x+y)
  s.write 0 i (y-i)

def sequenceReturn (i x y : Int) (s : State) : Option State := do
  let next ← s.write 0 i (x+y)
  let final ← next.write 0 i (x-y)
  return final

def failFirst (_i x y : Int) (s : State) : Option State := do
  let next ← s.write 0 (-1) x
  next.write 1 0 y

/-- Deliberately reuse the old state: treating this as ordinary sequencing
    would incorrectly retain the first write. This case is still unsupported. -/
def reuseOld (i x y : Int) (s : State) : Option State := do
  let _next ← s.write 0 i x
  s.write 1 i y

run_cmd do
  let native ← getEnv
  for name in [``NativeExamples.meanBody, ``scatter, ``chooseWrite, ``letWrite, ``sequential, ``conditionalSequence, ``sequenceReturn, ``failFirst] do
    let some result := LeanNamedBody.compile native name
      | throwError "ordinary array-update body rejected: {name}"
    let body := result.body
    let pi := LeanNamedBody.close result.imperativeProof
    let pf := LeanNamedBody.close result.functionalProof
    let ti := LeanNamedBody.specification name
      (imperativeEval (imperativeCode body.imperative) (.bvar 3) (.bvar 2) (.bvar 1) (.bvar 0))
    let tf := LeanNamedBody.specification name
      (functionalEval (functionalCode body.functional) (.bvar 3) (.bvar 2) (.bvar 1) (.bvar 0))
    for (suffix,proof,type) in [("imperativeBody",pi,ti),("functionalBody",pf,tf)] do
      liftCoreM <| addDecl (.thmDecl {
        name := .str name suffix, levelParams := [],
        type := LeanCertificate.expression type, value := LeanCertificate.expression proof })
    logInfo m!"{name}: both array-update body certificates accepted by the native kernel"

hls_body NativeExamples.meanBody as mean
hls_body scatter as scattered
hls_body chooseWrite as chosen
hls_body letWrite as withLets
hls_body sequential as sequenced
hls_body conditionalSequence as sequencedBranch
hls_body sequenceReturn as returned
hls_body failFirst as earlyFailure

example (start stride : Int) (count : Nat) (l r : Int) (input : Input) (s : State) :
    (mean.imperative start stride count l r).eval input s =
      BodyBackends.runSource NativeExamples.meanBody start stride count l r input s :=
  mean.imperative_correct start stride count l r input s

example (start stride : Int) (count : Nat) (l r : Int) (input : Input) (s : State) :
    (mean.functional start stride count l r).eval input s =
      BodyBackends.runSource NativeExamples.meanBody start stride count l r input s :=
  mean.functional_correct start stride count l r input s

private def initial : State := ⟨fun _ => 0, fun _ => #[0,0,0,0]⟩
private def observe (a : Nat) (r : Option State) : Option (Array Int) := r.map (fun s => s.arrays a)

example : observe 0 ((mean.imperative 0 1 3 0 1).eval (arrayInput #[2,4,6,8]) initial) =
    some #[3,5,7,0] := by decide
example : observe 0 ((mean.functional 0 1 3 0 1).eval (arrayInput #[2,4,6,8]) initial) =
    some #[3,5,7,0] := by decide
example : observe 0 ((mean.imperative 3 (-1) 3 0 (-1)).eval (arrayInput #[2,4,6,8]) initial) =
    some #[0,3,5,7] := by decide
example : observe 0 ((mean.functional 3 (-1) 3 0 (-1)).eval (arrayInput #[2,4,6,8]) initial) =
    some #[0,3,5,7] := by decide
-- The chosen branch writes a negative index. Both paths must fail.
example : observe 1 ((chosen.imperative 0 1 1 0 1).eval (arrayInput #[0,4]) initial) = none := by decide
example : observe 1 ((chosen.functional 0 1 1 0 1).eval (arrayInput #[0,4]) initial) = none := by decide
-- The false branch has an invalid address but is not executed.
example : observe 0 ((chosen.imperative 0 1 1 0 1).eval (arrayInput #[2,4]) initial) = some #[6,0,0,0] := by decide
example : observe 0 ((chosen.functional 0 1 1 0 1).eval (arrayInput #[2,4]) initial) = some #[6,0,0,0] := by decide

-- Different arrays must retain both updates.
example : observe 0 ((sequenced.imperative 0 1 1 0 1).eval (arrayInput #[2,5]) initial) = some #[2,0,0,0] := by decide
example : observe 1 ((sequenced.imperative 0 1 1 0 1).eval (arrayInput #[2,5]) initial) = some #[0,5,0,0] := by decide
example : observe 0 ((sequenced.functional 0 1 1 0 1).eval (arrayInput #[2,5]) initial) = some #[2,0,0,0] := by decide
example : observe 1 ((sequenced.functional 0 1 1 0 1).eval (arrayInput #[2,5]) initial) = some #[0,5,0,0] := by decide
-- Last write wins, and return must return the updated state.
example : observe 0 ((returned.imperative 0 1 1 0 1).eval (arrayInput #[2,5]) initial) = some #[-3,0,0,0] := by decide
example : observe 0 ((returned.functional 0 1 1 0 1).eval (arrayInput #[2,5]) initial) = some #[-3,0,0,0] := by decide
-- Failure of either stage cannot be dropped.
example : observe 1 ((earlyFailure.imperative 0 1 1 0 1).eval (arrayInput #[2,5]) initial) = none := by decide
example : observe 1 ((earlyFailure.functional 0 1 1 0 1).eval (arrayInput #[2,5]) initial) = none := by decide
example : observe 1 ((sequenced.imperative 3 1 1 (-3) (-2)).eval (arrayInput #[2,5]) initial) = none := by decide
example : observe 1 ((sequenced.functional 3 1 1 (-3) (-2)).eval (arrayInput #[2,5]) initial) = none := by decide
-- Branches and a three-stage update retain the state from earlier stages.
example : observe 1 ((sequencedBranch.imperative 0 1 1 0 1).eval (arrayInput #[0,5]) initial) = some #[5,0,0,0] := by decide
example : observe 2 ((sequencedBranch.functional 0 1 1 0 1).eval (arrayInput #[0,5]) initial) = some #[5,0,0,0] := by decide

-- Audit the actual exported final certificates as well as the general compiler.
run_cmd do
  for name in [``mean.imperative_correct, ``mean.functional_correct,
      ``scattered.imperative_correct, ``scattered.functional_correct,
      ``chosen.imperative_correct, ``chosen.functional_correct,
      ``withLets.imperative_correct, ``withLets.functional_correct,
      ``sequenced.imperative_correct, ``sequenced.functional_correct,
      ``sequencedBranch.imperative_correct, ``sequencedBranch.functional_correct,
      ``returned.imperative_correct, ``returned.functional_correct,
      ``earlyFailure.imperative_correct, ``earlyFailure.functional_correct] do
    for assumption in (← collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains assumption do
        throwError "unexpected certificate assumption {assumption} in {name}"
  if (LeanBodyPipeline.compile (← getEnv) ``reuseOld).isSome then
    throwError "reuse of the old state was silently treated as sequential update"

end IRComparison.LeanBodyExamples
