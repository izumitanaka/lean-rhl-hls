import IRComparison.Frontend.LeanControlCommand

namespace IRComparison.LoopEntryExamples
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

def counted (n x _y : Int) (s : State) : Option State := do
  let mut state := s
  for _ in List.range n.toNat do
    state ← state.write 0 0 x
  return state

def indexed (n x y : Int) (s : State) : Option State := do
  let mut state := s
  for k in List.range n.toNat do
    state ← state.write 0 (k : Int) (x + (k : Int)*y)
  return state

def copy (n x _y : Int) (s : State) : Option State := do
  let mut state := s
  for k in List.range n.toNat do
    let v ← (state.arrays 0)[k]?
    state ← state.write 1 (k : Int) (v+x)
  return state

def conditional (n x y : Int) (s : State) : Option State := do
  let mut state := s
  for k in List.range n.toNat do
    if x != 0 then
      state ← state.write 0 (k : Int) y
    else
      state ← state.write 0 (k : Int) (y+1)
  return state

def nested (n x m : Int) (s : State) : Option State := do
  let mut state := s
  for k in List.range n.toNat do
    for j in List.range m.toNat do
      state ← state.write 0 ((k : Int)*m+(j : Int)) (x+(k : Int)+(j : Int))
  return state

hls_control nested as nestedLoops
hls_control copy as copied
hls_control conditional as guarded
hls_control counted as constantLoop
hls_control indexed as indexedLoop

example : nestedLoops.imperativeControl = nestedLoops.functionalControl := rfl
example : copied.imperativeControl = copied.functionalControl := rfl
example : guarded.imperativeControl = guarded.functionalControl := rfl

example : constantLoop.imperativeControl = constantLoop.functionalControl := rfl
example : indexedLoop.imperativeControl = indexedLoop.functionalControl := rfl

def initial : State := ⟨fun _ => 0,fun _ => #[0,0,0,0]⟩
def observe : ControlIR.Config → Option (Option (Array Int))
  | .running .. | .inSnapshots .. => none
  | .stopped r => some (r.map fun s => s.arrays 0)

example : observe (ControlIR.run 4 3 2 160 (.running indexedLoop.imperativeControl initial [])) =
    some (some #[3,5,7,9]) := by decide +kernel
example : observe (ControlIR.run 0 3 2 160 (.running indexedLoop.functionalControl initial [])) =
    some (some #[0,0,0,0]) := by decide +kernel
example : observe (ControlIR.run (-4) 3 2 160 (.running indexedLoop.functionalControl initial [])) =
    some (some #[0,0,0,0]) := by decide +kernel
example : observe (ControlIR.run 5 3 2 160 (.running indexedLoop.functionalControl initial [])) =
    some none := by decide +kernel
example : observe (ControlIR.run 4 3 2 160 (.running constantLoop.imperativeControl initial [])) =
    some (some #[3,0,0,0]) := by decide +kernel

example : observe (ControlIR.run 4 3 2 200 (.running guarded.functionalControl initial [])) =
    some (some #[2,2,2,2]) := by decide +kernel
example : observe (ControlIR.run 4 0 2 200 (.running guarded.imperativeControl initial [])) =
    some (some #[3,3,3,3]) := by decide +kernel
example : (match ControlIR.run 4 3 2 200 (.running copied.imperativeControl initial []) with
    | .stopped r => r.map fun s => s.arrays 1 | _ => none) = some #[3,3,3,3] := by decide +kernel

example : observe (ControlIR.run 2 10 2 400 (.running nestedLoops.functionalControl initial [])) =
    some (some #[10,11,11,12]) := by decide +kernel

run_cmd do
  for name in [``nestedLoops.imperativeControl_correct, ``nestedLoops.functionalControl_correct,
      ``copied.imperativeControl_correct, ``copied.functionalControl_correct,
      ``guarded.imperativeControl_correct, ``guarded.functionalControl_correct,
      ``constantLoop.imperativeControl_correct, ``constantLoop.functionalControl_correct,
      ``indexedLoop.imperativeControl_correct, ``indexedLoop.functionalControl_correct] do
    for ax in (← Lean.collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected loop certificate assumption {ax}"

end IRComparison.LoopEntryExamples
