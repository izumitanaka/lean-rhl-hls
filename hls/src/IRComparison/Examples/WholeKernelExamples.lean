import IRComparison.Frontend.LeanControlCommand

namespace IRComparison.WholeKernelExamples
open Lean Elab Command
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

/-- Square-matrix multiplication, including all three loops. Arrays 0/1 are
    inputs, array 2 is the output. Existing output values are accumulated. -/
def gemm (n _x _y : Int) (s : State) : Option State := do
  let mut state := s
  for row in List.range n.toNat do
    for col in List.range n.toNat do
      for k in List.range n.toNat do
        let a ← (state.arrays 0)[((row : Int)*n+(k : Int)).toNat]?
        let b ← (state.arrays 1)[((k : Int)*n+(col : Int)).toNat]?
        let old ← (state.arrays 2)[((row : Int)*n+(col : Int)).toNat]?
        state ← state.write 2 ((row : Int)*n+(col : Int)) (old+a*b)
  return state

/-- CSR sparse matrix/vector multiplication. Row pointers (array 0) determine
    each inner loop's start/count at runtime; 1=columns, 2=values, 3=vector,
    4=output. Non-monotone pointers give zero iterations via Int.toNat. -/
def spmv (rows _x _y : Int) (s : State) : Option State := do
  let mut state := s
  for row in List.range rows.toNat do
    let first ← (state.arrays 0)[row]?
    let stop ← (state.arrays 0)[((row : Int)+1).toNat]?
    for offset in List.range (stop-first).toNat do
      let j := first+(offset : Int)
      let col ← (state.arrays 1)[j.toNat]?
      let value ← (state.arrays 2)[j.toNat]?
      let v ← (state.arrays 3)[col.toNat]?
      let old ← (state.arrays 4)[row]?
      state ← state.write 4 (row : Int) (old+value*v)
  return state

hls_control gemm as matrix
hls_control spmv as sparse

example : matrix.imperativeControl = matrix.functionalControl := rfl
example : sparse.imperativeControl = sparse.functionalControl := rfl

def matrixInput : State := ⟨fun _ => 0,fun a =>
  if a = 0 then #[1,2,3,4] else if a = 1 then #[5,6,7,8] else #[0,0,0,0]⟩
def sparseInput : State := ⟨fun _ => 0,fun a =>
  if a = 0 then #[0,2,2,3] else if a = 1 then #[0,2,1]
  else if a = 2 then #[2,3,4] else if a = 3 then #[10,20,30] else #[0,0,0]⟩
def observe (a : Nat) : ControlIR.Config → Option (Option (Array Int))
  | .stopped r => some (r.map fun s => s.arrays a)
  | _ => none

example : observe 2 (ControlIR.run 2 0 0 2000 (.running matrix.imperativeControl matrixInput [])) =
    some (some #[19,22,43,50]) := by decide +kernel
example : observe 4 (ControlIR.run 3 0 0 2000 (.running sparse.functionalControl sparseInput [])) =
    some (some #[110,0,80]) := by decide +kernel

run_cmd do
  for name in [``matrix.imperativeControl_correct, ``matrix.functionalControl_correct,
      ``sparse.imperativeControl_correct, ``sparse.functionalControl_correct] do
    for ax in (← collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected whole-kernel assumption {ax}"

end IRComparison.WholeKernelExamples
