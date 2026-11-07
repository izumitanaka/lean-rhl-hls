import IRComparison.Examples.ControlExamples
import IRComparison.Frontend.LeanArrayCommand
import IRComparison.Frontend.LeanBoundedReadCommand

namespace IRComparison.ControlWorkloads
open Lean Elab Command

/- Benchmark-inspired bodies, not full MachSuite ports. Sources:
 https://github.com/breagen/MachSuite/blob/master/stencil/stencil2d/stencil.c
 https://github.com/breagen/MachSuite/blob/master/gemm/ncubed/gemm.c
 https://github.com/breagen/MachSuite/blob/master/spmv/crs/spmv.c
 These independently expressed Lean examples use mathematical integers and
 Option failure. GEMM/SpMV perform one accumulation step with an array-backed
 accumulator. Initialization, traversal and C/FP semantics are not certified. -/

/-- One complete 3x3 stencil output, with input width w and linear base i.
    The nine fixed taps are written explicitly; this is not loop extraction. -/
def stencil9 (i w _y : Int) (s : State) : Option State := do
  let a0 ← (s.arrays 0)[i.toNat]?
  let a1 ← (s.arrays 0)[(i+1).toNat]?
  let a2 ← (s.arrays 0)[(i+2).toNat]?
  let a3 ← (s.arrays 0)[(i+w).toNat]?
  let a4 ← (s.arrays 0)[(i+w+1).toNat]?
  let a5 ← (s.arrays 0)[(i+w+2).toNat]?
  let a6 ← (s.arrays 0)[(i+2*w).toNat]?
  let a7 ← (s.arrays 0)[(i+2*w+1).toNat]?
  let a8 ← (s.arrays 0)[(i+2*w+2).toNat]?
  let k0 ← (s.arrays 1)[0]?
  let k1 ← (s.arrays 1)[1]?
  let k2 ← (s.arrays 1)[2]?
  let k3 ← (s.arrays 1)[3]?
  let k4 ← (s.arrays 1)[4]?
  let k5 ← (s.arrays 1)[5]?
  let k6 ← (s.arrays 1)[6]?
  let k7 ← (s.arrays 1)[7]?
  let k8 ← (s.arrays 1)[8]?
  let r0 := a0*k0 + a1*k1 + a2*k2
  let r1 := a3*k3 + a4*k4 + a5*k5
  let r2 := a6*k6 + a7*k7 + a8*k8
  s.write 2 i (r0 + r1 + r2)

/-- One GEMM multiply-accumulate. i identifies an output element, k a
    reduction index, w the row width. Array 2 is the partial output. -/
def gemmStep (i k w : Int) (s : State) : Option State := do
  let row := i / w
  let col := i - row*w
  let a ← (s.arrays 0)[(row*w+k).toNat]?
  let b ← (s.arrays 1)[(k*w+col).toNat]?
  let old ← (s.arrays 2)[i.toNat]?
  s.write 2 i (old + a*b)

/-- One CRS SpMV contribution. cols supplies a data-dependent vector index. -/
def spmvStep (row j _y : Int) (s : State) : Option State := do
  let col ← (s.arrays 1)[j.toNat]?
  let value ← (s.arrays 0)[j.toNat]?
  let v ← (s.arrays 2)[col.toNat]?
  let old ← (s.arrays 3)[row.toNat]?
  s.write 3 row (old + value*v)

/-- In-place swap: both original values must survive the first write. -/
def swap (i j _y : Int) (s : State) : Option State := do
  let a ← (s.arrays 0)[i.toNat]?
  let b ← (s.arrays 0)[j.toNat]?
  let s ← s.write 0 i b
  s.write 0 j a

/-- Branch-local read bindings followed by a shared continuation and reread. -/
def branchJoin (i x y : Int) (s : State) : Option State := do
  let s ← if x != 0 then do
      let a ← (s.arrays 0)[i.toNat]?
      s.write 0 i (a+y)
    else do
      let b ← (s.arrays 1)[i.toNat]?
      s.write 0 i (b-y)
  let value ← (s.arrays 0)[i.toNat]?
  s.write 2 i value

/-- A local pure function, and a source-level mathematical property. -/
def squaredDistanceWithHelper (i x y : Int) (s : State) : Option State :=
  let square := fun z : Int => z*z
  s.write 0 i (square (x-y))

/-- Equivalent expanded form, within the currently supported scalar syntax. -/
def squaredDistance (i x y : Int) (s : State) : Option State :=
  let delta := x-y
  s.write 0 i (delta*delta)

theorem helper_eq_expanded : squaredDistanceWithHelper = squaredDistance := rfl

theorem squaredDistance_symmetric (i x y : Int) (s : State) :
    squaredDistance i x y s = squaredDistance i y x s := by
  have h : y-x = -(x-y) := by omega
  simp [squaredDistance,h,Int.neg_mul,Int.mul_neg]

hls_control stencil9 as stencil
hls_control gemmStep as gemm
hls_control spmvStep as spmv
hls_control swap as swapped
hls_control branchJoin as joined
hls_control squaredDistance as distance
hls_control squaredDistanceWithHelper as helperDistance
example : helperDistance.imperativeControl = helperDistance.functionalControl := rfl
example : helperDistance.imperativeControl = distance.imperativeControl := rfl

example : stencil.imperativeControl = stencil.functionalControl := rfl
example : gemm.imperativeControl = gemm.functionalControl := rfl
example : spmv.imperativeControl = spmv.functionalControl := rfl
example : swapped.imperativeControl = swapped.functionalControl := rfl
example : joined.imperativeControl = joined.functionalControl := rfl
example : distance.imperativeControl = distance.functionalControl := rfl

/-- A source proof can be composed with compilation, without proving the
    low-level implementation's arithmetic property a second time. -/
theorem distance_controller_symmetric (i x y : Int) (s : State) :
    ∃ n, ControlIR.run i x y n (.running distance.imperativeControl s []) =
      .stopped (squaredDistance i y x s) := by
  rw [← squaredDistance_symmetric i x y s]
  exact distance.imperativeControl_correct i x y s

set_option maxRecDepth 8192

/-- Reference fixture; all four used arrays and several registers are observed. -/
def fixture : State :=
  ⟨fun r => (r : Int) + 7, fun a =>
    if a = 0 then (List.range 16).toArray.map (fun (n : Nat) => (n : Int)+1)
    else if a = 1 then (List.range 16).toArray.map (fun (n : Nat) => (n : Int)+1)
    else if a = 2 then (List.range 16).toArray.map (fun (n : Nat) => 10*((n : Int)+1))
    else if a = 3 then Array.replicate 16 0
    else #[]⟩

def badColumns : State := { fixture with arrays := fun a =>
  if a = 1 then (Array.replicate 16 (-1)) else fixture.arrays a }
def shortArrays : State := ⟨fun _ => -7, fun _ => #[2]⟩
def samples : List State := [fixture, LeanReadExamples.empty, shortArrays, badColumns]
def arguments : List (Int × Int × Int) :=
  [(0,3,0), (5,2,4), (0,1,3), (0,0,3), (-1,0,0), (15,2,4), (0,-2,-1)]

def outputs (r : Option State) : Option (List (Array Int) × List Int) := r.map fun s =>
  ((List.range 4).map s.arrays, (List.range 3).map s.regs)
def observed : ControlIR.Config → Option (Option (List (Array Int) × List Int))
  | .running .. | .inSnapshots .. => none
  | .stopped r => some (outputs r)

def workloads : List ((Int → Int → Int → State → Option State) × List ControlIR.Instr × List ControlIR.Instr) :=
  [(stencil9,stencil.imperativeControl,stencil.functionalControl),
   (gemmStep,gemm.imperativeControl,gemm.functionalControl),
   (spmvStep,spmv.imperativeControl,spmv.functionalControl),
   (swap,swapped.imperativeControl,swapped.functionalControl),
   (branchJoin,joined.imperativeControl,joined.functionalControl),
   (squaredDistance,distance.imperativeControl,distance.functionalControl)]

def allChecks : Bool := workloads.all fun (source,imp,fn) => samples.all fun s =>
  arguments.all fun (i,x,y) =>
    let expected := some (outputs (source i x y s))
    observed (ControlIR.run i x y 160 (.running imp s [])) == expected &&
    observed (ControlIR.run i x y 160 (.running fn s [])) == expected

-- 6 bodies × 4 states × 7 argument tuples = 168 cases, both backends.
-- The simulation cap does not replace the general finite-execution theorem.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
example : allChecks = true := by decide +kernel

example : ControlExamples.observe 2 (ControlIR.run 0 4 0 160 (.running stencil.imperativeControl fixture [])) =
    some (some (fixture.arrays 2 |>.set! 0 348)) := by decide +kernel
example : ControlExamples.observe 2 (ControlIR.run 5 2 4 160 (.running gemm.functionalControl fixture [])) =
    some (some (fixture.arrays 2 |>.set! 5 130)) := by decide +kernel
example : ControlExamples.observe 3 (ControlIR.run 0 1 0 160 (.running spmv.imperativeControl fixture [])) =
    some (some (fixture.arrays 3 |>.set! 0 60)) := by decide +kernel
example : ControlExamples.observe 0 (ControlIR.run 0 3 0 160 (.running swapped.functionalControl fixture [])) =
    some (some ((fixture.arrays 0).set! 0 4 |>.set! 3 1)) := by decide +kernel
example : ControlExamples.observe 2 (ControlIR.run 0 0 3 160 (.running joined.functionalControl fixture [])) =
    some (some (fixture.arrays 2 |>.set! 0 (-2))) := by decide +kernel
example : ControlExamples.observe 0 (ControlIR.run 0 (-5) 2 160 (.running distance.imperativeControl fixture [])) =
    some (some (fixture.arrays 0 |>.set! 0 49)) := by decide +kernel

/-- Additional ordinary Lean input forms, accepted by their typed entry interfaces. -/
def arrayMap (a : Array Int) : Array Int := a.map (fun z => z*z)
def boundedRead (a : Array Int) (i : Fin a.size) : Int := a[i]
hls_array arrayMap as arrayMapped
hls_get boundedRead as indexed

def ordinaryLoop (n x _y : Int) (s : State) : Option State := do
  let mut state := s
  for _ in List.range n.toNat do
    state ← state.write 0 0 x
  return state

hls_control ordinaryLoop as repeated
hls_control LeanReadExamples.oldRead as oldState

example : repeated.imperativeControl = repeated.functionalControl := rfl
example : oldState.imperativeControl = oldState.functionalControl := rfl

run_cmd do
  for name in [``repeated.imperativeControl_correct, ``repeated.functionalControl_correct,
      ``oldState.imperativeControl_correct, ``oldState.functionalControl_correct,
      ``stencil.imperativeControl_correct, ``stencil.functionalControl_correct,
      ``gemm.imperativeControl_correct, ``gemm.functionalControl_correct,
      ``spmv.imperativeControl_correct, ``spmv.functionalControl_correct,
      ``swapped.imperativeControl_correct, ``swapped.functionalControl_correct,
      ``joined.imperativeControl_correct, ``joined.functionalControl_correct,
      ``distance.imperativeControl_correct, ``distance.functionalControl_correct,
      ``arrayMapped.imperative_correct, ``arrayMapped.functional_correct,
      ``indexed.imperative_correct, ``indexed.functional_correct,
      ``helperDistance.imperativeControl_correct, ``helperDistance.functionalControl_correct,
      ``helper_eq_expanded, ``squaredDistance_symmetric, ``distance_controller_symmetric] do
    for ax in (← collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected workload proof assumption {ax} in {name}"
  logInfo "6 additional bodies: identical control code, 168 paired execution cases; helper, map, Fin, for and independent old-state read entries accepted"

end IRComparison.ControlWorkloads
