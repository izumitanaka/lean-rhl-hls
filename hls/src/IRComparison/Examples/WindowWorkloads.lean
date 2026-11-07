import IRComparison.Memory.WindowPipeline
import IRComparison.Frontend.LeanWindowCommand

namespace IRComparison.WindowWorkloads
open WindowPipeline
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

-- Kernel expressions and trip counts transcribed from PaperCore's
-- artifacts/paper-reference-audit/*/scaled-normalized.json.
-- All arrays have 64 initialized elements here: the finite-Array semantics
-- cannot reproduce the unbounded-heap allocation mismatch in some JSON files.
-- This is a kernel comparison, not a claim of full C benchmark equivalence.

def filter (i _x _y : Int) (s : State) : Option State := do
  let a ← (s.arrays 0)[(i).toNat]?
  let b ← (s.arrays 0)[(i+1).toNat]?
  let c ← (s.arrays 0)[(i+2).toNat]?
  s.write 1 i ((a+b+c)/3)
hls_window filter as filterCode

def filterAlt (i _x _y : Int) (s : State) : Option State := do
  let a ← (s.arrays 0)[(63-i).toNat]?
  let b ← (s.arrays 0)[(62-i).toNat]?
  let c ← (s.arrays 0)[(61-i).toNat]?
  s.write 1 i ((a+b+c)/3)
hls_window filterAlt as filterAltCode

def filterSkip (i _x _y : Int) (s : State) : Option State := do
  let a ← (s.arrays 0)[(2*i).toNat]?
  let b ← (s.arrays 0)[(2*i+1).toNat]?
  let c ← (s.arrays 0)[(2*i+2).toNat]?
  s.write 1 i ((a+b+c)/3)
hls_window filterSkip as filterSkipCode

def filterDilated (i _x _y : Int) (s : State) : Option State := do
  let a ← (s.arrays 0)[(2*i).toNat]?
  let b ← (s.arrays 0)[(2*i+2).toNat]?
  let c ← (s.arrays 0)[(2*i+4).toNat]?
  s.write 1 i ((a+b+c)/3)
hls_window filterDilated as filterDilatedCode

def filterDilatedAlt (i _x _y : Int) (s : State) : Option State := do
  let a ← (s.arrays 0)[((31-i)*2).toNat]?
  let b ← (s.arrays 0)[((30-i)*2).toNat]?
  let c ← (s.arrays 0)[((29-i)*2).toNat]?
  s.write 1 i ((a+b+c)/3)
hls_window filterDilatedAlt as filterDilatedAltCode

def filterDilatedRev (i _x _y : Int) (s : State) : Option State := do
  let a ← (s.arrays 0)[(i).toNat]?
  let b ← (s.arrays 0)[(i+2).toNat]?
  let c ← (s.arrays 0)[(i+4).toNat]?
  s.write 1 i ((a+b+c)/3)
hls_window filterDilatedRev as filterDilatedRevCode

def initial : State := ⟨fun _ => 0,fun a => if a = 0 then
  ((List.range 64).map (fun n => Int.ofNat n + 1)).toArray else Array.replicate 64 0⟩
def order : List Int := (List.range 64).map Int.ofNat

structure Workload where
  name : String
  imperative : Stage
  functional : Stage
  expectedFIFO : Bool

def workloads : List Workload := [
  ⟨"filter",imperative (filterCode.imperativeWindow 64 0 0 (1) 62 order),
    functional (filterCode.functionalWindow 64 0 0 (1) 62 order),true⟩,
  ⟨"filter_alt",imperative (filterAltCode.imperativeWindow 64 0 0 (1) 62 order),
    functional (filterAltCode.functionalWindow 64 0 0 (1) 62 order),false⟩,
  ⟨"filter_rev",imperative (filterCode.imperativeWindow 64 0 61 (-1) 62 order),
    functional (filterCode.functionalWindow 64 0 61 (-1) 62 order),false⟩,
  ⟨"filter_skip",imperative (filterSkipCode.imperativeWindow 64 0 0 (1) 30 order),
    functional (filterSkipCode.functionalWindow 64 0 0 (1) 30 order),true⟩,
  ⟨"filter_dilated",imperative (filterDilatedCode.imperativeWindow 64 0 0 (1) 28 order),
    functional (filterDilatedCode.functionalWindow 64 0 0 (1) 28 order),true⟩,
  ⟨"filter_dilated_alt",imperative (filterDilatedAltCode.imperativeWindow 64 0 0 (1) 28 order),
    functional (filterDilatedAltCode.functionalWindow 64 0 0 (1) 28 order),false⟩,
  ⟨"filter_dilated_rev",imperative (filterDilatedRevCode.imperativeWindow 64 0 59 (-1) 60 order),
    functional (filterDilatedRevCode.functionalWindow 64 0 59 (-1) 60 order),false⟩,
  ⟨"filter_dilated_skip",imperative (filterDilatedCode.imperativeWindow 64 0 0 (1) 28 order),
    functional (filterDilatedCode.functionalWindow 64 0 0 (1) 28 order),true⟩]

def observe (s : Option State) : Option (Array Int × Array Int × Array Int) :=
  s.map (fun t => (t.arrays 0,t.arrays 1,t.arrays 2))

-- Execution checks supplement the general theorems; they are not axioms.
#eval show IO Unit from do
  for w in workloads do
    let expected := observe (w.imperative.source 0 0 initial)
    unless expected.isSome do throw (IO.userError s!"{w.name}: invalid reference input")
    unless observe (w.imperative.eval 0 0 initial) == expected do
      throw (IO.userError s!"{w.name}: imperative mismatch")
    unless observe (w.functional.eval 0 0 initial) == expected do
      throw (IO.userError s!"{w.name}: functional mismatch")
    unless w.imperative.fifo == w.expectedFIFO && w.functional.fifo == w.expectedFIFO do
      throw (IO.userError s!"{w.name}: unexpected communication selection")
    for stage in [w.imperative,w.functional] do
      let some queue := stage.queue initial | throw (IO.userError "queue initialization failed")
      let endState := WindowControl.run (arrayInput (initial.arrays 0)) 0 0 20000
        (.start (WindowControl.lower stage.code) [] initial queue)
      match endState with
      | .stopped result _ =>
        unless observe result == expected do throw (IO.userError s!"{w.name}: control mismatch")
      | _ => throw (IO.userError s!"{w.name}: insufficient control steps")
  IO.println "8 reference kernel variants: both IRs, communication choice and control execution passed"

end IRComparison.WindowWorkloads
