import IRComparison.Core.CommunicationIR
import IRComparison.Examples.OptimizedControlExamples
import IRComparison.Examples.SnapshotLoopExamples

namespace IRComparison.CommunicationExamples
open CommunicationIR ProgramControlIR OptimizedControlExamples
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

def order : List Int := [0,1,2,3]
def iCode := filtered.imperativeOptimizedControl 0 1 3 0 1
def fCode := filtered.functionalOptimizedControl 0 1 3 0 1
def iTransport := compile 100 iCode 0 order
def fTransport := compile 100 fCode 0 order

example : iTransport.isFIFO = true := by decide +kernel
example : fTransport.isFIFO = true := by decide +kernel
example : (plan 100 iCode 0).map (·.addresses) = some order := by decide +kernel
-- The original two-read loop repeats addresses: buffering makes this order compatible.
example : (compile 100 (loopCode 0 1 3 0 1 filtered.imperativeControl) 0 order).isFIFO = false := by decide +kernel
example : observe (iTransport.execute (arrayInput #[1,2,3,4]) [1,2,3,4] initial ProgramControlIR.initial 500) =
    some (some #[3,5,7,0,0]) := by decide +kernel
example : observe (fTransport.execute (arrayInput #[1,2,3,4]) [1,2,3,4] initial ProgramControlIR.initial 500) =
    some (some #[3,5,7,0,0]) := by decide +kernel
example : (CommunicationIR.run 500 ⟨.running iCode initial ProgramControlIR.initial,[1,2,3,4]⟩).queue = [] := by decide +kernel

example : Corresponds (arrayInput #[1,2,3,4]) order [1,2,3,4] :=
  emit_correct (by decide +kernel)

-- No reuse: no buffer is inserted, and direct FIFO selection can still succeed.
def direct := compileOptimized 100 filtered.imperativeControl 0 2 3 0 1 [0,1,2,3,4,5]
example : direct.isFIFO = true := by decide +kernel
example : observe (direct.execute (arrayInput #[1,2,3,4,5,6]) [1,2,3,4,5,6] initial ProgramControlIR.initial 500) =
    some (some #[3,0,7,0,11]) := by decide +kernel

-- Descending consumption cannot use an ascending producer. The buffer remains.
def reverseMemory := compile 100 (filtered.imperativeOptimizedControl 3 (-1) 3 0 (-1)) 0 order
example : reverseMemory.isFIFO = false := by decide +kernel
example : observe (reverseMemory.execute (arrayInput #[1,2,3,4]) [] initial ProgramControlIR.initial 500) =
    some (some #[0,3,5,7,0]) := by decide +kernel
example : (compile 100 (filtered.functionalOptimizedControl 3 (-1) 3 0 (-1)) 0 [3,2,1,0]).isFIFO = true := by decide +kernel
-- A sparse producer order is accepted; dense producers needing discard are not yet rewritten.
example : (compile 100 (filtered.functionalOptimizedControl 0 2 2 0 2) 0 [0,2,4]).isFIFO = true := by decide +kernel
example : (compile 100 (filtered.functionalOptimizedControl 0 2 2 0 2) 0 [0,1,2,3,4]).isFIFO = false := by decide +kernel
-- Too little analysis fuel also keeps the original memory implementation.
example : (compile 0 iCode 0 order).isFIFO = false := rfl

-- Branches are accepted when their external read protocol agrees.
example : (compile 100 [.testReg 0 iCode fCode] 0 order).isFIFO = true := by decide +kernel
example : (compile 100 [.testReg 0 iCode []] 0 order).isFIFO = false := by decide +kernel
-- Reusing a token would be wrong: extra or missing production is not silently accepted.
example : (compile 100 iCode 0 [0,1,2]).isFIFO = false := by decide +kernel
example : (compile 100 iCode 0 [0,1,2,3,4]).isFIFO = false := by decide +kernel
example : (compile 100 (filtered.imperativeOptimizedControl 0 1 0 0 1) 0 []).isFIFO = true := by decide +kernel

-- Source body failure does not force consumption of the rest of the channel.
def tiny : State := ⟨fun _ => 0,fun _ => #[]⟩
example : (CommunicationIR.run 500 ⟨.running iCode tiny ProgramControlIR.initial,[1,2,3,4]⟩).queue = [3,4] := by decide +kernel
example : observe (iTransport.execute (arrayInput #[1,2,3,4]) [1,2,3,4] tiny ProgramControlIR.initial 500) = some none := by decide +kernel

/-- Whole-pipeline guarantee, for arbitrary native source parameters and state.
    Production correspondence is explicit, not an axiom about an SMT solver. -/
theorem native_filter_finishes (fuel : Nat) (start stride : Int) (count : Nat) (left right : Int)
    (producerOrder : List Int) (input : Input) (values : List Int) (s : State)
    (h : (compileOptimized fuel filtered.imperativeControl start stride count left right producerOrder).Contract input values) :
    ∃ steps, (compileOptimized fuel filtered.imperativeControl start stride count left right producerOrder).execute
      input values s ProgramControlIR.initial steps =
      .stopped (BodyBackends.runSource filter start stride count left right input s) :=
  compileOptimized_finishes fuel _ filter filtered.imperativeControl_correct start stride count left right producerOrder input values s h

theorem snapshot_body_finishes (fuel : Nat) (start stride : Int) (count : Nat) (left right : Int)
    (producerOrder : List Int) (input : Input) (values : List Int) (s : State)
    (h : (compileOptimized fuel SnapshotLoopExamples.nested.functionalControl start stride count left right producerOrder).Contract input values) :
    ∃ steps, (compileOptimized fuel SnapshotLoopExamples.nested.functionalControl start stride count left right producerOrder).execute
      input values s ProgramControlIR.initial steps =
      .stopped (BodyBackends.runSource SnapshotLoopExamples.nestedVersions start stride count left right input s) :=
  compileOptimized_finishes fuel _ _ SnapshotLoopExamples.nested.functionalControl_correct start stride count left right producerOrder input values s h

end IRComparison.CommunicationExamples
