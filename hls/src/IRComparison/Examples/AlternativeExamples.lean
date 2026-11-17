import IRComparison.Memory.AlternativeFusion
import IRComparison.Frontend.LeanWindowCommand

namespace IRComparison.AlternativeExamples
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

def producer (_i x y : Int) (s : State) : Option State := do
  let t ← s.write 1 0 x
  let u ← if y != 0 then t.write 1 1 (x+1) else t.write 1 2 (x+2)
  u.write 1 3 (x+3)

hls_window producer as native

def consumer : List NativeWindowPlan.Block :=
  [⟨0,[.memory 0,.memory 3],.store 2 (.lit 0) (.add (.local 0) (.local 1))⟩]

def plan := (AlternativeFusion.compile 0 1 4 native.imperativeBody consumer).get (by decide +kernel)

example : plan.sender.after = [[0,1,3],[0,2,3]] := by decide +kernel
example : (plan.receiver.code.map (·.loads)) = [[.take 0,.take 1]] := by decide +kernel

def initial : State := ⟨fun _ => 0,fun _ => #[0,0,0,0]⟩
example : (plan.eval 10 1 initial).map (fun s => (s.arrays 1,s.arrays 2)) =
    some (#[],#[23,0,0,0]) := by decide +kernel
example : (plan.eval 10 0 initial).map (fun s => (s.arrays 1,s.arrays 2)) =
    some (#[],#[23,0,0,0]) := by decide +kernel

theorem native_correct (s : State) (hsize : (s.arrays 1).size = 4) (x y : Int) :
    plan.eval x y s = (do
      let t ← producer 0 x y s
      NativeWindowPlan.evalI (arrayInput (t.arrays 1)) x y consumer [] t).map (StreamConsumer.erase 1) := by
  rw [plan.correct s hsize x y]
  unfold AlternativeFusion.source
  have h : native.imperativeBody.eval 0 x y s [] = producer 0 x y s := native.imperativeBody_correct 0 x y s
  rw [h]

-- Alternatives may differ in length; the shared continuation needs only
-- the common prefix. It does not insist that every token is consumed.
def variableLength : Imperative.Cmd := .seq (.store 1 (.lit 0) .left)
  (.branch .right (.store 1 (.lit 1) (.lit 7)) .skip)
def prefixConsumer : List NativeWindowPlan.Block := [⟨0,[.memory 0],.store 2 (.lit 0) (.local 0)⟩]
def variablePlan := (AlternativeFusion.compile 0 1 4 variableLength prefixConsumer).get (by decide +kernel)
example : variablePlan.sender.after = [[0,1],[0]] := by decide +kernel
example : (variablePlan.eval 10 0 initial).map (fun s => s.arrays 2) = some #[10,0,0,0] := by decide +kernel

-- A fixed destructive-read schedule cannot fetch index 1 from both queues.
-- The complete pair is rejected, not partly transformed.
example : (AlternativeFusion.compile 0 1 4 variableLength
  [⟨0,[.memory 1],.store 2 (.lit 0) (.local 0)⟩]).isSome = false := by decide +kernel

-- The continuation's write must be fresh under every incoming alternative.
example : (StreamAlternatives.compile 0 1 4 [[]]
  (.seq variableLength (.store 1 (.lit 1) (.lit 8)))).isSome = false := by decide +kernel

end IRComparison.AlternativeExamples
