import PaperCore.Notation
import PaperCore.CertifiedPipeline
import PaperCore.MixedEvaluator

namespace PaperCore.ReadableFilter
open AccessAnalysis

inductive Op where
  | add | sub | mul | div
  deriving Repr, DecidableEq

def meaning : Op → Int → Int → Int
  | .add => (· + ·)
  | .sub => (· - ·)
  | .mul => (· * ·)
  | .div => (· / ·)

def classify : Op → Option Arithmetic
  | .add => some .add
  | .sub => some .sub
  | .mul => some .mul
  | .div => none

theorem arithmetic_sound : ArithmeticSound classify meaning := by
  intro op kind known x y
  cases op <;> simp [classify] at known <;> subst kind <;> rfl

/-- Two-point filter from lang2.tex. Constants are kept as explicit variables,
just as in the paper core; no implicit expression normalization is performed. -/
def source : Source Op := paper {
  for x := 0 to 8 step 1 {
    input[x] := x;
  }
  kernel {
    for x := 0 to 7 step 1 {
      one := 1;
      two := 2;
      y0 := input[x];
      y1 := input[x + one];
      z0 := y0 + y1;
      z1 := z0 / two;
      output[x] := z1;
    }
  }
}

theorem source_wellFormed : source.wellFormed = true := rfl

/-- The readable input is definitionally the original paper-core AST. -/
theorem source_expansion : source =
  .seq (.loop "x" (.num 0) 8 1 (.action (.write "input" (.var "x") "x")))
    (.kernel (.loop "x" (.num 0) 7 1
      (.seq (.assign "one" (.num 1))
        (.seq (.assign "two" (.num 2))
          (.seq (.action (.read "y0" "input" (.var "x")))
            (.seq (.action (.read "y1" "input" (.bin .add "x" "one")))
              (.seq (.assign "z0" (.bin .add "y0" "y1"))
                (.seq (.assign "z1" (.bin .div "z0" "two"))
                  (.action (.write "output" (.var "x") "z1")))))))))) := rfl

-- General transformation guarantees live at CertifiedPipeline.forward/backward.
-- This file only supplies an input example and an execution check.
#print axioms source_expansion

end PaperCore.ReadableFilter

open PaperCore PaperCore.ReadableFilter

/-- Run the unchanged certified pipeline with the readable input. -/
def main : IO Unit := do
  let artifact ← CertifiedPipeline.compileBuffered classify .add .mul source
    "artifacts/paper-readable-filter"
  let some before := run meaning (memoryRun meaning) 1000 source ⟨[],[]⟩
    | throw (IO.userError "source execution failed")
  let some after := run meaning (MixedTarget.actionRun meaning) 1000 artifact.backend.code
      ⟨[],([],ProgramState.emptyStreams artifact.backend.fifoArrays)⟩
    | throw (IO.userError "target execution failed")
  unless artifact.backend.fifoArrays.contains "input" &&
      artifact.backend.fifoArrays.contains "output" do
    throw (IO.userError "expected both arrays to become FIFOs")
  for i in List.range 7 do
    unless before.memory.lookup ("output",(i:Int)) == some (i:Int) do
      throw (IO.userError "unexpected source output")
  unless after.memory.2.lookup "output" == some [0,1,2,3,4,5,6] do
    throw (IO.userError "unexpected target output")
  for x in BufferNames.sourceVars source do
    unless before.regs.lookup x == after.regs.lookup x do
      throw (IO.userError ("source register changed: " ++ x))
  IO.println "filter: readable input -> certified buffer/FIFO transformation; output [0,1,2,3,4,5,6]"
