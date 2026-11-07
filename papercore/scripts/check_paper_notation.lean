import PaperCore.Notation
import PaperCore.CertifiedPipeline
import PaperCore.AnalysisExamples

open PaperCore PaperCore.AnalysisExamples

def N : Int := 4

def readable : Source Op := paper {
  value := -3;
  for i := 0 to #N step 1 {
    input[i] := value;
  }
  kernel {
    for i := 3 to -1 step -1 {
      x := input[i];
      if x then {
        y := x + value;
      } else {
        y := x [op| Op.sub] value;
      }
      output[i] := y;
    }
  }
}

/-- The notation is exactly the old AST, checked by Lean's kernel, not a
separately trusted parser/normalizer. Covers sequencing and nested control. -/
example : readable =
  .seq (.assign "value" (.num (-3)))
    (.seq (.loop "i" (.num 0) N 1 (.action (.write "input" (.var "i") "value")))
      (.kernel (.loop "i" (.num 3) (-1) (-1)
        (.seq (.action (.read "x" "input" (.var "i")))
          (.seq (.branch "x" (.assign "y" (.bin .add "x" "value"))
              (.assign "y" (.bin .sub "x" "value")))
            (.action (.write "output" (.var "i") "y"))))))) := rfl

example : readable.wellFormed = true := rfl

example : (paper { x := y; } : Source Op) = .assign "x" (.var "y") := rfl
example : (paper { x := a[i * k]; } : Source Op) =
  .action (.read "x" "a" (.bin .mul "i" "k")) := rfl

-- Kernel nesting remains representable at the raw AST level, but is rejected
-- by the existing wellFormed condition; the notation does not change it.
example : (paper { kernel { kernel { x := 0; } } } : Source Op).wellFormed = false := rfl

def main : IO Unit := do
  let some result := run meaning (memoryRun meaning) 100 readable ⟨[],[]⟩
    | throw (IO.userError "readable reverse-loop execution failed")
  for i in List.range 4 do
    unless result.memory.lookup ("output",(i:Int)) == some (-6) do
      throw (IO.userError "reverse-loop output mismatch")
  IO.println "notation: definitional AST equality, parameter constants, branch and reverse loop checked"

-- The public guarantee applies to every source, not just the examples above.
#check @CertifiedPipeline.forward
#check @CertifiedPipeline.backward
#print axioms CertifiedPipeline.forward
#print axioms CertifiedPipeline.backward
