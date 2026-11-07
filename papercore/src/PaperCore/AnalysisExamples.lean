import PaperCore.WindowAnalysis
import PaperCore.Evaluator

namespace PaperCore.AnalysisExamples
open AccessAnalysis LoopAnalysis

inductive Op where
  | add | sub | mul
  deriving Repr, DecidableEq

def meaning : Op → Int → Int → Int
  | .add => (· + ·)
  | .sub => (· - ·)
  | .mul => (· * ·)

def classify : Op → Option Arithmetic
  | .add => some .add
  | .sub => some .sub
  | .mul => some .mul

theorem arithmetic_sound : ArithmeticSound classify meaning := by
  intro op kind known x y
  cases op <;> simp [classify] at known <;> subst kind <;> rfl

/-- Independently written input, not one of the scan/sliding fixtures. -/
def customBody : Source Op :=
  .seq (.assign "radius" (.num 2))
    (.seq (.assign "position" (.bin .add "cursor" "radius"))
      (.seq (.action (.read "sample" "pixels" (.var "position")))
        (.seq (.assign "radius" (.num 6))
          (.seq (.assign "position" (.bin .add "cursor" "radius"))
            (.action (.read "neighbor" "pixels" (.var "position")))))))

def customLoop : Source Op := .loop "cursor" (.num 3) 21 2 customBody

def customInfo : Info Op :=
  ⟨"cursor",.num 3,21,2,[⟨.read,"pixels",⟨1,2⟩⟩,⟨.read,"pixels",⟨1,6⟩⟩],some ⟨1,0⟩⟩

example : inspect classify customLoop = .ok customInfo := rfl
example : WindowAnalysis.infer "pixels" customInfo.accesses =
    .ok ⟨"pixels",1,2,6,[2,6]⟩ := rfl

/-- The inferred window covers gaps, but this example does not assert that
    the missing cells can safely be prefetched. Only indices 5 and 9 exist. -/
def state : State Heap := ⟨[("cursor",3)],[(("pixels",5),42),(("pixels",9),99)]⟩

theorem custom_trace : ∃ t, SourceExec meaning customBody state t ∧
    AccessTrace meaning customBody state t [⟨.read,"pixels",5⟩,⟨.read,"pixels",9⟩] := by
  have evaluated : ∃ t, run meaning (memoryRun meaning) 20 customBody state = some t := ⟨_,rfl⟩
  obtain ⟨t,success⟩ := evaluated
  have executed := run_sound meaning (memoryRun meaning) (MemoryStep meaning)
    (fun _ _ _ h => memoryRun_sound meaning h) success
  refine ⟨t,executed,?_⟩
  exact (inspect_sound arithmetic_sound (info := customInfo) (start := .num 3) (counter := "cursor") (k := 3)
    (stop := 21) (step := 2) rfl rfl executed).1

def changedCounter : Source Op := .loop "cursor" (.num 0) 10 1
  (.seq (.assign "one" (.num 1))
    (.seq (.assign "cursor" (.bin .add "cursor" "one"))
      (.action (.read "out" "pixels" (.var "cursor")))))

example : inspect classify changedCounter =
    .ok ⟨"cursor",.num 0,10,1,[⟨.read,"pixels",⟨1,1⟩⟩],some ⟨1,1⟩⟩ := rfl

def forgottenIndex : Source Op := .loop "cursor" (.num 0) 10 1
  (.seq (.assign "ptr" (.var "cursor"))
    (.seq (.action (.read "ptr" "pixels" (.var "cursor")))
      (.action (.read "out" "pixels" (.var "ptr")))))

example : inspect classify forgottenIndex = .error "unknown-read-index:pixels" := rfl

def unrelatedMultiply : Source Op := .loop "cursor" (.num 0) 10 1
  (.seq (.assign "junk" (.bin .mul "cursor" "cursor"))
    (.action (.read "out" "pixels" (.var "cursor"))))

example : inspect classify unrelatedMultiply =
    .ok ⟨"cursor",.num 0,10,1,[⟨.read,"pixels",⟨1,0⟩⟩],some ⟨1,0⟩⟩ := rfl

def nonlinearIndex : Source Op := .loop "cursor" (.num 0) 10 1
  (.seq (.assign "position" (.bin .mul "cursor" "cursor"))
    (.action (.read "out" "pixels" (.var "position"))))

example : inspect classify nonlinearIndex = .error "unknown-read-index:pixels" := rfl

def branchingBody : Source Op := .loop "cursor" (.num 0) 10 1
  (.branch "flag" (.action (.read "out" "pixels" (.var "cursor")))
    (.assign "out" (.num 0)))

example : inspect classify branchingBody = .error "branch-dependent-access-sequence-not-yet-supported" := rfl

example : ((sites (.branch "flag" customLoop changedCounter)).map (·.path)) = [[0],[1]] := rfl
example : ((sites (.loop "outer" (.num 0) 2 1 customLoop)).map (·.path)) = [[],[0]] := rfl

example : WindowAnalysis.infer "pixels"
    [⟨.read,"pixels",⟨1,0⟩⟩,⟨.read,"pixels",⟨2,0⟩⟩] =
    .error "window-analysis-nonuniform-index-scale" := rfl
example : WindowAnalysis.infer "pixels"
    [⟨.read,"pixels",⟨1,0⟩⟩,⟨.write,"pixels",⟨1,1⟩⟩] =
    .error "window-analysis-read-write-array-not-yet-supported" := rfl

#print axioms custom_trace
end PaperCore.AnalysisExamples
