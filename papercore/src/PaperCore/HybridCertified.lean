import PaperCore.HybridSolver

namespace PaperCore.Hybrid.Certified
open AccessAnalysis QueueInterface

/-- The accepted plan fixes storage per array for the entire source. -/
structure Artifact (classify : Op → Option Arithmetic) (source : Source Op) where
  fifoArrays : List Array
  plan : Pipeline.Plan classify (BufferNames.sourceVars source) fifoArrays source
  replies : Alternatives.Replies plan
  verifiedQueries : Nat
  code : MixedTarget.Code Op
  after : List Queues
  accepted : Alternatives.build plan [QueueInterface.empty] replies = some (code,after)
  consistent : MixedTarget.respects (fun a => if a ∈ fifoArrays then .fifo else .memory) code = true

variable {Op : Type} {classify : Op → Option Arithmetic} {source : Source Op}

def compileWithPolicy (classify : Op → Option Arithmetic) (source : Source Op)
    (fifoArrays : List Array) (directory : String) : IO (Artifact classify source) := do
  let plan ← match Pipeline.prepareClosed classify source fifoArrays with
    | .ok p => pure p
    | .error reason => throw (IO.userError ("preparation failed: " ++ reason))
  let (replies,_,count) ← Alternatives.solve plan [QueueInterface.empty] directory
  match accepted : Alternatives.build plan [QueueInterface.empty] replies with
  | none => throw (IO.userError "mixed transformation failed final acceptance")
  | some (code,after) =>
    if consistent : MixedTarget.respects (fun a => if a ∈ fifoArrays then .fifo else .memory) code = true then
      return ⟨fifoArrays,plan,replies,count,code,after,accepted,consistent⟩
    else throw (IO.userError "mixed transformation violates program-wide storage policy")

/-- Enumerate storage policies, preferring more FIFO arrays. Failed candidates
never escape. This is a finite search strategy, not a restriction of the input
language or an assumption of the correctness theorem. -/
def policies : List Array → List (List Array)
  | [] => [[]]
  | a :: rest => let tail := policies rest; tail.map (a :: ·) ++ tail

def compile (classify : Op → Option Arithmetic) (source : Source Op) (directory : String) :
    IO (Artifact classify source) := do
  IO.FS.createDirAll directory
  let arrays := (ProgramState.sourceArrays source).eraseDups
  let candidates := (policies arrays).mergeSort (fun a b => a.length ≥ b.length)
  let mut report := ""
  let mut n := 0
  for selected in candidates do
    let trial := directory ++ "/policy-" ++ toString n
    n := n+1
    try
      let artifact ← compileWithPolicy classify source selected trial
      report := report ++ "accepted FIFO arrays: " ++ reprStr selected ++ "\n"
      IO.FS.writeFile (directory ++ "/storage-decisions.txt") report
      return artifact
    catch error =>
      report := report ++ "not adopted FIFO arrays: " ++ reprStr selected ++ "; " ++ error.toString ++ "\n"
  IO.FS.writeFile (directory ++ "/storage-decisions.txt") report
  throw (IO.userError "no mixed storage policy accepted; see storage-decisions.txt")

def Artifact.SolverSound (artifact : Artifact classify source) : Prop :=
  Alternatives.SoundReplies artifact.plan artifact.replies

theorem Artifact.forward (artifact : Artifact classify source) (ops : ArithmeticSound classify meaning)
    (solver : artifact.SolverSound) (run : SourceExec meaning source ⟨regs,[]⟩ out) :
    ∃ targetOut indices, MixedTarget.Execution meaning artifact.code
        ⟨regs,([],ProgramState.emptyStreams artifact.fifoArrays)⟩ targetOut ∧
      Related (fun x => x ∈ BufferNames.sourceVars source) (fun a => a ∈ artifact.fifoArrays)
        (Alternatives.HoldsAny artifact.fifoArrays artifact.after) out targetOut indices :=
  Alternatives.build_closed_forward artifact.plan ops artifact.accepted solver run

theorem Artifact.backward (artifact : Artifact classify source) (ops : ArithmeticSound classify meaning)
    (solver : artifact.SolverSound)
    (run : MixedTarget.Execution meaning artifact.code
      ⟨regs,([],ProgramState.emptyStreams artifact.fifoArrays)⟩ targetOut) :
    ∃ out indices, SourceExec meaning source ⟨regs,[]⟩ out ∧
      Related (fun x => x ∈ BufferNames.sourceVars source) (fun a => a ∈ artifact.fifoArrays)
        (Alternatives.HoldsAny artifact.fifoArrays artifact.after) out targetOut indices :=
  Alternatives.build_closed_backward artifact.plan ops artifact.accepted solver run

#print axioms Artifact.forward
#print axioms Artifact.backward
end PaperCore.Hybrid.Certified
