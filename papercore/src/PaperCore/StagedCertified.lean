import PaperCore.MemoryBufferPass
import PaperCore.SourcePass
import PaperCore.HybridCertified

namespace PaperCore.StagedCertified
open AccessAnalysis

/-- The memory program is fixed before the storage policy search starts. -/
structure Artifact (classify : Op → Option Arithmetic) (source : Source Op) where
  memoryPass : SourcePass.Prepared classify source
  backend : Hybrid.Certified.Artifact classify memoryPass.code

/-- This entry point consumes an independently certified memory pass. In
particular, a failed FIFO trial cannot undo its buffer insertion. -/
def compile (pass : SourcePass.Prepared classify source) (directory : String) :
    IO (Artifact classify source) := do
  let backend ← Hybrid.Certified.compile classify pass.code directory
  return ⟨pass,backend⟩

def compileWithPolicy (pass : SourcePass.Prepared classify source) (arrays : List Array)
    (directory : String) : IO (Artifact classify source) := do
  let backend ← Hybrid.Certified.compileWithPolicy classify pass.code arrays directory
  return ⟨pass,backend⟩

/-- Main two-stage entry: decide and certify memory buffering once, then
search FIFO policies on that fixed intermediate program. -/
def compileSource (classify : Op → Option Arithmetic) (add mul : Op) (source : Source Op)
    (directory : String) : IO (Artifact classify source) := do
  let memory := MemoryBufferPass.compile classify add mul source
  IO.FS.createDirAll directory
  IO.FS.writeFile (directory ++ "/buffer-decisions.txt") (String.intercalate "\n" memory.notes)
  compile memory.pass directory

def compileSourceWithPolicy (classify : Op → Option Arithmetic) (add mul : Op) (source : Source Op)
    (arrays : List Array) (directory : String) : IO (Artifact classify source) := do
  let memory := MemoryBufferPass.compile classify add mul source
  IO.FS.createDirAll directory
  IO.FS.writeFile (directory ++ "/buffer-decisions.txt") (String.intercalate "\n" memory.notes)
  compileWithPolicy memory.pass arrays directory

/-- Transport the backend's result to the actual original program, rather
than silently changing the guarantee's starting point to buffered code. -/
theorem transport (pass : SourcePass.Prepared classify source)
    (agrees : SourcePass.Agrees (fun x => x ∈ BufferNames.sourceVars source) original buffered)
    (related : Hybrid.Related (fun x => x ∈ BufferNames.sourceVars pass.code) fifo post
      buffered target indices) :
    Hybrid.Related (fun x => x ∈ BufferNames.sourceVars source) fifo post original target indices := by
  refine ⟨⟨⟨?_,?_⟩,?_⟩,?_⟩
  · intro x hx
    exact (agrees.registers x hx).trans (related.1.registers x (pass.names x hx))
  · intro a ha
    simpa only [agrees.memory] using related.1.streams.streams a ha
  · intro a ha i
    simpa only [agrees.memory] using related.1.memory a ha i
  · simpa only [agrees.memory] using related.2

def Artifact.SolverSound (artifact : Artifact classify source) : Prop := artifact.backend.SolverSound

theorem Artifact.forward (artifact : Artifact classify source) (ops : ArithmeticSound classify meaning)
    (solver : artifact.SolverSound) (run : SourceExec meaning source ⟨regs,[]⟩ out) :
    ∃ targetOut indices, MixedTarget.Execution meaning artifact.backend.code
        ⟨regs,([],ProgramState.emptyStreams artifact.backend.fifoArrays)⟩ targetOut ∧
      Hybrid.Related (fun x => x ∈ BufferNames.sourceVars source) (fun a => a ∈ artifact.backend.fifoArrays)
        (Hybrid.Alternatives.HoldsAny artifact.backend.fifoArrays artifact.backend.after) out targetOut indices := by
  obtain ⟨buffered,executed,agrees⟩ := (artifact.memoryPass.correct meaning ops).forward _ _ run
  obtain ⟨target,indices,compiled,related⟩ := artifact.backend.forward ops solver executed
  exact ⟨target,indices,compiled,transport artifact.memoryPass agrees related⟩

theorem Artifact.backward (artifact : Artifact classify source) (ops : ArithmeticSound classify meaning)
    (solver : artifact.SolverSound)
    (run : MixedTarget.Execution meaning artifact.backend.code
      ⟨regs,([],ProgramState.emptyStreams artifact.backend.fifoArrays)⟩ targetOut) :
    ∃ out indices, SourceExec meaning source ⟨regs,[]⟩ out ∧
      Hybrid.Related (fun x => x ∈ BufferNames.sourceVars source) (fun a => a ∈ artifact.backend.fifoArrays)
        (Hybrid.Alternatives.HoldsAny artifact.backend.fifoArrays artifact.backend.after) out targetOut indices := by
  obtain ⟨buffered,indices,executed,related⟩ := artifact.backend.backward ops solver run
  obtain ⟨out,original,agrees⟩ := (artifact.memoryPass.correct meaning ops).backward _ _ executed
  exact ⟨out,indices,original,transport artifact.memoryPass agrees related⟩

#print axioms Artifact.forward
#print axioms Artifact.backward
end PaperCore.StagedCertified
