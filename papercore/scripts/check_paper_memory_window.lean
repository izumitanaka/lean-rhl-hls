import PaperCore.MemoryWindowPlan
import PaperCore.StagedCertified
import PaperCore.MixedEvaluator
import PaperCore.AnalysisExamples

open PaperCore PaperCore.AnalysisExamples

def producer : Source Op := .loop "p" (.num 0) 32 1
  (.seq (.assign "v" (.bin .mul "p" "p")) (.action (.write "input" (.var "p") "v")))

def body (scale offset gap : Int) : Source Op :=
  MemoryWindowSchedule.prepend [
    .assign "factor" (.num scale),
    .assign "address" (.bin .mul "factor" "i"),
    .assign "offset" (.num offset),
    .assign "address" (.bin .add "address" "offset"),
    .action (.read "x" "input" (.var "address")),
    .assign "gap" (.num gap),
    .assign "address" (.bin .add "address" "gap"),
    .action (.read "y" "input" (.var "address")),
    .assign "result" (.bin .sub "x" "y")]
    (.action (.write "output" (.var "i") "result"))

def check (name : String) (start stop step scale offset gap : Int) : IO Unit := do
  let loop : Source Op := .loop "i" (.num start) stop step (body scale offset gap)
  let original := Stmt.seq producer loop
  let .ok candidate := MemoryWindowPlan.prepare classify .add .mul (BufferNames.sourceVars original) loop
    | throw (IO.userError (name ++ ": candidate rejected"))
  let transformed := Stmt.seq producer candidate.code
  let some left := run meaning (memoryRun meaning) 10000 original ⟨[],[]⟩
    | throw (IO.userError (name ++ ": original execution failed"))
  let some middle := run meaning (memoryRun meaning) 10000 transformed ⟨[],[]⟩
    | throw (IO.userError (name ++ ": window execution failed"))
  unless left.memory == middle.memory do throw (IO.userError (name ++ ": memory differs"))
  for x in BufferNames.sourceVars original do
    unless left.regs.lookup x == middle.regs.lookup x do
      throw (IO.userError (name ++ ": original register differs: " ++ x))
  let artifact ← StagedCertified.compileSourceWithPolicy classify .add .mul original
    ["output"] ("artifacts/paper-memory-window/" ++ name)
  unless artifact.memoryPass.code == transformed do
    throw (IO.userError (name ++ ": certified prepass did not adopt expected window"))
  let some right := run meaning (MixedTarget.actionRun meaning) 10000 artifact.backend.code
      ⟨[],([],ProgramState.emptyStreams ["output"])⟩
    | throw (IO.userError (name ++ ": mixed execution failed"))
  for ((a,i),v) in left.memory do
    if a != "output" then
      unless right.memory.1.lookup (a,i) == some v do throw (IO.userError "retained memory differs")
  unless artifact.backend.after.any (fun q =>
      match (q "output").sequence.mapM (fun i => left.memory.lookup ("output",i)) with
      | none => false
      | some values => right.memory.2.lookup "output" == some values) do
    throw (IO.userError (name ++ ": FIFO output differs"))
  IO.FS.writeFile ("artifacts/paper-memory-window/" ++ name ++ "/buffered.txt") (reprStr transformed)
  IO.println (name ++ ": certified original -> memory-window -> input-memory/output-FIFO; overlap=" ++
    toString candidate.overlap ++ ", refill=" ++ toString candidate.reload)

def checkGap : IO Unit := do
  let sparse : Source Op := .loop "p" (.num 0) 4 2 (.action (.write "input" (.var "p") "p"))
  let original : Source Op := .seq sparse (.loop "i" (.num 0) 1 1 (body 1 0 2))
  let prepared := MemoryBufferPass.compile classify .add .mul original
  unless prepared.notes.contains "memory-window-prefetch-not-proved:input" do
    throw (IO.userError "uninitialized gap was not reported")
  unless prepared.pass.code == original do throw (IO.userError "buffer was inserted across an uninitialized gap")
  let some left := run meaning (memoryRun meaning) 100 original ⟨[],[]⟩
    | throw (IO.userError "gap source should terminate")
  unless left.memory.lookup ("input",1) == none do throw (IO.userError "gap fixture is not sparse")
  IO.println "uninitialized-gap: buffering declined, valid original retained"

def checkPolicies : IO Unit := do
  let original : Source Op := .seq producer (.loop "i" (.num 0) 5 1 (body 1 0 2))
  let allFifo ← StagedCertified.compileSourceWithPolicy classify .add .mul original ["input","output"]
    "artifacts/paper-memory-window/policy-all"
  let retained ← StagedCertified.compileSourceWithPolicy classify .add .mul original ["output"]
    "artifacts/paper-memory-window/policy-retained"
  unless allFifo.memoryPass.code == retained.memoryPass.code do
    throw (IO.userError "FIFO policy changed independently inserted buffer")
  let some left := run meaning (memoryRun meaning) 10000 original ⟨[],[]⟩
    | throw (IO.userError "policy source failed")
  for artifact in [allFifo,retained] do
    let backend := artifact.backend
    let some right := run meaning (MixedTarget.actionRun meaning) 10000 backend.code
        ⟨[],([],ProgramState.emptyStreams backend.fifoArrays)⟩
      | throw (IO.userError "policy target failed")
    unless backend.after.any (fun q => backend.fifoArrays.all (fun a =>
        match (q a).sequence.mapM (fun i => left.memory.lookup (a,i)) with
        | none => false
        | some values => right.memory.2.lookup a == some values)) do
      throw (IO.userError "policy FIFO contents differ")
  IO.println "both-storage-policies: identical buffer program, correct FIFO contents"

def checkLiteralGuards : IO Unit := do
  for (name,count,index) in [("empty",0,0),("wrong-head",3,1)] do
    let original : Source Op := .seq (.loop "p" (.num 0) count 1 (.action (.write "a" (.var "p") "p")))
      (.action (.read "x" "a" (.num index)))
    let rejected ← try
      let _ ← StagedCertified.compileSourceWithPolicy classify .add .mul original ["a"]
        ("artifacts/paper-memory-window/literal-" ++ name)
      pure false
    catch _ => pure true
    unless rejected do throw (IO.userError ("invalid literal FIFO read accepted: " ++ name))
  IO.println "literal-preloads: empty FIFO and wrong head rejected"

def main : IO Unit := do
  check "ascending" 0 5 1 1 0 2
  check "negative-index-coefficient" 0 5 1 (-1) 9 (-2)
  check "negative-loop-step" 5 0 (-1) 1 0 2
  check "step-two" 0 6 2 1 0 4
  check "negative-step-two" 6 0 (-2) 1 0 4
  check "scale-two" 0 3 1 2 0 4
  check "negative-scale-two" 0 3 1 (-2) 12 (-4)
  check "empty-loop" 0 0 1 1 0 2
  checkGap
  checkPolicies
  checkLiteralGuards

#print axioms MemoryBufferPass.compile
#print axioms MemoryWindowPlan.Candidate.program_forward
#print axioms MemoryWindowPlan.Candidate.program_backward
#print axioms StagedCertified.Artifact.forward
#print axioms StagedCertified.Artifact.backward
