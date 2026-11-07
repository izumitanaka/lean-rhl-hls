import PaperCore.CertifiedPipeline
import PaperCore.MixedEvaluator
import PaperCore.AnalysisExamples

open PaperCore PaperCore.AnalysisExamples

def sequence (head : Source Op) (tail : List (Source Op)) : Source Op :=
  match tail with
  | [] => head
  | next :: rest => .seq head (sequence next rest)

/-- Different values at each address and subtraction make reversed slots observable. -/
def producer (first stop step : Int) : Source Op :=
  .loop "p" (.num first) stop step (sequence
    (.assign "value" (.bin .mul "p" "p"))
    [.action (.write "input" (.var "p") "value")])

def body (factor : Int) (gap : Nat) (update : Int := 0) (branched : Bool := false) : Source Op :=
  let readBody := sequence (.assign "factor" (.num factor))
    [.assign "address" (.bin .mul "i" "factor"),
     .action (.read "left" "input" (.var "address")),
     .assign "gap" (.num gap),
     .assign "address" (.bin .add "address" "gap"),
     .action (.read "right" "input" (.var "address")),
     .assign "difference" (.bin .sub "left" "right"),
     .action (.write "output" (.var "i") "difference")]
  let selected := if branched then .branch "i" readBody readBody else readBody
  sequence selected [.assign "update" (.num update), .assign "i" (.bin .add "i" "update")]

def check (name : String) (start step factor : Int) (gap trips : Nat)
    (update : Int := 0) (branched : Bool := false) (leftover : Nat := 0) : IO Unit := do
  let delta := step+update
  let movement := factor*delta
  let reverse := movement < 0
  let direction : Int := if reverse then -1 else 1
  let stop := start+(trips:Int)*delta
  let middle : Source Op := .loop "i" (.num start) stop step (body factor gap update branched)
  let .ok p := MemoryWindowPlan.prepare classify .add .mul [] middle
    | throw (IO.userError (name ++ ": preparation rejected"))
  if p.reverse != reverse || p.counterDelta != delta || p.trips != trips then
    throw (IO.userError (name ++ ": wrong signed schedule"))
  if !(p.overlap > 0 && p.reload > 0) then
    throw (IO.userError (name ++ ": test did not select a buffer"))
  let first := factor*start+(if reverse then (gap:Int) else 0)
  let required := if start == stop then 0 else gap+1-movement.natAbs+trips*movement.natAbs
  let source : Source Op := .seq (producer first (first+((required+leftover:Nat):Int)*direction) direction) (.kernel middle)
  let directory := "artifacts/paper-reverse-window/" ++ name
  let staged ← CertifiedPipeline.compileBufferedWithPolicy classify .add .mul source ["input","output"] directory
  let artifact := staged.backend
  IO.FS.writeFile (directory ++ "/source.txt") (reprStr source)
  IO.FS.writeFile (directory ++ "/target.txt") (reprStr artifact.code)
  let some left := run meaning (memoryRun meaning) 10000 source ⟨[],[]⟩
    | throw (IO.userError (name ++ ": source execution failed"))
  let some right := run meaning (MixedTarget.actionRun meaning) 10000 artifact.code
      ⟨[],([],ProgramState.emptyStreams artifact.fifoArrays)⟩
    | throw (IO.userError (name ++ ": target execution failed"))
  for x in (BufferNames.sourceVars source).eraseDups do
    if left.regs.lookup x != right.regs.lookup x then
      throw (IO.userError (name ++ ": register mismatch: " ++ x))
  if !artifact.after.any (fun queues => (ProgramState.sourceArrays source).eraseDups.all (fun a =>
      match (queues a).sequence.mapM (fun i => left.memory.lookup (a,i)) with
      | none => false
      | some values => right.memory.2.lookup a == some values)) then
    throw (IO.userError (name ++ ": output sequence or unused FIFO tail mismatch"))
  IO.println (name ++ ": SMT accepted; all source registers and every remaining FIFO value agree")

def reject (name : String) (source : Source Op) (reason : String) : IO Unit := do
  match MemoryWindowPlan.prepare classify .add .mul [] source with
  | .error actual =>
    if actual != reason then throw (IO.userError (name ++ ": wrong rejection: " ++ actual))
  | .ok _ => throw (IO.userError (name ++ ": unexpectedly accepted"))
  IO.println (name ++ ": rejected with explicit reason")

def main : IO Unit := do
  check "descending-unit" 8 (-1) 1 2 7
  check "descending-step2" 12 (-2) 1 4 5
  check "descending-step3-gapped" 15 (-3) 1 6 4
  check "descending-scaled-index" 8 (-2) 2 6 3
  check "ascending-counter-negative-index" 0 1 (-1) 4 5
  check "ascending-counter-negative-index-step2" 0 2 (-2) 6 3
  check "descending-counter-negative-index" 8 (-2) (-1) 4 3
  check "negative-indices" (-3) (-1) 1 3 4
  check "descending-single-iteration" 6 (-2) 1 4 1
  check "descending-empty" 6 (-2) 1 4 0
  check "descending-with-tail" 8 (-1) 1 2 5 0 false 3
  check "descending-branch" 2 (-1) 1 2 4 0 true
  check "descending-net-step2" 8 (-1) 1 4 4 (-1)
  check "ascending-net-step2" 0 1 1 4 4 1
  reject "unreachable-negative-stop" (.loop "i" (.num 8) 1 (-2) (body 1 4))
    "memory-window-endpoint-not-reached"
  reject "wrong-way" (.loop "i" (.num 0) 4 (-1) (body 1 4))
    "memory-window-endpoint-not-reached"
  reject "zero-step" (.loop "i" (.num 0) 4 0 (body 1 4))
    "memory-window-zero-net-step"
  -- A descending consumer cannot silently reinterpret an ascending producer.
  let incompatible : Source Op := .seq (producer 0 8 1)
    (.loop "i" (.num 5) (-1) (-1) (body 1 2))
  let rejected ← try
    let _ ← CertifiedPipeline.compileBufferedWithPolicy classify .add .mul incompatible ["input","output"] "artifacts/paper-reverse-window/wrong-producer-order"
    pure false
  catch _ => pure true
  if !rejected then throw (IO.userError "incompatible producer order accepted")
  IO.println "incompatible producer order: SMT does not adopt the transformation"

#print axioms StagedCertified.Artifact.forward
#print axioms StagedCertified.Artifact.backward
