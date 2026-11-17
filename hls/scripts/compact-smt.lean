import IRComparison.Memory.CompactSequence
open IRComparison.CompactSequence

def main : IO Unit := do
  let cases : List Seq := [⟨0,1,1000000000⟩,⟨63,-1,64⟩,⟨99,-7,0⟩,⟨4,99,1⟩,⟨0,2,32⟩]
  for (wanted,n) in cases.zipIdx do
    let (wire,result) ← solve wanted (System.FilePath.mk "artifacts/compact-smt" / toString n)
    let some certificate := result | throw (IO.userError s!"SMT model rejected for {repr wanted}: {wire.response}")
    unless equivalent certificate.sequence wanted do throw (IO.userError "sequence mismatch")
    unless (accept wanted wire.request "unknown").isNone do throw (IO.userError "unknown was accepted")
    unless (accept wanted wire.request "unsat").isNone do throw (IO.userError "unsat was accepted")
    unless (accept wanted (wire.request ++ "(assert false)") wire.response).isNone do
      throw (IO.userError "changed request was accepted")
  IO.println "5 real Z3 transcripts accepted; compact arithmetic rechecked; unknown/unsat/request tampering rejected"
