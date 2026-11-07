import IRComparison.Examples.HybridCompactExamples
open IRComparison IRComparison.HybridCompactExamples

def main : IO Unit := do
  let initial := NativeWindowExamples.initial
  let cases := [(forward.code,CompactSequence.Seq.mk 0 1 13,List.range 13 |>.map (fun n => Int.ofNat n+1)),
    (strided.code,CompactSequence.Seq.mk 0 1 13,List.range 13 |>.map (fun n => Int.ofNat n+1)),
    (reverse.code,CompactSequence.Seq.mk 6 (-1) 7,[7,6,5,4,3,2,1]),
    (reverse.code,CompactSequence.Seq.mk 0 1 13,List.range 13 |>.map (fun n => Int.ofNat n+1))]
  for ((code,sequence,queue),n) in cases.zipIdx do
    let (wire,compiled) ← HybridCompactTransport.solveAndSelect code sequence
      (System.FilePath.mk "artifacts/hybrid-compact-transport" / toString n)
    unless (CompactSequence.accept sequence wire.request wire.response).isSome do
      throw (IO.userError s!"{n}: real solver model was not accepted")
    for invalid in ["unknown","unsat","sat\n((first 0) (step 0) (count 0))","broken reply"] do
      unless (CompactSequence.accept sequence wire.request invalid).isNone do
        throw (IO.userError "invalid reply accepted")
    unless (CompactSequence.accept sequence (wire.request ++ "(assert false)") wire.response).isNone do
      throw (IO.userError "modified request accepted")
    let expected := (code.eval (arrayInput (initial.arrays 0)) 0 0 initial).map (fun s => s.arrays 1)
    let actual := (compiled.eval (arrayInput (initial.arrays 0)) 0 0 initial queue).map (fun s => s.arrays 1)
    unless expected == actual do throw (IO.userError s!"case {n}: output mismatch")
    match compiled.selected with
    | .fifo p =>
      if n == 3 then throw (IO.userError "wrong-order FIFO accepted")
      match HybridCompactFIFOControl.run p.code 0 0 2000 (.start initial queue) with
      | .stopped r => unless r.map (fun (s,_) => s.arrays 1) == expected do
          throw (IO.userError "FIFO control mismatch")
      | _ => throw (IO.userError "FIFO control did not finish")
    | .memory =>
      if n != 3 then throw (IO.userError s!"case {n}: expected FIFO")
      match HybridSymbolicWindowControl.run code (arrayInput (initial.arrays 0)) 0 0 2000 (.start initial) with
      | .stopped r => unless r.map (fun s => s.arrays 1) == expected do throw (IO.userError "memory control mismatch")
      | _ => throw (IO.userError "memory control did not finish")
  IO.println "Mixed counted transport: forward/stride-2/reverse/control passed; wrong order retained memory; invalid solver replies rejected"
