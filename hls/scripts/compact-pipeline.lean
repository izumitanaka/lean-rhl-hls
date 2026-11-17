import IRComparison.Memory.CompactTransport
import IRComparison.Examples.CompactFIFOExamples
open IRComparison IRComparison.SymbolicWindowExamples IRComparison.NativeWindowExamples

def main : IO Unit := do
  let cases := [(forward.code,CompactSequence.Seq.mk 0 1 13,List.range 13 |>.map (fun n => Int.ofNat n+1)),
    (strided.code,CompactSequence.Seq.mk 0 1 13,List.range 13 |>.map (fun n => Int.ofNat n+1)),
    (reverse.code,CompactSequence.Seq.mk 6 (-1) 7,[7,6,5,4,3,2,1]),
    (reverse.code,CompactSequence.Seq.mk 0 1 13,List.range 13 |>.map (fun n => Int.ofNat n+1))]
  for ((code,sequence,queue),n) in cases.zipIdx do
    let (_,compiled) ← CompactTransport.solveAndSelect code sequence (System.FilePath.mk "artifacts/compact-pipeline" / toString n)
    let expected := (code.eval (arrayInput (initial.arrays 0)) 0 0 initial).map (fun s => s.arrays 1)
    let actual := (compiled.eval (arrayInput (initial.arrays 0)) 0 0 initial queue).map (fun s => s.arrays 1)
    unless expected == actual do throw (IO.userError s!"incorrect output in case {n}")
    match compiled.selected with
    | .fifo _ => if n == 3 then throw (IO.userError "wrong-order supplier was accepted")
    | .memory => if n != 3 then throw (IO.userError s!"expected FIFO in case {n}")
  let (_,large) ← CompactTransport.solveAndSelect billion.code ⟨0,1,1000000004⟩ "artifacts/compact-pipeline/billion"
  match large.selected with
  | .memory => throw (IO.userError "large compact pipeline fell back")
  | .fifo plan =>
    unless plan.code.initial.length == 5 && plan.code.refill.length == 5 do
      throw (IO.userError "code size depends on count")
  IO.println "SMT -> compact FIFO selection -> execution: forward, stride 2, reverse passed; wrong order retained memory; billion-count code stayed compact"
