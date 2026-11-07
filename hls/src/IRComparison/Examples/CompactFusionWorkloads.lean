import IRComparison.Memory.CompactFusionControl
import IRComparison.Examples.StreamWorkloads

namespace IRComparison.CompactFusionWorkloads
open WindowWorkloads

structure Workload where
  name : String
  start : Int
  stride : Int
  count : Nat
  imperative : SymbolicWindowLoop.Code
  functional : SymbolicWindowLoop.Code

def workloads : List Workload := [
  ⟨"filter",0,(1),62,
    (filterCode.imperativeCompactWindow 64 0 0 (1) 62).code,
    (filterCode.functionalCompactWindow 64 0 0 (1) 62).code⟩,
  ⟨"filter_alt",0,(1),62,
    (filterAltCode.imperativeCompactWindow 64 0 0 (1) 62).code,
    (filterAltCode.functionalCompactWindow 64 0 0 (1) 62).code⟩,
  ⟨"filter_rev",61,(-1),62,
    (filterCode.imperativeCompactWindow 64 0 61 (-1) 62).code,
    (filterCode.functionalCompactWindow 64 0 61 (-1) 62).code⟩,
  ⟨"filter_skip",0,(1),30,
    (filterSkipCode.imperativeCompactWindow 64 0 0 (1) 30).code,
    (filterSkipCode.functionalCompactWindow 64 0 0 (1) 30).code⟩,
  ⟨"filter_dilated",0,(1),28,
    (filterDilatedCode.imperativeCompactWindow 64 0 0 (1) 28).code,
    (filterDilatedCode.functionalCompactWindow 64 0 0 (1) 28).code⟩,
  ⟨"filter_dilated_alt",0,(1),28,
    (filterDilatedAltCode.imperativeCompactWindow 64 0 0 (1) 28).code,
    (filterDilatedAltCode.functionalCompactWindow 64 0 0 (1) 28).code⟩,
  ⟨"filter_dilated_rev",59,(-1),60,
    (filterDilatedRevCode.imperativeCompactWindow 64 0 59 (-1) 60).code,
    (filterDilatedRevCode.functionalCompactWindow 64 0 59 (-1) 60).code⟩,
  ⟨"filter_dilated_skip",0,(1),28,
    (filterDilatedCode.imperativeCompactWindow 64 0 0 (1) 28).code,
    (filterDilatedCode.functionalCompactWindow 64 0 0 (1) 28).code⟩ ]

#eval show IO Unit from do
  for w in workloads do
    let sinkI := (StreamWorkloads.sink.imperativeCompactWindow 64 1 w.start w.stride w.count).code
    let sinkF := (StreamWorkloads.sink.functionalCompactWindow 64 1 w.start w.stride w.count).code
    for (producer,consumer) in [(w.imperative,sinkI),(w.functional,sinkF)] do
      let some p := CompactFusion.compile 0 1 64 producer consumer |
        throw (IO.userError s!"{w.name}: compact fusion was not selected")
      let expected := (CompactFusion.source 0 1 producer consumer 0 0 initial).map (fun s => (#[],s.arrays 2))
      unless expected.isSome && (p.eval 0 0 initial).map (fun s => (s.arrays 1,s.arrays 2)) == expected do
        throw (IO.userError s!"{w.name}: compact fusion differs")
      match CompactFusionControl.run 1 p.sender.code p.receiver.code (arrayInput (initial.arrays 0)) 0 0 40000
          (.producer (.start (StreamConsumer.erase 1 initial))) with
      | .stopped r => unless r.map (fun s => (s.arrays 1,s.arrays 2)) == expected do
          throw (IO.userError s!"{w.name}: compact control differs")
      | _ => throw (IO.userError s!"{w.name}: compact control did not finish")
  IO.println "8 reference kernels x 2 IRs: compact loops, producer sends, FIFO consumer, removed middle array and control passed"

end IRComparison.CompactFusionWorkloads
