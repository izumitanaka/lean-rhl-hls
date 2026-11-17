import IRComparison.Examples.StreamFusionExamples
import IRComparison.Examples.WindowWorkloads

namespace IRComparison.StreamWorkloads
open WindowPipeline WindowWorkloads

/-- Consume the private filter output and produce public array 2. -/
def consume (i _x _y : Int) (s : State) : Option State := do
  let v ← (s.arrays 1)[i.toNat]?
  s.write 2 i (v+1)
hls_window consume as sink

-- Matching source iteration order is a benchmark input, not an ability to
-- reorder an incompatible existing producer. Negative cases are separate.
def traversals : List (Int × Int × Nat) :=
  [(0,1,62),(0,1,62),(61,-1,62),(0,1,30),(0,1,28),(0,1,28),(59,-1,60),(0,1,28)]

def observe (s : Option State) : Option (Array Int × Array Int × Array Int) :=
  s.map (fun t => (t.arrays 0,t.arrays 1,t.arrays 2))

def observeControl : StreamFusionControl.Config → Option (Option (Array Int × Array Int × Array Int))
  | .stopped r => some (observe r)
  | _ => none

#eval show IO Unit from do
  for (w,(start,stride,count)) in workloads.zip traversals do
    let order := (List.range count).map (fun n => start + stride * Int.ofNat n)
    let sinkI := sink.imperativeStage 64 1 start stride count order
    let sinkF := sink.functionalStage 64 1 start stride count order
    for (producer,consumer) in [(w.imperative,sinkI),(w.functional,sinkF)] do
      let some plan := StreamFusion.compile producer consumer 1 64 |
        throw (IO.userError s!"{w.name}: expected private-channel conversion")
      let expected := (do consumer.source 0 0 (← producer.source 0 0 initial)).map (StreamConsumer.erase 1)
      unless expected.isSome do throw (IO.userError s!"{w.name}: invalid source execution")
      unless observe (plan.eval 0 0 initial) == observe expected do
        throw (IO.userError s!"{w.name}: private-channel mismatch")
      let some qi := producer.queue (StreamConsumer.erase 1 initial) |
        throw (IO.userError s!"{w.name}: input initialization failed")
      let controlled := StreamFusionControl.run 1 consumer.code (arrayInput (initial.arrays 0)) 0 0 30000
        (.producer (.start plan.producerCode.code [] (StreamConsumer.erase 1 initial) qi []))
      unless observeControl controlled == some (observe expected) do
        throw (IO.userError s!"{w.name}: fused control mismatch")
  IO.println "8 reference kernels x 2 IRs: producer sends, erased intermediate array, consumer and control passed"

end IRComparison.StreamWorkloads
