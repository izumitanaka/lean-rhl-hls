import IRComparison.Memory.AlternativeProducerBlocks
import IRComparison.Memory.AlternativeRouting
import IRComparison.Memory.WindowPipeline

namespace IRComparison.AlternativeStageFusion
open StreamState StreamConsumer WindowPipeline

structure Plan (producer consumer : Stage) where
  producerCode : AlternativeProducerBlocks.Compiled consumer.array consumer.size [[]] producer.code
  inputDifferent : producer.array ≠ consumer.array
  view : WindowView.View consumer.array consumer.size consumer.source
  receiver : AlternativeRouting.Blocks view.blocks producerCode.after
  consumerClosed : Closed consumer.array receiver.code

def compile (producer consumer : Stage) : Option (Plan producer consumer) := do
  if different : producer.array ≠ consumer.array then
    let sender ← AlternativeProducerBlocks.compile consumer.array consumer.size [[]] producer.code
    let view ← consumer.window
    let receiver ← AlternativeRouting.compile view.blocks sender.after
    let closed ← checkBlocks consumer.array receiver.code
    return ⟨sender,different,view,receiver,closed⟩
  else none

def Plan.eval (p : Plan producer consumer) (x y : Int) (s : State) : Option State := do
  let initial := erase consumer.array s
  let inputQueue ← producer.queue initial
  let (middle,_,outputQueue) ← StreamProducerBlocks.eval (arrayInput (initial.arrays producer.array)) x y
    p.producerCode.code [] initial inputQueue []
  -- The consumer receives the produced values directly. There is no output
  -- array write, snapshot, or emit-from-memory operation at this boundary.
  (WindowTransport.eval (fun _ => none) x y p.receiver.code [] (erase consumer.array middle) outputQueue).map Prod.fst

theorem Plan.consume_correct (p : Plan producer consumer)
    (member : keys ∈ p.producerCode.after)
    (h : Related consumer.array consumer.size keys s t q) :
    (WindowTransport.eval (fun _ => none) x y p.receiver.code [] (erase consumer.array t) q).map Prod.fst =
      (consumer.source x y s).map (erase consumer.array) := by
  have same := (p.receiver.eval_correct member h.values [] s x y).trans (p.view.correct s h.sized x y)
  rw [← StreamConsumer.Agree.erase_eq h.agree]
  rw [← p.consumerClosed.correct (input:=arrayInput (s.arrays consumer.array)) (other:=fun _ => none)]
  simpa only [Option.map_map,Function.comp_def] using congrArg (Option.map (erase consumer.array)) same

theorem Plan.correct (p : Plan producer consumer) (s : State)
    (ready : producer.Ready s) (sized : (s.arrays consumer.array).size = consumer.size) (x y : Int) :
    p.eval x y s = ((do consumer.source x y (← producer.source x y s))).map (erase consumer.array) := by
  obtain ⟨qi,hq,hc⟩ := producer.queue_ready s ready
  have ha : (erase consumer.array s).arrays producer.array = s.arrays producer.array := by simp [erase,p.inputDifferent]
  have he : producer.queue (erase consumer.array s) = some qi := by simpa [Stage.queue,ha] using hq
  simp only [Plan.eval,he,ha,bind,Option.bind]
  have relation : Related consumer.array consumer.size [] s (erase consumer.array s) [] := ⟨erase_agree s,sized,.nil⟩
  have hp := p.producerCode.correct [] (by simp) (arrayInput (s.arrays producer.array)) x y [] s (erase consumer.array s) qi [] relation
  have sourceEq := producer.correct s ready.1 x y qi hc
  cases hs : WindowTransport.eval (arrayInput (s.arrays producer.array)) x y producer.code [] s qi <;>
    cases ht : StreamProducerBlocks.eval (arrayInput (s.arrays producer.array)) x y p.producerCode.code [] (erase consumer.array s) qi [] <;>
    simp only [hs,ht] at hp
  · simp only [hs,Option.map_none] at sourceEq
    simp [← sourceEq]
  · cases hp
  · cases hp
  · rename_i original transformed
    obtain ⟨u,remaining⟩ := original
    obtain ⟨v,rest,qo⟩ := transformed
    cases hp with
    | some member hr =>
      simp only [hs,Option.map_some] at sourceEq
      simp only [← sourceEq,bind,Option.bind]
      exact p.consume_correct member hr

theorem Plan.observe_correct (p : Plan producer consumer) (s : State)
    (ready : producer.Ready s) (sized : (s.arrays consumer.array).size = consumer.size) (x y : Int)
    (observe : State → α) (unobserved : ∀ t, observe (erase consumer.array t) = observe t) :
    (p.eval x y s).map observe = (do consumer.source x y (← producer.source x y s)).map observe := by
  rw [p.correct s ready sized x y,Option.map_map]
  simp only [Function.comp_def,unobserved]

end IRComparison.AlternativeStageFusion
