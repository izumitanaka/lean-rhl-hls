import IRComparison.Memory.StreamProducerBlocks
import IRComparison.Memory.WindowPipeline

namespace IRComparison.StreamFusion
open StreamState StreamConsumer WindowPipeline

structure Plan (producer consumer : Stage) (array size : Nat) where
  producerCode : StreamProducerBlocks.Compiled array size [] producer.code
  inputDifferent : producer.array ≠ array
  consumerArray : consumer.array = array
  consumerSize : consumer.size = size
  consumerOrder : consumer.producer = producerCode.after
  consumerFIFO : consumer.fifo = true
  consumerClosed : Closed array consumer.code

/-- Failure preserves both original stages at the caller; no half-converted
    channel is returned. Both branches must have the same static output order
    in this first implementation. -/
def compile (producer consumer : Stage) (array size : Nat) : Option (Plan producer consumer array size) := do
  let pc ← StreamProducerBlocks.compile array size [] producer.code
  if hd : producer.array ≠ array then
    if ha : consumer.array = array then
      if hs : consumer.size = size then
        if ho : consumer.producer = pc.after then
          if hf : consumer.fifo = true then
            let closed ← checkBlocks array consumer.code
            return ⟨pc,hd,ha,hs,ho,hf,closed⟩
          else none
        else none
      else none
    else none
  else none

def Plan.eval (p : Plan producer consumer array size) (x y : Int) (s : State) : Option State := do
  let initial := erase array s
  let inputQueue ← producer.queue initial
  let (middle,_,outputQueue) ← StreamProducerBlocks.eval (arrayInput (initial.arrays producer.array)) x y
    p.producerCode.code [] initial inputQueue []
  -- The consumer receives the produced values directly. There is no output
  -- array write, snapshot, or emit-from-memory operation at this boundary.
  (WindowTransport.eval (fun _ => none) x y consumer.code [] (erase array middle) outputQueue).map Prod.fst

theorem Plan.consume_correct (p : Plan producer consumer array size)
    (h : Related array size p.producerCode.after s t q) :
    (WindowTransport.eval (fun _ => none) x y consumer.code [] (erase array t) q).map Prod.fst =
      (consumer.source x y s).map (erase array) := by
  have sized : (s.arrays consumer.array).size = consumer.size := by
    simpa only [p.consumerArray,p.consumerSize] using h.sized
  have correspondence : consumer.fifo = true → CommunicationIR.Corresponds
      (arrayInput (s.arrays consumer.array)) consumer.producer q := by
    intro _
    simpa only [p.consumerArray,p.consumerOrder] using h.values
  have same := consumer.correct s sized x y q correspondence
  rw [← StreamConsumer.Agree.erase_eq h.agree]
  rw [← p.consumerClosed.correct (input:=arrayInput (s.arrays consumer.array)) (other:=fun _ => none)]
  simpa only [Option.map_map,Function.comp_def] using congrArg (Option.map (erase array)) same

theorem Plan.correct (p : Plan producer consumer array size) (s : State)
    (ready : producer.Ready s) (sized : (s.arrays array).size = size) (x y : Int) :
    p.eval x y s = ((do consumer.source x y (← producer.source x y s))).map (erase array) := by
  obtain ⟨qi,hq,hc⟩ := producer.queue_ready s ready
  have ha : (erase array s).arrays producer.array = s.arrays producer.array := by simp [erase,p.inputDifferent]
  have he : producer.queue (erase array s) = some qi := by simpa [Stage.queue,ha] using hq
  simp only [Plan.eval,he,ha,bind,Option.bind]
  have relation : Related array size [] s (erase array s) [] := ⟨erase_agree s,sized,.nil⟩
  have hp := p.producerCode.correct (arrayInput (s.arrays producer.array)) x y [] s (erase array s) qi [] relation
  have sourceEq := producer.correct s ready.1 x y qi hc
  cases hs : WindowTransport.eval (arrayInput (s.arrays producer.array)) x y producer.code [] s qi <;>
    cases ht : StreamProducerBlocks.eval (arrayInput (s.arrays producer.array)) x y p.producerCode.code [] (erase array s) qi [] <;>
    simp only [hs,ht] at hp
  · simp only [hs,Option.map_none] at sourceEq
    simp [← sourceEq]
  · cases hp
  · cases hp
  · rename_i original transformed
    obtain ⟨u,remaining⟩ := original
    obtain ⟨v,rest,qo⟩ := transformed
    cases hp with
    | some hr =>
      simp only [hs,Option.map_some] at sourceEq
      simp only [← sourceEq,bind,Option.bind]
      exact p.consume_correct hr

/-- Public observations may be any function insensitive to the private array.
    This gives ordinary output equality, rather than requiring users to inspect
    or trust the internal state correspondence. -/
theorem Plan.observe_correct (p : Plan producer consumer array size) (s : State)
    (ready : producer.Ready s) (sized : (s.arrays array).size = size) (x y : Int)
    (observe : State → α) (unobserved : ∀ t, observe (erase array t) = observe t) :
    (p.eval x y s).map observe = (do consumer.source x y (← producer.source x y s)).map observe := by
  rw [p.correct s ready sized x y,Option.map_map]
  simp only [Function.comp_def,unobserved]

/-- `array` is private to the region: its value is excluded from observation
    on both paths. Selection does not establish whole-program liveness. -/
inductive Selected (producer consumer : Stage) (array size : Nat) where
  | memory
  | fifo (plan : Plan producer consumer array size)

def select (producer consumer : Stage) (array size : Nat) : Selected producer consumer array size :=
  match compile producer consumer array size with
  | none => .memory
  | some p => .fifo p

def Selected.isFIFO : Selected producer consumer array size → Bool
  | .memory => false
  | .fifo _ => true

def Selected.eval (p : Selected producer consumer array size) (x y : Int) (s : State) : Option State :=
  match p with
  | .memory => (WindowPipeline.eval x y [producer,consumer] s).map (erase array)
  | .fifo plan => plan.eval x y s

theorem Selected.correct (p : Selected producer consumer array size) (s : State)
    (ready : WindowPipeline.Ready x y [producer,consumer] s) (sized : (s.arrays array).size = size) :
    p.eval x y s = (WindowPipeline.source x y [producer,consumer] s).map (erase array) := by
  cases p with
  | memory => exact congrArg (Option.map (erase array)) (WindowPipeline.eval_correct _ s ready)
  | fifo plan =>
    simpa [WindowPipeline.source] using plan.correct s ready.1 sized x y

end IRComparison.StreamFusion
