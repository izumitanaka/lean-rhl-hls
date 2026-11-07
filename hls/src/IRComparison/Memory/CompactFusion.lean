import IRComparison.Memory.SymbolicProducerLoop
import IRComparison.Memory.CompactFIFO
import IRComparison.Memory.StreamConsumer

namespace IRComparison.CompactFusion
open StreamConsumer StreamState

theorem fifo_loop_erase (checked : Checked array code.body) (n k : Nat) (old : List Int) (s : State) (q : List Int) :
    (CompactFIFO.Code.loop code x y n k old s q).map (fun (t,qs) => (erase array t,qs)) =
      code.loop x y n k old (erase array s) q := by
  induction n generalizing k old s q with
  | zero => rfl
  | succ n ih =>
    rw [CompactFIFO.Code.loop,CompactFIFO.Code.loop,← checked.correct]
    cases hb : code.body.eval (SymbolicWindowLoop.index code.start code.stride k) x y s old with
    | none => rfl
    | some t =>
      cases n with
      | zero => rfl
      | succ m =>
        simp only [Option.map_some,bind,Option.bind]
        cases hl : WindowFIFO.execute (fun _ => none) old
            (CompactRouting.instantiate (SymbolicWindowLoop.index code.start code.stride (k+1)) code.refill) q with
        | none => rfl
        | some pair => obtain ⟨vs,qs⟩ := pair; exact ih (k+1) vs t qs

theorem fifo_erase (checked : Checked array code.body) (s : State) (q : List Int) :
    (CompactFIFO.Code.eval code x y s q).map (fun (t,qs) => (erase array t,qs)) =
      code.eval x y (erase array s) q := by
  cases hc : code.count with
  | zero => simp [CompactFIFO.Code.eval,hc]
  | succ n =>
    simp only [CompactFIFO.Code.eval,hc]
    cases WindowFIFO.execute (fun _ => none) [] (CompactRouting.instantiate code.start code.initial) q with
    | none => rfl
    | some pair => obtain ⟨vs,qs⟩ := pair; exact fifo_loop_erase checked (n+1) 0 vs s qs

structure Receiver (source : SymbolicWindowLoop.Code) (supplier : CompactSequence.Seq) where
  code : CompactFIFO.Code
  body : code.body = source.body
  correct : ∀ input x y s q, CommunicationIR.Corresponds input supplier.entries q →
    (code.eval x y s q).map Prod.fst = source.eval input x y s

def receiver (p : CompactFIFO.Plan source supplier) : Receiver source supplier :=
  ⟨p.code,rfl,fun input x y s q h => p.correct s q h⟩

def candidateReceiver (candidate : CompactSequence.Certified supplier)
    (p : CompactFIFO.Plan source candidate.sequence) : Receiver source supplier :=
  ⟨p.code,rfl,by intro input x y s q h; apply p.correct s q; simpa only [candidate.correct] using h⟩

structure Plan (inputArray output size : Nat) (producer consumer : SymbolicWindowLoop.Code) where
  sender : SymbolicProducerLoop.Plan output size producer
  receiver : Receiver consumer sender.sequence
  different : inputArray ≠ output
  closed : Checked output consumer.body

def compile (inputArray output size : Nat) (producer consumer : SymbolicWindowLoop.Code) :
    Option (Plan inputArray output size producer consumer) := do
  if different : inputArray ≠ output then
    let sender ← SymbolicProducerLoop.compile output size producer
    let receiver ← CompactFIFO.compile consumer sender.sequence
    let closed ← check output consumer.body
    return ⟨sender,CompactFusion.receiver receiver,different,closed⟩
  else none

def source (inputArray output : Nat) (producer consumer : SymbolicWindowLoop.Code) (x y : Int) (s : State) : Option State := do
  let t ← producer.eval (arrayInput (s.arrays inputArray)) x y s
  consumer.eval (arrayInput (t.arrays output)) x y t

def Plan.eval (p : Plan inputArray output size producer consumer) (x y : Int) (s : State) : Option State := do
  let initial := erase output s
  let (t,q) ← p.sender.code.eval (arrayInput (initial.arrays inputArray)) x y initial
  (p.receiver.code.eval x y (erase output t) q).map Prod.fst

theorem Plan.consume_correct (p : Plan inputArray output size producer consumer)
    (h : Related output size p.sender.sequence.entries s t q) :
    (p.receiver.code.eval x y (erase output t) q).map Prod.fst =
      (consumer.eval (arrayInput (s.arrays output)) x y s).map (erase output) := by
  have same := p.receiver.correct (arrayInput (s.arrays output)) x y s q h.values
  rw [← StreamConsumer.Agree.erase_eq h.agree,← fifo_erase (p.receiver.body.symm ▸ p.closed)]
  simpa only [Option.map_map,Function.comp_def] using congrArg (Option.map (erase output)) same

theorem Plan.correct (p : Plan inputArray output size producer consumer) (s : State)
    (sized : (s.arrays output).size = size) (x y : Int) :
    p.eval x y s = (source inputArray output producer consumer x y s).map (erase output) := by
  have relation : Related output size [] s (erase output s) [] := ⟨erase_agree s,sized,.nil⟩
  have hp := p.sender.correct (input:=arrayInput (s.arrays inputArray)) (x:=x) (y:=y) s (erase output s) relation
  simp only [Plan.eval,source,erase,p.different,↓reduceIte]
  change (do
    let (t,q) ← p.sender.code.eval (arrayInput (s.arrays inputArray)) x y (erase output s)
    (p.receiver.code.eval x y (erase output t) q).map Prod.fst) = _
  cases hs : producer.eval (arrayInput (s.arrays inputArray)) x y s <;>
    cases ht : p.sender.code.eval (arrayInput (s.arrays inputArray)) x y (erase output s) <;>
    simp only [hs,ht] at hp
  · rfl
  · cases hp
  · cases hp
  · rename_i u pair
    obtain ⟨t,q⟩ := pair
    cases hp with
    | some h => exact p.consume_correct h

/-- The supplier comes from the compiled producer, not user-supplied queue
    contents. The wire-checked SAT candidate is used to compile the consumer. -/
def compileWithSMT (inputArray output size : Nat) (producer consumer : SymbolicWindowLoop.Code)
    (directory : System.FilePath) : IO (Option (Plan inputArray output size producer consumer)) := do
  if different : inputArray ≠ output then
    let some sender := SymbolicProducerLoop.compile output size producer | return none
    let (_,certificate) ← CompactSequence.solve sender.sequence directory
    let some certificate := certificate | return none
    let some routed := CompactFIFO.compile consumer certificate.sequence | return none
    let some closed := check output consumer.body | return none
    return some ⟨sender,candidateReceiver certificate routed,different,closed⟩
  else return none

inductive Selected (inputArray output size : Nat) (producer consumer : SymbolicWindowLoop.Code) where
  | memory
  | fifo (plan : Plan inputArray output size producer consumer)

def select (inputArray output size : Nat) (producer consumer : SymbolicWindowLoop.Code) : Selected inputArray output size producer consumer :=
  match compile inputArray output size producer consumer with
  | none => .memory
  | some p => .fifo p

def Selected.eval (p : Selected inputArray output size producer consumer) (x y : Int) (s : State) : Option State :=
  match p with
  | .memory => source inputArray output producer consumer x y s
  | .fifo plan => plan.eval x y s

theorem Selected.correct (p : Selected inputArray output size producer consumer) (s : State)
    (sized : (s.arrays output).size = size) (x y : Int) (observe : State → α)
    (unobserved : ∀ s, observe (erase output s) = observe s) :
    (p.eval x y s).map observe = (source inputArray output producer consumer x y s).map observe := by
  cases p with
  | memory => rfl
  | fifo plan =>
    rw [Selected.eval,plan.correct s sized x y,Option.map_map]
    simp only [Function.comp_def,unobserved]

def selectWithSMT (inputArray output size : Nat) (producer consumer : SymbolicWindowLoop.Code)
    (directory : System.FilePath) : IO (Selected inputArray output size producer consumer) := do
  match ← compileWithSMT inputArray output size producer consumer directory with
  | none => return .memory
  | some p => return .fifo p

end IRComparison.CompactFusion
