import IRComparison.Circuit.InstructionFacts

namespace IRComparison.Circuit

structure BlocksContract (cap : Nat → Nat) (code : Schedule) (input qi qo : Nat) (bs : List HybridIR.Block) : Prop where
  frame : code.above 2
  correct : ∀ p x y, p.wires 0 = x → p.wires 1 = y → p.queues qo = [] →
    ∃ result, code.Eval cap p result ∧
      result.map (fun q => (q.data,q.queues)) =
        (HybridIR.blocksEval (arrayInput (p.data.arrays input)) x y bs [] p.data (p.queues qi) []).map
          (fun (t,rest,out) => (t,GlobalPipeline.put (GlobalPipeline.put p.queues qi rest) qo out))

def BlocksContract.ofBlocks (input qi qo : Nat) (bs : List HybridIR.Block) (b : Build)
    (inputs : 2 ≤ b.wires.size) (distinct : qi ≠ qo)
    (readonly : ∀ block ∈ bs, input ∉ commandWrites block.body)
    (known : blocksBudget bs = some budget) (capacity : budget ≤ cap qo) :
    BlocksContract cap (blocks input qi qo [] bs b).1 input qi qo bs := by
  constructor
  · exact Schedule.above_mono _ (blocks_frame input qi qo [] bs b).2 inputs
  · intro p x y hx hy empty
    obtain ⟨r,hr,ho⟩ := blocks_full_correct input qi qo [] bs b p x y [] distinct inputs readonly
      (by simp) matches_nil hx hy known (by simpa [empty] using capacity)
    exact ⟨r,hr,by simpa only [empty] using ho⟩

structure InstructionContract (ids : List Nat) (mapping : Nat → Nat) (limit next : Nat)
    (cap : Nat → Nat) (a : InstructionLayout) (c : HybridIR.Instruction) : Prop where
  fresh : limit ≤ a.frozen
  inputMatch : InputQueueMatches ids mapping next c.mode a.inputQueue
  outputMatch : OutputQueueMatches ids mapping next c.output a.outputQueue
  distinct : a.inputQueue ≠ a.outputQueue
  preload : ∀ array order, c.mode = .memory array order true → order.length ≤ cap a.inputQueue
  body : BlocksContract cap a.body a.frozen a.inputQueue a.outputQueue c.blocks

def eraseData (output : Option Nat) (s : State) : State :=
  match output with | none => s | some a => StreamConsumer.erase a s

theorem eraseOutput_data (p : Payload) (output : Option Nat) :
    (p.eraseOutput output).data = eraseData output p.data := by cases output <;> rfl

theorem eraseOutput_wires (p : Payload) (output : Option Nat) :
    (p.eraseOutput output).wires = p.wires := by cases output <;> rfl

theorem eraseOutput_queues (p : Payload) (output : Option Nat) :
    (p.eraseOutput output).queues = p.queues := by cases output <;> rfl

theorem eraseData_trim (output : Option Nat) (s : State) :
    trimState limit (eraseData output s) = eraseData output (trimState limit s) := by
  cases output with
  | none => rfl
  | some => exact trim_erase

theorem eraseOutput_snapshot (p : Payload) (output : Option Nat)
    (separate : ∀ a ∈ output.toList, a ≠ frozen) :
    (p.eraseOutput output).data.arrays frozen = p.data.arrays frozen := by
  cases output with
  | none => rfl
  | some a =>
    have ha := separate a (by simp)
    simp [Payload.eraseOutput,Payload.erase,StreamConsumer.erase,Ne.symm ha]

theorem queues_after_instruction (physical : GlobalPipeline.Queues) (distinct : qi ≠ qo) :
    GlobalPipeline.put (GlobalPipeline.put (GlobalPipeline.put
      (GlobalPipeline.put (GlobalPipeline.put physical qi inputValues) qo []) qi remaining) qo outputValues) qi [] =
      GlobalPipeline.put (GlobalPipeline.put physical qi []) qo outputValues := by
  funext n
  by_cases hi : n = qi
  · subst n; simp [GlobalPipeline.put,distinct]
  · by_cases ho : n = qo
    · subst n; simp [GlobalPipeline.put,hi]
    · simp [GlobalPipeline.put,hi,ho]

def instructionView (ids : List Nat) (mapping : Nat → Nat) (limit : Nat) (p : Payload) :=
  (trimState limit p.data,channelView ids mapping p.queues)

end IRComparison.Circuit
