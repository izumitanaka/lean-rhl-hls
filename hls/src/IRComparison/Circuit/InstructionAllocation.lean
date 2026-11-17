import IRComparison.Circuit.QueueChoice
import IRComparison.Circuit.InstructionSound

namespace IRComparison.Circuit

theorem OutputQueueMatches.lower (h : OutputQueueMatches ids mapping n output qo) (hn : m ≤ n) :
    OutputQueueMatches ids mapping m output qo := by
  cases output with
  | none => exact Nat.le_trans hn h
  | some => exact h

/-- Construct the instruction contract directly from the allocator and the
proved block compiler. New FIFO and snapshot IDs are disjoint from every
previously allocated channel. -/
theorem prepareInstruction_contract (sizes : Nat → Nat) (mapping : Nat → Nat) (c : HybridIR.Instruction)
    (b : Build) (inputs : 2 ≤ b.wires.size) (floor : limit ≤ b.nextArray)
    (channels : ChannelMap ids mapping b.nextQueue) (consistent : instructionChannels ids c)
    (outputMembers : ∀ a ∈ c.output.toList, a ∈ ids)
    (scopeOK : InstructionScoped limit c)
    (known : blocksBudget c.blocks = some budget)
    (capacity : ∀ a ∈ c.output.toList, budget ≤ cap (mapping a))
    (covered : CoversQueues cap (prepareInstruction sizes mapping c b).2) :
    InstructionContract ids mapping limit b.nextQueue cap (prepareInstruction sizes mapping c b).1 c := by
  let b0 := b.allocateSnapshot c.input sizes
  have inputExtend := chooseInput_extension mapping c.mode b0
  have inputMatches := chooseInput_matches (b:=b0) channels consistent
  have inputStorage := chooseInput_storage mapping c.mode b0
  change CoversQueues cap (let (qi,b1) := chooseInputQueue mapping c.mode b0;
    let (qo,b2) := chooseOutputQueue mapping ((blocksBudget c.blocks).getD 0) c.output b1;
    (blocks b.nextArray qi qo [] c.blocks b2).2) at covered
  change InstructionContract ids mapping limit b.nextQueue cap
    (let (qi,b1) := chooseInputQueue mapping c.mode b0;
    let (qo,b2) := chooseOutputQueue mapping ((blocksBudget c.blocks).getD 0) c.output b1;
    let (body,_) := blocks b.nextArray qi qo [] c.blocks b2;
    ⟨b.nextArray,qi,qo,body⟩) c
  generalize hi : chooseInputQueue mapping c.mode b0 = pair at *
  obtain ⟨qi,b1⟩ := pair
  dsimp only at inputExtend inputMatches inputStorage covered ⊢
  have outputExtend := chooseOutput_extension mapping ((blocksBudget c.blocks).getD 0) c.output b1
  have outputMatches := chooseOutput_matches (mapping:=mapping) (b:=b1)
    (budget:=(blocksBudget c.blocks).getD 0) outputMembers
  have outputStorage := chooseOutput_storage mapping ((blocksBudget c.blocks).getD 0) c.output b1
  have distinct := choices_distinct (budget:=(blocksBudget c.blocks).getD 0) channels consistent inputMatches.1 inputMatches.2 outputMembers
  generalize ho : chooseOutputQueue mapping ((blocksBudget c.blocks).getD 0) c.output b1 = pair at *
  obtain ⟨qo,b2⟩ := pair
  dsimp only at outputExtend outputMatches outputStorage distinct covered ⊢
  have blockExtend := extends_blocks b.nextArray qi qo [] c.blocks b2
  have bounds := blocks_frame b.nextArray qi qo [] c.blocks b2
  generalize hc : blocks b.nextArray qi qo [] c.blocks b2 = pair at *
  obtain ⟨body,b3⟩ := pair
  dsimp only at blockExtend bounds covered ⊢
  have coveredBody := covered.before blockExtend
  have coveredInput := coveredBody.before outputExtend
  have inputCap : ∀ array order, c.mode = .memory array order true → order.length ≤ cap qi := by
    intro array order hm
    have hh := chooseInput_capacity (b:=b0) (mapping:=mapping) (cap:=cap) (mode:=c.mode)
      (by rw [hi]; exact coveredInput) hm
    simpa only [hi] using hh
  have outputCap : budget ≤ cap qo := by
    have hh := chooseOutput_capacity (b:=b1) (mapping:=mapping) (cap:=cap) (output:=c.output)
      (budget:=(blocksBudget c.blocks).getD 0) (by rw [ho]; exact coveredBody) (by simpa [known] using capacity)
    rw [ho] at hh
    simpa only [known,Option.getD_some] using hh
  have readonly : ∀ block ∈ c.blocks, b.nextArray ∉ commandWrites block.body := by
    intro block member write
    have := scopeOK.body block member _ (commandWrites_mem _ write)
    omega
  have bodyInputs : 2 ≤ b2.wires.size := Nat.le_trans inputs (Nat.le_trans inputExtend.wires outputExtend.wires)
  have bodyContract := BlocksContract.ofBlocks b.nextArray qi qo c.blocks b2 bodyInputs distinct readonly known outputCap
  rw [hc] at bodyContract
  refine ⟨floor,inputMatches.1,?_,distinct,inputCap,bodyContract⟩
  exact outputMatches.lower inputExtend.nextQueue

end IRComparison.Circuit
