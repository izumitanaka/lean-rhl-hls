import IRComparison.Circuit.InstructionAllocation

namespace IRComparison.Circuit

theorem chooseInput_queues (mapping : Nat → Nat) (mode : GlobalPipeline.InputMode) :
    PreservesQueues (chooseInputQueue mapping mode) := by
  cases mode with
  | channel => exact queues_pure _
  | memory => exact queues_allocate _

theorem chooseOutput_queues (mapping : Nat → Nat) (budget : Nat) (output : Option Nat) :
    PreservesQueues (chooseOutputQueue mapping budget output) := by
  cases output with
  | some => exact queues_pure _
  | none => exact queues_allocate _

theorem prepareInstruction_extension (sizes : Nat → Nat) (mapping : Nat → Nat) (c : HybridIR.Instruction) :
    ExtendsBuild (prepareInstruction sizes mapping c) := by
  apply extends_bind _ _ (extends_snapshot _ _)
  intro input
  apply extends_bind _ _ (chooseInput_extension _ _)
  intro qi
  apply extends_bind _ _ (chooseOutput_extension _ _ _)
  intro qo
  exact extends_bind _ _ (extends_blocks _ _ _ _ _) (fun _ => extends_pure _)

theorem instruction_extension (sizes : Nat → Nat) (mapping : Nat → Nat) (c : HybridIR.Instruction) :
    ExtendsBuild (instruction sizes mapping c) :=
  extends_bind _ _ (prepareInstruction_extension _ _ _) (fun _ => extends_pure _)

theorem instruction_queues (sizes : Nat → Nat) (mapping : Nat → Nat) (c : HybridIR.Instruction) :
    PreservesQueues (instruction sizes mapping c) := by
  apply queues_bind _ _ ?_ (fun _ => queues_pure _)
  apply queues_bind _ _ (queues_snapshot _ _)
  intro input
  apply queues_bind _ _ (chooseInput_queues _ _)
  intro qi
  apply queues_bind _ _ (chooseOutput_queues _ _ _)
  intro qo
  exact queues_bind _ _ (queues_of_resources _ (blocks_resources _ _ _ _ _)) (fun _ => queues_pure _)

theorem instructions_extension (sizes : Nat → Nat) (mapping : Nat → Nat) (cs : List HybridIR.Instruction) :
    ExtendsBuild (instructions sizes mapping cs) := by
  induction cs with
  | nil => exact extends_pure _
  | cons c cs ih => exact extends_bind _ _ (instruction_extension _ _ _) (fun _ => extends_bind _ _ ih (fun _ => extends_pure _))

theorem instructions_queues (sizes : Nat → Nat) (mapping : Nat → Nat) (cs : List HybridIR.Instruction) :
    PreservesQueues (instructions sizes mapping cs) := by
  induction cs with
  | nil => exact queues_pure _
  | cons c cs ih => exact queues_bind _ _ (instruction_queues _ _ _) (fun _ => queues_bind _ _ ih (fun _ => queues_pure _))

theorem instruction_array (sizes : Nat → Nat) (mapping : Nat → Nat) (c : HybridIR.Instruction) (b : Build) :
    (instruction sizes mapping c b).2.nextArray = b.nextArray+1 := by
  let b0 := b.allocateSnapshot c.input sizes
  have hi := chooseInput_storage mapping c.mode b0
  change (let (qi,b1) := chooseInputQueue mapping c.mode b0;
    let (qo,b2) := chooseOutputQueue mapping ((blocksBudget c.blocks).getD 0) c.output b1;
    (blocks b.nextArray qi qo [] c.blocks b2).2).nextArray = _
  generalize ei : chooseInputQueue mapping c.mode b0 = pair at *
  obtain ⟨qi,b1⟩ := pair
  dsimp only at hi ⊢
  have ho := chooseOutput_storage mapping ((blocksBudget c.blocks).getD 0) c.output b1
  generalize eo : chooseOutputQueue mapping ((blocksBudget c.blocks).getD 0) c.output b1 = pair at *
  obtain ⟨qo,b2⟩ := pair
  dsimp only at ho ⊢
  have hb := blocks_resources b.nextArray qi qo [] c.blocks b2
  have ha := congrArg (fun r => r.2.2.1) hb
  dsimp only [Build.resources] at ha
  exact ha.trans (ho.2.trans hi.2)

theorem preload_frame (input qi : Nat) (indices : List Int) : (preload input qi indices).above base := by
  induction indices with
  | nil => trivial
  | cons i indices ih => exact ⟨True.intro,ih⟩

theorem InstructionLayout.above (a : InstructionLayout) (c : HybridIR.Instruction) (h : a.body.above base) :
    (a.schedule c).above base := by
  have initial : (inputSetup c.mode a.inputQueue).above base := by
    cases c.mode with
    | channel => trivial
    | memory array order fifo => cases fifo <;> exact ⟨True.intro,by first | trivial | exact preload_frame _ _ _⟩
  have erased : (match c.output with | some a => Schedule.step (.erase a) | none => .skip).above base := by cases c.output <;> trivial
  exact ⟨True.intro,initial,True.intro,erased,h,erased,True.intro⟩

theorem instruction_frame (sizes : Nat → Nat) (mapping : Nat → Nat) (c : HybridIR.Instruction) (b : Build) :
    (instruction sizes mapping c b).1.above b.wires.size := by
  let b0 := b.allocateSnapshot c.input sizes
  have hi := chooseInput_extension mapping c.mode b0
  change (let (qi,b1) := chooseInputQueue mapping c.mode b0;
    let (qo,b2) := chooseOutputQueue mapping ((blocksBudget c.blocks).getD 0) c.output b1;
    let (body,_) := blocks b.nextArray qi qo [] c.blocks b2;
    InstructionLayout.schedule ⟨b.nextArray,qi,qo,body⟩ c).above b.wires.size
  generalize ei : chooseInputQueue mapping c.mode b0 = pair at *
  obtain ⟨qi,b1⟩ := pair
  dsimp only at hi ⊢
  have ho := chooseOutput_extension mapping ((blocksBudget c.blocks).getD 0) c.output b1
  generalize eo : chooseOutputQueue mapping ((blocksBudget c.blocks).getD 0) c.output b1 = pair at *
  obtain ⟨qo,b2⟩ := pair
  dsimp only at ho ⊢
  have hb := blocks_frame b.nextArray qi qo [] c.blocks b2
  generalize eb : blocks b.nextArray qi qo [] c.blocks b2 = pair at *
  obtain ⟨body,b3⟩ := pair
  exact InstructionLayout.above _ _ (body.above_mono hb.2 (Nat.le_trans hi.wires ho.wires))

end IRComparison.Circuit
