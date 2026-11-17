import IRComparison.Circuit.SharedPipelineRelation

namespace IRComparison.Circuit.Shared
open BuilderRelated

structure InstructionRelated (a : Circuit.InstructionLayout) (b : InstructionLayout) : Prop where
  frozen : a.frozen = b.frozen
  inputQueue : a.inputQueue = b.inputQueue
  outputQueue : a.outputQueue = b.outputQueue
  body : a.body.Simulates b.body

theorem chooseInput_related (channels : Nat → Nat) (mode : GlobalPipeline.InputMode) :
    BuilderRelated Eq (chooseInputQueue channels mode) (chooseInputQueue channels mode) := by
  cases mode with
  | channel => exact pure rfl
  | memory => exact BuilderRelated.queue _

theorem chooseOutput_related (channels : Nat → Nat) (budget : Nat) (output : Option Nat) :
    BuilderRelated Eq (chooseOutputQueue channels budget output) (chooseOutputQueue channels budget output) := by
  cases output with
  | none => exact BuilderRelated.queue _
  | some => exact pure rfl

theorem prepareInstruction_related (sizes channels : Nat → Nat) (c : HybridIR.Instruction) :
    BuilderRelated InstructionRelated (Circuit.prepareInstruction sizes channels c) (prepareInstruction sizes channels c) := by
  apply equalBind (BuilderRelated.snapshot _ _)
  intro input
  apply equalBind (chooseInput_related _ _)
  intro qi
  apply equalBind (chooseOutput_related _ _ _)
  intro qo
  apply BuilderRelated.bind (blocks_related _ _ _ _ _)
  intro a b h
  exact pure ⟨rfl,rfl,rfl,h⟩

theorem InstructionRelated.schedule (h : InstructionRelated a b) (c : HybridIR.Instruction) :
    (a.schedule c).Simulates (b.schedule c) := by
  simp only [Circuit.InstructionLayout.schedule,InstructionLayout.schedule,h.frozen,h.inputQueue,h.outputQueue]
  cases c.mode with
  | channel =>
    cases c.output <;>
      repeat' first | exact h.body | exact small_simulates _ | apply Schedule.Simulates.seq
  | memory array order fifo =>
    cases fifo <;> cases c.output <;>
      simp only [Bool.false_eq_true,↓reduceIte] <;>
      repeat' first | exact h.body | exact small_simulates _ | apply Schedule.Simulates.seq

theorem instruction_related (sizes channels : Nat → Nat) (c : HybridIR.Instruction) :
    BuilderRelated Schedule.Simulates (Circuit.instruction sizes channels c) (instruction sizes channels c) :=
  BuilderRelated.bind (prepareInstruction_related sizes channels c) (fun _ _ h => pure (h.schedule c))

theorem instructions_related (sizes channels : Nat → Nat) (cs : List HybridIR.Instruction) :
    BuilderRelated Schedule.Simulates (Circuit.instructions sizes channels cs) (instructions sizes channels cs) := by
  induction cs with
  | nil => exact pure .skip
  | cons c cs ih =>
    exact BuilderRelated.bind (instruction_related _ _ _) (fun _ _ h =>
      BuilderRelated.bind ih (fun _ _ ht => pure (h.seq ht)))

theorem tailCode_related (sizes : Nat → Nat) (incoming : Nat) (c : HybridCompactChainControl.Code) :
    BuilderRelated Schedule.Simulates (Circuit.tailCode sizes incoming c) (tailCode sizes incoming c) := by
  induction c generalizing incoming with
  | finish r =>
    apply equalBind (BuilderRelated.queue _)
    intro qo
    apply BuilderRelated.bind (counted_related _ _ _ _ _ _ _ _ _)
    intro a b h
    exact pure ((small_simulates (.step (.clear qo))).seq h)
  | stage a code rest ih =>
    apply equalBind (BuilderRelated.queue _)
    intro qo
    apply BuilderRelated.bind (counted_related _ _ _ _ _ _ _ _ _)
    intro first second h
    apply BuilderRelated.bind (ih qo)
    intro tail rest htail
    apply BuilderRelated.pure
    repeat' first | exact h | exact htail | exact small_simulates _ | apply Schedule.Simulates.seq

theorem rootCode_related (sizes : Nat → Nat) (c : HybridCompactChainControl.RootCode) :
    BuilderRelated Schedule.Simulates (Circuit.rootCode sizes c) (rootCode sizes c) := by
  apply equalBind (BuilderRelated.queue _)
  intro qo
  apply equalBind (BuilderRelated.queue _)
  intro qi
  apply equalBind (BuilderRelated.snapshot _ _)
  intro input
  apply BuilderRelated.bind (counted_related _ _ _ _ _ _ _ _ _)
  intro first second h
  apply BuilderRelated.bind (tailCode_related _ _ _)
  intro tail rest htail
  apply BuilderRelated.pure
  repeat' first | exact h | exact htail | exact small_simulates _ | apply Schedule.Simulates.seq

theorem regionCode_related (sizes : Nat → Nat) (c : HybridRegions.Region) :
    BuilderRelated Schedule.Simulates (Circuit.regionCode sizes c) (regionCode sizes c) := by
  apply equalBind (BuilderRelated.queue _)
  intro qi
  apply equalBind (BuilderRelated.queue _)
  intro qo
  apply equalBind (BuilderRelated.snapshot _ _)
  intro input
  apply BuilderRelated.bind (counted_related _ _ _ _ _ _ _ _ _)
  intro a b h
  apply BuilderRelated.pure
  repeat' first | exact h | exact small_simulates _ | apply Schedule.Simulates.seq

theorem regionsCode_related (sizes : Nat → Nat) (cs : List HybridRegions.Region) :
    BuilderRelated Schedule.Simulates (Circuit.regionsCode sizes cs) (regionsCode sizes cs) := by
  induction cs with
  | nil => exact pure .skip
  | cons c cs ih => exact BuilderRelated.bind (regionCode_related _ _) (fun _ _ h =>
      BuilderRelated.bind ih (fun _ _ ht => pure (h.seq ht)))

open HybridSymbolicGlobal (Instruction)

def CountedRelatedBuilder (old : Circuit.CountedBuilder) (shared : CountedBuilder) : Prop :=
  ∀ start stride count initial refill body input qi qo,
    BuilderRelated Schedule.Simulates (old start stride count initial refill body input qi qo)
      (shared start stride count initial refill body input qi qo)

theorem prepareSymbolic_related (counted : CountedRelatedBuilder old shared) (sizes channels : Nat → Nat) (c : Instruction) :
    BuilderRelated InstructionRelated (Circuit.prepareSymbolicWith old sizes channels c)
      (prepareSymbolicWith shared sizes channels c) := by
  apply equalBind (BuilderRelated.snapshot _ _)
  intro input
  apply equalBind (chooseInput_related _ _)
  intro qi
  apply equalBind (chooseOutput_related _ _ _)
  intro qo
  apply BuilderRelated.bind (counted _ _ _ _ _ _ _ _ _)
  intro a b h
  exact pure ⟨rfl,rfl,rfl,h⟩

theorem InstructionRelated.symbolic (h : InstructionRelated a b) (c : Instruction) :
    (Circuit.symbolicSchedule a c).Simulates (symbolicSchedule b c) := by
  simp only [Circuit.symbolicSchedule,symbolicSchedule,h.frozen,h.inputQueue,h.outputQueue]
  cases symbolicMode c <;> cases symbolicOutput c <;>
    repeat' first | exact h.body | exact small_simulates _ | apply Schedule.Simulates.seq

theorem symbolicInstruction_related (counted : CountedRelatedBuilder old shared) (sizes channels : Nat → Nat) (c : Instruction) :
    BuilderRelated Schedule.Simulates (Circuit.symbolicInstructionWith old sizes channels c)
      (symbolicInstructionWith shared sizes channels c) :=
  BuilderRelated.bind (prepareSymbolic_related counted sizes channels c) (fun _ _ h => pure (h.symbolic c))

theorem symbolicInstructions_related (counted : CountedRelatedBuilder old shared) (sizes channels : Nat → Nat) (cs : List Instruction) :
    BuilderRelated Schedule.Simulates (Circuit.symbolicInstructionsWith old sizes channels cs)
      (symbolicInstructionsWith shared sizes channels cs) := by
  induction cs with
  | nil => exact pure .skip
  | cons c cs ih => exact BuilderRelated.bind (symbolicInstruction_related counted sizes channels c) (fun _ _ h =>
      BuilderRelated.bind ih (fun _ _ ht => pure (h.seq ht)))

theorem allocateChannels_related (capacity : Nat → Nat) (ids : List Nat) :
    BuilderRelated Eq (allocateChannels capacity ids) (allocateChannels capacity ids) := by
  induction ids with
  | nil => exact pure rfl
  | cons a ids ih => exact equalBind (BuilderRelated.queue _) (fun q => equalBind ih (fun rest => pure rfl))

theorem symbolicProgram_related (counted : CountedRelatedBuilder old shared) (sizes : Nat → Nat) (cs : List Instruction) :
    BuilderRelated Schedule.Simulates (Circuit.symbolicProgramWith old sizes cs)
      (symbolicProgramWith shared sizes cs) :=
  equalBind (allocateChannels_related _ _) (fun channels => symbolicInstructions_related counted sizes _ cs)

theorem schedule_related (counted : CountedRelatedBuilder old shared) (layout : Array (Nat × Nat))
    (code : HybridUnifiedPipeline.Code) :
    (Circuit.scheduleWith old layout code).schedule.Simulates (scheduleWith shared layout code).schedule ∧
      BuildRelated (Circuit.scheduleWith old layout code).build (scheduleWith shared layout code).build := by
  cases code with
  | expanded cs =>
    exact (equalBind (allocateChannels_related _ _) (fun channels => instructions_related _ _ cs)) _ _ (.refl _)
  | symbolic cs => exact symbolicProgram_related counted _ cs _ _ (.refl _)
  | compact c =>
    let sizes := fun a => ((layout.toList.find? (fun p => p.1 == a)).map Prod.snd).getD 0
    let initial : Build := { memories := layout, nextArray := layout.foldl (fun n p => max n (p.1+1)) 0 }
    exact rootCode_related sizes c initial initial (.refl initial)
  | regions cs => exact regionsCode_related _ cs _ _ (.refl _)

theorem pipeline_related (layout : Array (Nat × Nat)) (code : HybridUnifiedPipeline.Code) :
    (Circuit.scheduleWith CountedBackend.named.build layout code).schedule.Simulates (pipeline layout code).schedule ∧
      BuildRelated (Circuit.scheduleWith CountedBackend.named.build layout code).build (pipeline layout code).build :=
  schedule_related namedCounted_related layout code

end IRComparison.Circuit.Shared
