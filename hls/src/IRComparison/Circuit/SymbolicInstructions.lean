import IRComparison.Circuit.SymbolicAllocation

namespace IRComparison.Circuit
open HybridSymbolicGlobal (Instruction)

theorem symbolicSchedule_eq (a : InstructionLayout) (c : Instruction) :
    symbolicSchedule a c = a.schedule (symbolicReference c) := by cases c <;> rfl

theorem symbolicInstruction_extension_with (backend : CountedBackend) (sizes mapping : Nat → Nat) (c : Instruction) :
    ExtendsBuild (symbolicInstructionWith backend.build sizes mapping c) := by
  apply extends_bind _ _ ?_ (fun _ => extends_pure _)
  apply extends_bind _ _ (extends_snapshot _ _)
  intro input
  apply extends_bind _ _ (chooseInput_extension _ _)
  intro qi
  apply extends_bind _ _ (chooseOutput_extension _ _ _)
  intro qo
  exact extends_bind _ _ (backend.extension _ _ _ _ _ _ _ _ _) (fun _ => extends_pure _)

theorem symbolicInstructions_extension_with (backend : CountedBackend) (sizes mapping : Nat → Nat) (cs : List Instruction) :
    ExtendsBuild (symbolicInstructionsWith backend.build sizes mapping cs) := by
  induction cs with
  | nil => exact extends_pure _
  | cons c cs ih => exact extends_bind _ _ (symbolicInstruction_extension_with backend _ _ _) (fun _ => extends_bind _ _ ih (fun _ => extends_pure _))

theorem symbolicInstruction_queues_with (backend : CountedBackend) (sizes mapping : Nat → Nat) (c : Instruction) :
    PreservesQueues (symbolicInstructionWith backend.build sizes mapping c) := by
  apply queues_bind _ _ ?_ (fun _ => queues_pure _)
  apply queues_bind _ _ (queues_snapshot _ _)
  intro input
  apply queues_bind _ _ (chooseInput_queues _ _)
  intro qi
  apply queues_bind _ _ (chooseOutput_queues _ _ _)
  intro qo
  exact queues_bind _ _ (queues_of_resources _ (backend.resources _ _ _ _ _ _ _ _ _)) (fun _ => queues_pure _)

theorem symbolicInstructions_queues_with (backend : CountedBackend) (sizes mapping : Nat → Nat) (cs : List Instruction) :
    PreservesQueues (symbolicInstructionsWith backend.build sizes mapping cs) := by
  induction cs with
  | nil => exact queues_pure _
  | cons c cs ih => exact queues_bind _ _ (symbolicInstruction_queues_with backend _ _ _) (fun _ => queues_bind _ _ ih (fun _ => queues_pure _))

theorem symbolicInstruction_array_with (backend : CountedBackend) (sizes mapping : Nat → Nat) (c : Instruction) (b : Build) :
    (symbolicInstructionWith backend.build sizes mapping c b).2.nextArray = b.nextArray+1 := by
  let b0 := b.allocateSnapshot (symbolicInput c) sizes
  have hi := chooseInput_storage mapping (symbolicMode c) b0
  change (let (qi,b1) := chooseInputQueue mapping (symbolicMode c) b0;
    let (qo,b2) := chooseOutputQueue mapping (symbolicBudget c) (symbolicOutput c) b1;
    (backend.build (symbolicBody c).start (symbolicBody c).stride (symbolicBody c).count
      (symbolicInitial c) (symbolicRefill c) (symbolicBody c).body b.nextArray qi qo b2).2).nextArray = _
  generalize ei : chooseInputQueue mapping (symbolicMode c) b0 = pair at *
  obtain ⟨qi,b1⟩ := pair
  dsimp only at hi ⊢
  have ho := chooseOutput_storage mapping (symbolicBudget c) (symbolicOutput c) b1
  generalize eo : chooseOutputQueue mapping (symbolicBudget c) (symbolicOutput c) b1 = pair at *
  obtain ⟨qo,b2⟩ := pair
  dsimp only at ho ⊢
  have hb := backend.resources (symbolicBody c).start (symbolicBody c).stride (symbolicBody c).count
    (symbolicInitial c) (symbolicRefill c) (symbolicBody c).body b.nextArray qi qo b2
  have ha := congrArg (fun r => r.2.2.1) hb
  dsimp only [Build.resources] at ha
  exact ha.trans (ho.2.trans hi.2)

theorem symbolicInstruction_frame_with (backend : CountedBackend) (sizes mapping : Nat → Nat) (c : Instruction) (b : Build)
    (inputs : 2 ≤ b.wires.size) :
    (symbolicInstructionWith backend.build sizes mapping c b).1.above b.wires.size := by
  let b0 := b.allocateSnapshot (symbolicInput c) sizes
  have hi := chooseInput_extension mapping (symbolicMode c) b0
  change (let (qi,b1) := chooseInputQueue mapping (symbolicMode c) b0;
    let (qo,b2) := chooseOutputQueue mapping (symbolicBudget c) (symbolicOutput c) b1;
    let (body,_) := backend.build (symbolicBody c).start (symbolicBody c).stride (symbolicBody c).count
      (symbolicInitial c) (symbolicRefill c) (symbolicBody c).body b.nextArray qi qo b2;
    symbolicSchedule ⟨b.nextArray,qi,qo,body⟩ c).above b.wires.size
  generalize ei : chooseInputQueue mapping (symbolicMode c) b0 = pair at *
  obtain ⟨qi,b1⟩ := pair
  dsimp only at hi ⊢
  have ho := chooseOutput_extension mapping (symbolicBudget c) (symbolicOutput c) b1
  generalize eo : chooseOutputQueue mapping (symbolicBudget c) (symbolicOutput c) b1 = pair at *
  obtain ⟨qo,b2⟩ := pair
  dsimp only at ho ⊢
  have growth : b.wires.size ≤ b2.wires.size := Nat.le_trans hi.wires ho.wires
  have hf := backend.frame (symbolicBody c).start (symbolicBody c).stride (symbolicBody c).count
    (symbolicInitial c) (symbolicRefill c) (symbolicBody c).body b.nextArray qi qo b2 (Nat.le_trans inputs growth)
  generalize ec : backend.build (symbolicBody c).start (symbolicBody c).stride (symbolicBody c).count
    (symbolicInitial c) (symbolicRefill c) (symbolicBody c).body b.nextArray qi qo b2 = pair at *
  obtain ⟨body,b3⟩ := pair
  dsimp only at hf ⊢
  rw [symbolicSchedule_eq]
  exact InstructionLayout.above _ _ (Schedule.above_mono _ hf growth)

theorem symbolic_reference_scope (c : Instruction)
    (input : symbolicInput c < limit)
    (body : ∀ a ∈ allCommandArrays (symbolicBody c).body, a < limit) :
    InstructionScoped limit (symbolicReference c) := by
  refine ⟨input,?_,?_⟩
  · cases c <;> exact input
  · intro block hb a ha
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hb
    exact body a ha

structure SymbolicScoped (ids : List Nat) (limit : Nat) (cs : List Instruction) : Prop where
  consistent : ∀ c ∈ cs, instructionChannels ids (symbolicReference c)
  member : ∀ c ∈ cs, ∀ a ∈ (symbolicOutput c).toList, a ∈ ids
  input : ∀ c ∈ cs, symbolicInput c < limit
  body : ∀ c ∈ cs, ∀ a ∈ allCommandArrays (symbolicBody c).body, a < limit
  outputs : ∀ c ∈ cs, ∀ a ∈ (symbolicOutput c).toList, a < limit

def SymbolicCapacity (mapping cap : Nat → Nat) (cs : List Instruction) : Prop :=
  ∀ c ∈ cs, ∃ bound, sendBound (symbolicBody c).body = some bound ∧
    ∀ a ∈ (symbolicOutput c).toList, symbolicBudget c ≤ cap (mapping a)

theorem symbolicInstructions_correct_with (backend : CountedBackend) (sizes mapping : Nat → Nat) (cs : List Instruction)
    (b : Build) (inputs : 2 ≤ b.wires.size) (floor : limit ≤ b.nextArray)
    (channels : ChannelMap ids mapping b.nextQueue)
    (scopeOK : SymbolicScoped ids limit cs) (capacity : SymbolicCapacity mapping cap cs)
    (covered : CoversQueues cap (symbolicInstructionsWith backend.build sizes mapping cs b).2)
    (p : Payload) (hx : p.wires 0 = x) (hy : p.wires 1 = y) :
    ∃ r, (symbolicInstructionsWith backend.build sizes mapping cs b).1.Eval cap p r ∧
      r.map (fun q => trimState limit q.data) =
        HybridSymbolicGlobal.execute x y cs (trimState limit p.data) (channelView ids mapping p.queues) := by
  induction cs generalizing b p with
  | nil => exact ⟨some p,.skip,rfl⟩
  | cons c cs ih =>
    let first := symbolicInstructionWith backend.build sizes mapping c b
    have extended := symbolicInstruction_extension_with backend sizes mapping c b
    have tailExtended := symbolicInstructions_extension_with backend sizes mapping cs first.2
    have firstCovered : CoversQueues cap first.2 := covered.before tailExtended
    obtain ⟨bound,known,outputCap⟩ := capacity c (by simp)
    have contract := prepareSymbolicWith_contract backend sizes mapping c b inputs floor channels
      (scopeOK.consistent c (by simp)) (scopeOK.member c (by simp))
      (scopeOK.body c (by simp)) known outputCap firstCovered
    obtain ⟨r,hr,ho⟩ := instruction_schedule_correct contract channels (scopeOK.consistent c (by simp))
      (symbolic_reference_scope c (scopeOK.input c (by simp)) (scopeOK.body c (by simp)))
      (scopeOK.outputs c (by simp)) p hx hy
    rw [symbolicReference_correct] at ho
    have tailScope : SymbolicScoped ids limit cs := ⟨
      fun d hd => scopeOK.consistent d (by simp [hd]),fun d hd => scopeOK.member d (by simp [hd]),
      fun d hd => scopeOK.input d (by simp [hd]),fun d hd => scopeOK.body d (by simp [hd]),
      fun d hd => scopeOK.outputs d (by simp [hd])⟩
    have tailCap : SymbolicCapacity mapping cap cs := fun d hd => capacity d (by simp [hd])
    have tailFloor : limit ≤ first.2.nextArray := by
      dsimp only [first]; rw [symbolicInstruction_array_with backend]; omega
    change ∃ result, (Schedule.seq first.1 (symbolicInstructionsWith backend.build sizes mapping cs first.2).1).Eval cap p result ∧ _
    rw [← symbolicSchedule_eq] at hr
    change first.1.Eval cap p r at hr
    cases r with
    | none =>
      refine ⟨none,.seq_error hr,?_⟩
      rw [HybridSymbolicGlobal.execute,← ho]; rfl
    | some q =>
      have stable := Schedule.preserves_below hr (symbolicInstruction_frame_with backend sizes mapping c b inputs) rfl
      have qx : q.wires 0 = x := (stable 0 (by omega)).symm.trans hx
      have qy : q.wires 1 = y := (stable 1 (by omega)).symm.trans hy
      obtain ⟨result,he,hs⟩ := ih first.2 (Nat.le_trans inputs extended.wires) tailFloor
        (channels.grow extended.nextQueue) tailScope tailCap covered q qx qy
      refine ⟨result,.seq hr he,?_⟩
      rw [HybridSymbolicGlobal.execute,← ho]
      exact hs

abbrev symbolicInstruction_extension := symbolicInstruction_extension_with CountedBackend.legacy
abbrev symbolicInstructions_extension := symbolicInstructions_extension_with CountedBackend.legacy
abbrev symbolicInstruction_queues := symbolicInstruction_queues_with CountedBackend.legacy
abbrev symbolicInstructions_queues := symbolicInstructions_queues_with CountedBackend.legacy
abbrev symbolicInstruction_array := symbolicInstruction_array_with CountedBackend.legacy
abbrev symbolicInstruction_frame := symbolicInstruction_frame_with CountedBackend.legacy
abbrev symbolicInstructions_correct {limit : Nat} {ids : List Nat} {cap : Nat → Nat} {x y : Int} :=
  symbolicInstructions_correct_with (limit:=limit) (ids:=ids) (cap:=cap) (x:=x) (y:=y) CountedBackend.legacy

end IRComparison.Circuit
