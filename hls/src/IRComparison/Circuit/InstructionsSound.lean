import IRComparison.Circuit.InstructionFrame

namespace IRComparison.Circuit

/-- Properties of the whole-array communication plan and of the source layout.
These are checked on the supplied code, independently of its execution. -/
structure InstructionsScoped (ids : List Nat) (limit : Nat) (cs : List HybridIR.Instruction) : Prop where
  consistent : ∀ c ∈ cs, instructionChannels ids c
  member : ∀ c ∈ cs, ∀ a ∈ c.output.toList, a ∈ ids
  arrays : ∀ c ∈ cs, InstructionScoped limit c
  outputs : ∀ c ∈ cs, ∀ a ∈ c.output.toList, a < limit

def InstructionsCapacity (mapping cap : Nat → Nat) (cs : List HybridIR.Instruction) : Prop :=
  ∀ c ∈ cs, ∃ budget, blocksBudget c.blocks = some budget ∧
    ∀ a ∈ c.output.toList, budget ≤ cap (mapping a)

theorem instructions_correct (sizes mapping : Nat → Nat) (cs : List HybridIR.Instruction)
    (b : Build) (inputs : 2 ≤ b.wires.size) (floor : limit ≤ b.nextArray)
    (channels : ChannelMap ids mapping b.nextQueue)
    (scopeOK : InstructionsScoped ids limit cs)
    (capacity : InstructionsCapacity mapping cap cs)
    (covered : CoversQueues cap (instructions sizes mapping cs b).2)
    (p : Payload) (hx : p.wires 0 = x) (hy : p.wires 1 = y) :
    ∃ r, (instructions sizes mapping cs b).1.Eval cap p r ∧
      r.map (fun q => trimState limit q.data) =
        HybridIR.execute x y cs (trimState limit p.data) (channelView ids mapping p.queues) := by
  induction cs generalizing b p with
  | nil => exact ⟨some p,.skip,rfl⟩
  | cons c cs ih =>
    let first := instruction sizes mapping c b
    have extended := instruction_extension sizes mapping c b
    have tailExtended := instructions_extension sizes mapping cs first.2
    have firstCovered : CoversQueues cap first.2 := covered.before tailExtended
    obtain ⟨budget,known,outputCap⟩ := capacity c (by simp)
    have contract := prepareInstruction_contract sizes mapping c b inputs floor channels
      (scopeOK.consistent c (by simp)) (scopeOK.member c (by simp))
      (scopeOK.arrays c (by simp)) known outputCap firstCovered
    obtain ⟨r,hr,ho⟩ := instruction_schedule_correct contract channels (scopeOK.consistent c (by simp))
      (scopeOK.arrays c (by simp)) (scopeOK.outputs c (by simp)) p hx hy
    have tailScope : InstructionsScoped ids limit cs := ⟨
      fun d hd => scopeOK.consistent d (by simp [hd]),
      fun d hd => scopeOK.member d (by simp [hd]),
      fun d hd => scopeOK.arrays d (by simp [hd]),
      fun d hd => scopeOK.outputs d (by simp [hd])⟩
    have tailCap : InstructionsCapacity mapping cap cs := fun d hd => capacity d (by simp [hd])
    have tailFloor : limit ≤ first.2.nextArray := by
      dsimp only [first]
      rw [instruction_array]
      omega
    change ∃ result, (Schedule.seq first.1 (instructions sizes mapping cs first.2).1).Eval cap p result ∧ _
    change first.1.Eval cap p r at hr
    cases r with
    | none =>
      refine ⟨none,.seq_error hr,?_⟩
      rw [HybridIR.execute,← ho]
      rfl
    | some q =>
      have stable := Schedule.preserves_below hr (instruction_frame sizes mapping c b) rfl
      have qx : q.wires 0 = x := (stable 0 (by omega)).symm.trans hx
      have qy : q.wires 1 = y := (stable 1 (by omega)).symm.trans hy
      obtain ⟨result,he,hs⟩ := ih first.2 (Nat.le_trans inputs extended.wires) tailFloor
        (channels.grow extended.nextQueue) tailScope tailCap covered q qx qy
      refine ⟨result,.seq hr he,?_⟩
      rw [HybridIR.execute,← ho]
      exact hs

end IRComparison.Circuit
