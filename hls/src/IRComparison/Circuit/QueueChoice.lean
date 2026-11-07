import IRComparison.Circuit.InstructionContract
import IRComparison.Circuit.RootSound

namespace IRComparison.Circuit

theorem chooseInput_extension (mapping : Nat → Nat) (mode : GlobalPipeline.InputMode) :
    ExtendsBuild (chooseInputQueue mapping mode) := by
  cases mode with
  | channel => exact extends_pure _
  | memory => exact extends_queue _

theorem chooseOutput_extension (mapping : Nat → Nat) (budget : Nat) (output : Option Nat) :
    ExtendsBuild (chooseOutputQueue mapping budget output) := by
  cases output with
  | some => exact extends_pure _
  | none => exact extends_queue _

theorem chooseInput_storage (mapping : Nat → Nat) (mode : GlobalPipeline.InputMode) (b : Build) :
    (chooseInputQueue mapping mode b).2.wires = b.wires ∧
      (chooseInputQueue mapping mode b).2.nextArray = b.nextArray := by
  cases mode <;> exact ⟨rfl,rfl⟩

theorem chooseOutput_storage (mapping : Nat → Nat) (budget : Nat) (output : Option Nat) (b : Build) :
    (chooseOutputQueue mapping budget output b).2.wires = b.wires ∧
      (chooseOutputQueue mapping budget output b).2.nextArray = b.nextArray := by
  cases output <;> exact ⟨rfl,rfl⟩

theorem chooseInput_matches (channels : ChannelMap ids mapping b.nextQueue)
    (consistent : instructionChannels ids c) :
    InputQueueMatches ids mapping b.nextQueue c.mode (chooseInputQueue mapping c.mode b).1 ∧
      (chooseInputQueue mapping c.mode b).1 < (chooseInputQueue mapping c.mode b).2.nextQueue := by
  cases hm : c.mode with
  | channel a =>
    simp only [hm,instructionChannels] at consistent
    exact ⟨⟨consistent.2.1,rfl⟩,channels.below a consistent.2.1⟩
  | memory a order fifo => exact ⟨Nat.le_refl _,Nat.lt_succ_self _⟩

theorem chooseOutput_matches (members : ∀ a ∈ output.toList, a ∈ ids) :
    OutputQueueMatches ids mapping b.nextQueue output (chooseOutputQueue mapping budget output b).1 := by
  cases output with
  | some a => exact ⟨members a (by simp),rfl⟩
  | none => exact Nat.le_refl _

theorem chooseInput_capacity (covered : CoversQueues cap (chooseInputQueue mapping mode b).2)
    (he : mode = .memory array order true) : order.length ≤ cap (chooseInputQueue mapping mode b).1 := by
  subst mode
  exact covered.allocated

theorem chooseOutput_capacity (covered : CoversQueues cap (chooseOutputQueue mapping budget output b).2)
    (known : ∀ a ∈ output.toList, budget ≤ cap (mapping a)) :
    budget ≤ cap (chooseOutputQueue mapping budget output b).1 := by
  cases output with
  | none => exact covered.allocated
  | some a => exact known a (by simp)

theorem choices_distinct (channels : ChannelMap ids mapping start)
    (consistent : instructionChannels ids c) (matched : InputQueueMatches ids mapping start c.mode qi)
    (inputBound : qi < b.nextQueue) (outputMembers : ∀ a ∈ c.output.toList, a ∈ ids) :
    qi ≠ (chooseOutputQueue mapping budget c.output b).1 := by
  cases ho : c.output with
  | none => exact Nat.ne_of_lt inputBound
  | some a =>
    have member := outputMembers a (by simp [ho])
    cases hm : c.mode with
    | memory array order fifo =>
      have lower : start ≤ qi := by simpa only [hm,InputQueueMatches] using matched
      have upper := channels.below a member
      change qi ≠ mapping a
      omega
    | channel array =>
      simp only [hm,InputQueueMatches] at matched
      simp only [hm,instructionChannels] at consistent
      change qi ≠ mapping a
      rw [matched.2]
      intro same
      have eq := channels.injective array matched.1 a member same
      exact consistent.2.2 (by simpa [eq] using ho)

end IRComparison.Circuit
