import IRComparison.Circuit.Lower

namespace IRComparison.Circuit

def channelIds (code : List HybridIR.Instruction) := (code.filterMap (·.output)).eraseDups

/-- Resource consistency of the existing whole-array representation policy.
The input name must agree with its input mode, selected channel arrays must
stay channels, and a destructive input queue cannot alias the cleared output.
These are control-IR representation invariants, not arithmetic restrictions. -/
def instructionChannels (ids : List Nat) (c : HybridIR.Instruction) : Prop :=
  match c.mode with
  | .memory a _ _ => a = c.input ∧ a ∉ ids
  | .channel a => a = c.input ∧ a ∈ ids ∧ c.output ≠ some a

instance (ids : List Nat) (c : HybridIR.Instruction) : Decidable (instructionChannels ids c) := by
  unfold instructionChannels
  split <;> infer_instance

/-- Metadata-only check: never construct the proof's reference blocks. -/
def symbolicInstructionChannels (ids : List Nat) (c : HybridSymbolicGlobal.Instruction) : Prop :=
  match symbolicMode c with
  | .memory a _ _ => a = symbolicInput c ∧ a ∉ ids
  | .channel a => a = symbolicInput c ∧ a ∈ ids ∧ symbolicOutput c ≠ some a

instance (ids : List Nat) (c : HybridSymbolicGlobal.Instruction) : Decidable (symbolicInstructionChannels ids c) := by
  unfold symbolicInstructionChannels
  split <;> infer_instance

def checkCommunication (code : HybridUnifiedPipeline.Code) : Except String Unit :=
  match code with
  | .compact _ | .regions _ => .ok ()
  | .symbolic cs =>
      if cs.all (fun c => decide (symbolicInstructionChannels (symbolicChannels cs) c)) then .ok ()
      else .error "inconsistent symbolic channels: whole-array policy or input/output alias"
  | .expanded cs =>
      if cs.all (fun c => decide (instructionChannels (channelIds cs) c)) then .ok ()
      else .error "inconsistent control-IR channels: input mode/name, whole-array policy, or input/output alias"

theorem communication_checked (h : checkCommunication (.expanded cs) = .ok ()) (c : HybridIR.Instruction) (hc : c ∈ cs) :
    instructionChannels (channelIds cs) c := by
  dsimp only [checkCommunication] at h
  split at h
  next hh => exact of_decide_eq_true (List.all_eq_true.mp hh c hc)
  next => cases h

end IRComparison.Circuit
