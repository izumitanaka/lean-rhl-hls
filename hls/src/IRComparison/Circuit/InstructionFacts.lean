import IRComparison.Circuit.InputSetup
import IRComparison.Circuit.ChannelView
import IRComparison.Circuit.CommunicationCheck
import IRComparison.Circuit.ExpandedProjection
import IRComparison.Circuit.BlocksFullSound

namespace IRComparison.Circuit

def eraseOutput (output : Option Nat) : Schedule :=
  match output with | none => .skip | some a => .step (.erase a)

def Payload.eraseOutput (p : Payload) (output : Option Nat) : Payload :=
  match output with | none => p | some a => p.erase a

theorem eraseOutput_eval (p : Payload) (output : Option Nat) :
    (eraseOutput output).Eval cap p (some (p.eraseOutput output)) := by
  cases output with
  | none => exact .skip
  | some a => exact erase_eval p a

theorem put_twice (qs : GlobalPipeline.Queues) (a : Nat) (first last : List Int) :
    GlobalPipeline.put (GlobalPipeline.put qs a first) a last = GlobalPipeline.put qs a last := by
  funext n
  by_cases h : n = a <;> simp [GlobalPipeline.put,h]

theorem put_commute (qs : GlobalPipeline.Queues) (h : a ≠ b) (first last : List Int) :
    GlobalPipeline.put (GlobalPipeline.put qs a first) b last = GlobalPipeline.put (GlobalPipeline.put qs b last) a first := by
  funext n
  by_cases ha : n = a
  · subst n; simp [GlobalPipeline.put,h]
  · by_cases hb : n = b
    · subst n; simp [GlobalPipeline.put,ha]
    · simp [GlobalPipeline.put,ha,hb]

def InputQueueMatches (ids : List Nat) (mapping : Nat → Nat) (next : Nat) (mode : GlobalPipeline.InputMode) (qi : Nat) : Prop :=
  match mode with
  | .channel a => a ∈ ids ∧ qi = mapping a
  | .memory _ _ _ => next ≤ qi

def OutputQueueMatches (ids : List Nat) (mapping : Nat → Nat) (next : Nat) (output : Option Nat) (qo : Nat) : Prop :=
  match output with
  | some a => a ∈ ids ∧ qo = mapping a
  | none => next ≤ qo

theorem inputSetupResult_source (p : Payload) (mode : GlobalPipeline.InputMode)
    (scopedMode : ModeScoped limit mode) (freshSnapshot : limit ≤ frozen)
    (matched : InputQueueMatches ids mapping next mode qi) :
    inputSetupResult mode qi (p.snapshot frozen input) =
      (mode.eval (trimState limit p.data) (channelView ids mapping p.queues)).map
        ((p.snapshot frozen input).setQueue qi) := by
  cases mode with
  | channel a =>
    obtain ⟨member,rfl⟩ := matched
    simp only [inputSetupResult,GlobalPipeline.InputMode.eval,channelView,member,↓reduceIte,Option.map_some]
    exact congrArg some (Payload.setQueue_self (p.snapshot frozen input) (mapping a)).symm
  | memory a order fifo =>
    have less : a < limit := scopedMode
    have different : a ≠ frozen := by omega
    simp [inputSetupResult,GlobalPipeline.InputMode.eval,trimState,Payload.snapshot,less,different]

theorem channelView_input_clear (channels : ChannelMap ids mapping next)
    (consistent : instructionChannels ids c) (matched : InputQueueMatches ids mapping next c.mode qi) :
    channelView ids mapping (GlobalPipeline.put physical qi []) =
      GlobalPipeline.put (channelView ids mapping physical) c.input [] := by
  cases hm : c.mode with
  | channel a =>
    simp only [hm,InputQueueMatches] at matched
    simp only [hm,instructionChannels] at consistent
    obtain ⟨member,rfl⟩ := matched
    rw [← consistent.1]
    exact channelView_public channels member
  | memory a order fifo =>
    simp only [hm,InputQueueMatches] at matched
    simp only [hm,instructionChannels] at consistent
    rw [channelView_private channels matched,← consistent.1,channelView_put_unmapped consistent.2]

def outputQueues (output : Option Nat) (qs : GlobalPipeline.Queues) (values : List Int) :=
  match output with
  | none => qs
  | some a => GlobalPipeline.put qs a values

theorem channelView_output (channels : ChannelMap ids mapping next)
    (matched : OutputQueueMatches ids mapping next output qo) :
    channelView ids mapping (GlobalPipeline.put physical qo values) =
      outputQueues output (channelView ids mapping physical) values := by
  cases output with
  | none => exact channelView_private channels matched
  | some a => obtain ⟨member,rfl⟩ := matched; exact channelView_public channels member

theorem trim_snapshot_ge (p : Payload) (source : Nat) (fresh : limit ≤ frozen) :
    trimState limit (p.snapshot frozen source).data = trimState limit p.data := by
  unfold trimState Payload.snapshot
  congr 1
  funext a
  by_cases h : a < limit
  · simp [h,show a ≠ frozen from by omega]
  · simp [h]

end IRComparison.Circuit
