import IRComparison.Circuit.Lower

namespace IRComparison.Circuit

def tailHasSendBounds : HybridCompactChainControl.Code → Bool
  | .finish _ => true
  | .stage _ sender rest => (sendBound sender.body).isSome && tailHasSendBounds rest

def hasSendBounds : HybridUnifiedPipeline.Code → Bool
  | .expanded cs => cs.all fun c => (blocksBudget c.blocks).isSome
  | .compact c => (sendBound c.sender.body).isSome && tailHasSendBounds c.tail

def checkSendBudgets (code : HybridUnifiedPipeline.Code) : Except String Unit :=
  if hasSendBounds code then .ok () else
    .error "finite FIFO capacity is unknown: a data-dependent loop may send tokens"

theorem checkSendBudgets_sound (h : checkSendBudgets code = .ok ()) : hasSendBounds code = true := by
  unfold checkSendBudgets at h
  split at h
  · assumption
  · cases h

theorem expandedSendBounds (h : hasSendBounds (.expanded cs) = true) (c : HybridIR.Instruction) (hc : c ∈ cs) :
    ∃ bound, blocksBudget c.blocks = some bound := by
  have hh := List.all_eq_true.mp h c hc
  cases hb : blocksBudget c.blocks with
  | none => simp [hb] at hh
  | some n => exact ⟨n,rfl⟩

end IRComparison.Circuit
