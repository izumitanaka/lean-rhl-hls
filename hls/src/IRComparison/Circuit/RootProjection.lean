import IRComparison.Circuit.IterationProjection
import IRComparison.Circuit.PayloadOperations

namespace IRComparison.Circuit

theorem commandWrites_mem (c : HybridIR.Cmd) (h : a ∈ commandWrites c) : a ∈ allCommandArrays c := by
  induction c with
  | skip | assign | send => simp [commandWrites] at h
  | store array j e =>
    have ha : a = array := by simpa [commandWrites] using h
    simp [allCommandArrays,ha]
  | letValue e b ih | forRange e b ih => exact List.mem_append_right _ (ih h)
  | «repeat» n b ih => exact ih h
  | seq x y ix iy =>
    rcases List.mem_append.mp h with hx | hy
    · exact List.mem_append_left _ (ix hx)
    · exact List.mem_append_right _ (iy hy)
  | branch e x y ix iy =>
    rcases List.mem_append.mp h with hx | hy
    · simp [allCommandArrays,ix hx]
    · simp [allCommandArrays,iy hy]

theorem trim_snapshot (p : Payload) (source : Nat) :
    trimState limit (p.snapshot limit source).data = trimState limit p.data := by
  unfold trimState Payload.snapshot
  congr 1
  funext a
  by_cases h : a < limit
  · simp [h,show a ≠ limit from by omega]
  · simp [h]

def rootContinuation (code : HybridCompactChainControl.RootCode) (input : Input) (x y : Int) (s : State) : Option State := do
  let (t,q) ← code.sender.eval input x y s
  code.tail.eval x y (StreamConsumer.erase code.output t) q

theorem rootContinuation_trim (code : HybridCompactChainControl.RootCode)
    (senderSafe : ∀ a ∈ allCommandArrays code.sender.body, a < limit)
    (tailSafe : ∀ a ∈ tailArrays code.tail, a < limit) :
    (rootContinuation code input x y s).map (trimState limit) = rootContinuation code input x y (trimState limit s) := by
  simp only [rootContinuation,← producer_trim code.sender senderSafe]
  cases code.sender.eval input x y s with
  | none => rfl
  | some pair =>
    obtain ⟨t,q⟩ := pair
    simpa only [Option.map_some,bind,Option.bind,trimResult,← trim_erase] using
      tail_trim (x:=x) (y:=y) (s:=StreamConsumer.erase code.output t) (qi:=q) code.tail tailSafe

theorem root_snapshot_correct (code : HybridCompactChainControl.RootCode) (p : Payload)
    (senderSafe : ∀ a ∈ allCommandArrays code.sender.body, a < limit)
    (tailSafe : ∀ a ∈ tailArrays code.tail, a < limit) :
    (rootContinuation code (arrayInput ((p.erase code.output).data.arrays code.inputArray)) x y
      ((p.erase code.output).snapshot limit code.inputArray).data).map (trimState limit) =
      (code.eval x y p.data).map (trimState limit) := by
  change _ = (rootContinuation code (arrayInput ((p.erase code.output).data.arrays code.inputArray)) x y
    (p.erase code.output).data).map (trimState limit)
  rw [rootContinuation_trim code senderSafe tailSafe,rootContinuation_trim code senderSafe tailSafe,trim_snapshot]

end IRComparison.Circuit
