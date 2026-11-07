import IRComparison.Circuit.PreloadSound

namespace IRComparison.Circuit

def inputSetup (mode : GlobalPipeline.InputMode) (qi : Nat) : Schedule :=
  match mode with
  | .channel _ => .skip
  | .memory a order fifo => .seq (.step (.clear qi)) (if fifo then preload a qi order else .skip)

def inputSetupResult (mode : GlobalPipeline.InputMode) (qi : Nat) (p : Payload) : Option Payload :=
  match mode with
  | .channel _ => some p
  | .memory a order fifo =>
      (if fifo then CommunicationIR.emit (arrayInput (p.data.arrays a)) order else some []).map (p.setQueue qi)

theorem inputSetup_correct (mode : GlobalPipeline.InputMode) (qi : Nat) (p : Payload)
    (fits : ∀ a order, mode = .memory a order true → order.length ≤ cap qi) :
    (inputSetup mode qi).Eval cap p (inputSetupResult mode qi p) := by
  cases mode with
  | channel => exact .skip
  | memory a order fifo =>
    cases fifo with
    | false => exact .seq (clear_eval p qi) .skip
    | true =>
      have hh := preload_correct a qi order (p.clear qi) (by simpa [Payload.clear] using fits a order rfl)
      have result := Schedule.Eval.seq (clear_eval p qi) hh
      change (Schedule.seq (.step (.clear qi)) (preload a qi order)).Eval cap p _
      cases he : CommunicationIR.emit (arrayInput (p.data.arrays a)) order with
      | none => simpa [Payload.clear,he,inputSetupResult] using result
      | some values =>
        have qzero : (p.clear qi).queues qi = [] := by simp [Payload.clear]
        have dataSame : (p.clear qi).data = p.data := rfl
        simp only [dataSame,he,Option.map_some,qzero,List.nil_append] at result
        change (Schedule.seq (.step (.clear qi)) (preload a qi order)).Eval cap p
          (some ((p.setQueue qi []).setQueue qi values)) at result
        rw [Payload.setQueue_twice] at result
        simpa only [inputSetupResult,he,Option.map_some,↓reduceIte] using result

end IRComparison.Circuit
