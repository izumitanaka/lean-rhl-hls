import IRComparison.Circuit.Lower

namespace IRComparison.Circuit

theorem newSlots_shape (n : Nat) (b : Build) :
    ((newSlots n).run b).1 = List.range' b.wires.size n ∧
    ((newSlots n).run b).2.wires.size = b.wires.size+n := by
  induction n generalizing b with
  | zero => exact ⟨rfl,by simp [newSlots,StateT.run,pure,StateT.pure]⟩
  | succ n ih =>
    have hh := ih (b.addWire wordRange)
    dsimp only [StateT.run] at hh
    dsimp only [newSlots,fresh,bind,pure,StateT.bind,StateT.pure,StateT.run]
    generalize he : newSlots n (b.addWire wordRange) = pair at *
    obtain ⟨slots,b1⟩ := pair
    have size : (b.addWire wordRange).wires.size = b.wires.size+1 := by simp [Build.addWire]
    constructor
    · simpa [List.range'_succ,size] using congrArg (List.cons b.wires.size) hh.1
    · change b1.wires.size = b.wires.size+(n+1)
      have hh := hh.2
      simp only [size] at hh
      omega

end IRComparison.Circuit
