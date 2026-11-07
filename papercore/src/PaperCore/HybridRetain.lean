import PaperCore.HybridRules
import PaperCore.BufferNames
import PaperCore.ProgramState

namespace PaperCore.Hybrid
open MixedTarget

theorem retain_correct (code : Source Op) (typed : BufferView.Typed ordinary code)
    (retained : ∀ a ∈ ProgramState.sourceArrays code, ¬ fifo a) (extra : IndexMap → Prop) :
    Translation meaning ordinary fifo (fun _ _ indices => extra indices) code (retain code)
      (fun _ _ indices => extra indices) := by
  induction code with
  | action command =>
    cases command with
    | read x a e =>
      intro s t indices initial
      constructor
      · intro out run
        obtain ⟨target,executed,corr⟩ := retained_read_forward initial.1 (retained a (by simp [ProgramState.sourceArrays])) typed.2 run
        exact ⟨target,indices,executed,corr,initial.2⟩
      · intro out run
        obtain ⟨source,executed,corr⟩ := retained_read_backward initial.1 (retained a (by simp [ProgramState.sourceArrays])) typed.2 run
        exact ⟨source,indices,executed,corr,initial.2⟩
    | write a e x =>
      intro s t indices initial
      constructor
      · intro out run
        obtain ⟨target,executed,corr⟩ := retained_write_forward initial.1 (retained a (by simp [ProgramState.sourceArrays])) typed run
        exact ⟨target,indices,executed,corr,initial.2⟩
      · intro out run
        obtain ⟨source,executed,corr⟩ := retained_write_backward initial.1 (retained a (by simp [ProgramState.sourceArrays])) typed run
        exact ⟨source,indices,executed,corr,initial.2⟩
  | assign x e =>
    apply Translation.consequence (assign_valid (post := fun _ _ indices => extra indices) meaning typed.2)
    · intro regs heap indices h value _; exact h
    · intro regs heap indices h; exact h
  | seq a b ia ib =>
    exact Translation.seq
      (ia typed.1 (fun x hx => retained x (List.mem_append_left _ hx)))
      (ib typed.2 (fun x hx => retained x (List.mem_append_right _ hx)))
  | branch x a b ia ib =>
    apply Translation.branch typed.1
    · apply Translation.consequence (ia typed.2.1 (fun x hx => retained x (List.mem_append_left _ hx)))
      · intro regs heap indices h; exact h.1
      · intro regs heap indices h; exact h
    · apply Translation.consequence (ib typed.2.2 (fun x hx => retained x (List.mem_append_right _ hx)))
      · intro regs heap indices h; exact h.1
      · intro regs heap indices h; exact h
  | kernel body ih => exact Translation.kernel (ih typed retained)
  | loop x e stop step body ih =>
    have bodyCorrect := ih typed.2.2 retained
    have guarded : Translation meaning ordinary fifo
        (loopGuard (fun _ _ indices => extra indices) x stop) body (retain body)
        (advancePre (fun _ _ indices => extra indices) x step) := by
      apply Translation.consequence bodyCorrect
      · intro regs heap indices h; exact h.1
      · intro regs heap indices h value _; exact h
    apply Translation.consequence (Translation.loop meaning typed.2.1 typed.1 guarded)
    · intro regs heap indices h value _; exact h
    · intro regs heap indices h; exact h.1

#print axioms retain_correct
end PaperCore.Hybrid
