import IRComparison.Hybrid.HybridSource
import IRComparison.Memory.StreamConsumer

namespace IRComparison.HybridSafety
open HybridIR StreamState StreamConsumer

def avoids (array : Nat) : ReadCode → Bool
  | .pure .. | .register .. => true
  | .memory a _ => a != array
  | .bind first next => avoids array first && avoids array next
  | .branch _ yes no => avoids array yes && avoids array no

theorem read_correct (e : ReadCode) (safe : avoids array e = true) (h : Agree array s t) :
    e.eval i x y s ls temps = e.eval i x y t ls temps := by
  induction e generalizing temps with
  | pure => rfl
  | register r => simp [ReadCode.eval,h.regs]
  | memory a j =>
    have hn : a ≠ array := by simpa [avoids] using safe
    simp only [ReadCode.eval,h.arrays a hn]
  | bind first next hf hn =>
    simp only [avoids,Bool.and_eq_true] at safe
    simp only [ReadCode.eval,hf safe.1,hn safe.2]
  | branch c yes no hy hn =>
    simp only [avoids,Bool.and_eq_true] at safe
    simp only [ReadCode.eval,hy safe.1,hn safe.2]

structure Checked (array : Nat) (body : MemoryCmd) : Type where
  correct : ∀ i x y s ls, (body.eval i x y s ls).map (erase array) = body.eval i x y (erase array s) ls

/-- Read/write exclusion is checked after window substitution. This check
    never removes a remaining memory access by assumption. -/
def check (array : Nat) : (body : MemoryCmd) → Option (Checked array body)
  | .skip => some ⟨by intros; rfl⟩
  | .assign r e =>
    if safe : avoids array e = true then some ⟨by
      intro i x y s ls
      simp only [MemoryCmd.eval,← read_correct e safe (erase_agree s)]
      cases he : e.eval i x y s ls [] <;> rfl⟩ else none
  | .store a j e =>
    if different : a ≠ array then
      if safeJ : avoids array j = true then
        if safeE : avoids array e = true then some ⟨by
          intro i x y s ls
          simp only [MemoryCmd.eval,← read_correct j safeJ (erase_agree s),← read_correct e safeE (erase_agree s)]
          cases hj : j.eval i x y s ls [] with
          | none => rfl
          | some index =>
            cases he : e.eval i x y s ls [] with
            | none => rfl
            | some v => exact erase_write s different⟩ else none
      else none
    else none
  | .letValue e b =>
    if safe : avoids array e = true then do
      let cb ← check array b
      return ⟨by
        intro i x y s ls
        simp only [MemoryCmd.eval,← read_correct e safe (erase_agree s)]
        cases he : e.eval i x y s ls [] with
        | none => rfl
        | some v => exact cb.correct i x y s (v::ls)⟩
    else none
  | .seq a b => do
    let ca ← check array a
    let cb ← check array b
    return ⟨by
      intro i x y s ls
      simp only [MemoryCmd.eval,← ca.correct i x y s ls]
      cases ha : a.eval i x y s ls with
      | none => rfl
      | some t => exact cb.correct i x y t ls⟩
  | .branch e a b =>
    if safe : avoids array e = true then do
      let ca ← check array a
      let cb ← check array b
      return ⟨by
        intro i x y s ls
        simp only [MemoryCmd.eval,← read_correct e safe (erase_agree s)]
        cases he : e.eval i x y s ls [] with
        | none => rfl
        | some v =>
          simp only [bind,Option.bind]
          split
          · exact ca.correct i x y s ls
          · exact cb.correct i x y s ls⟩
    else none
  | .repeat .. | .forRange .. => none


end IRComparison.HybridSafety
