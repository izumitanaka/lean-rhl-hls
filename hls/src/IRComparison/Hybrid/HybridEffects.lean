import IRComparison.Hybrid.HybridStage
import IRComparison.Memory.GlobalEffects

namespace IRComparison.HybridEffects
open HybridStage
open GlobalEffects (write_other fold_preserves)

def writes : HybridIR.MemoryCmd → List Nat
  | .store a _ _ => [a]
  | .seq a b | .branch _ a b => writes a ++ writes b
  | .letValue _ b | .repeat _ b | .forRange _ b => writes b
  | _ => []

theorem body_preserves (body : HybridIR.MemoryCmd) (safe : a ∉ writes body)
    (h : body.eval i x y s ls = some t) : t.arrays a = s.arrays a := by
  induction body generalizing s t ls with
  | skip => cases h; rfl
  | assign r e =>
    cases he : e.eval i x y s ls [] <;> simp [HybridIR.MemoryCmd.eval,he] at h
    subst t; rfl
  | store b j e =>
    cases hj : j.eval i x y s ls [] <;> simp [HybridIR.MemoryCmd.eval,hj] at h
    cases he : e.eval i x y s ls [] <;> simp [he] at h
    exact write_other h (by simpa [writes] using safe)
  | letValue e b ih =>
    cases he : e.eval i x y s ls [] <;> simp [HybridIR.MemoryCmd.eval,he] at h
    exact ih safe h
  | seq b c hb hc =>
    simp only [writes,List.mem_append,not_or] at safe
    cases he : b.eval i x y s ls <;> simp [HybridIR.MemoryCmd.eval,he] at h
    exact (hc safe.2 h).trans (hb safe.1 he)
  | branch e b c hb hc =>
    simp only [writes,List.mem_append,not_or] at safe
    cases he : e.eval i x y s ls [] <;> simp [HybridIR.MemoryCmd.eval,he] at h
    split at h
    · exact hc safe.2 h
    · exact hb safe.1 h
  | «repeat» n b ih => exact fold_preserves (fun _ _ _ h => ih safe h) _ h
  | forRange n b ih =>
    cases he : n.eval i x y s ls [] <;> simp [HybridIR.MemoryCmd.eval,he] at h
    exact fold_preserves (fun _ _ _ h => ih safe h) _ h

def blockWrites (blocks : List HybridWindowTransport.Block) := blocks.flatMap (fun b => writes b.body)

theorem blocks_preserve (blocks : List HybridWindowTransport.Block) (safe : a ∉ blockWrites blocks)
    (h : HybridWindowTransport.eval input x y blocks old s q = some (t,rest)) : t.arrays a = s.arrays a := by
  induction blocks generalizing old s q with
  | nil => simp [HybridWindowTransport.eval] at h; obtain ⟨rfl,_⟩ := h; rfl
  | cons b bs ih =>
    simp only [blockWrites,List.flatMap_cons,List.mem_append,not_or] at safe
    cases hl : WindowFIFO.execute input old b.loads q <;> simp [HybridWindowTransport.eval,hl] at h
    rename_i pair
    obtain ⟨vs,qs⟩ := pair
    cases hb : b.body.eval b.index x y s vs <;> simp [hb] at h
    exact (ih safe.2 h).trans (body_preserves b.body safe.1 hb)

theorem stage_preserves (p : Stage) (safe : a ∉ blockWrites p.code) (ready : p.Ready s)
    (h : p.source x y s = some t) : t.arrays a = s.arrays a := by
  obtain ⟨q,_,hc⟩ := p.queue_ready s ready
  have he := p.correct s ready.1 x y q hc
  rw [h] at he
  cases hb : HybridWindowTransport.eval (arrayInput (s.arrays p.array)) x y p.code [] s q with
  | none => simp [hb] at he
  | some pair =>
    obtain ⟨u,rest⟩ := pair
    simp [hb] at he
    subst u
    exact blocks_preserve p.code safe hb

end IRComparison.HybridEffects
