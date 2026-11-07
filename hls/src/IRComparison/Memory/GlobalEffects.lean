import IRComparison.Memory.StreamChainEmit

namespace IRComparison.GlobalEffects
open WindowPipeline

def writes : Imperative.Cmd → List Nat
  | .store a _ _ => [a]
  | .seq a b | .branch _ a b => writes a ++ writes b
  | .letValue _ b | .repeat _ b | .forRange _ b => writes b
  | _ => []

theorem write_other {s t : State} (h : s.write a j v = some t) (hne : b ≠ a) : t.arrays b = s.arrays b := by
  unfold State.write at h
  split at h
  · simp at h
  · split at h
    · simp at h; subst t; simp [hne]
    · simp at h

theorem fold_preserves {f : State → α → Option State}
    (hf : ∀ s a t, f s a = some t → t.arrays k = s.arrays k)
    (xs : List α) (h : xs.foldlM f s = some t) : t.arrays k = s.arrays k := by
  induction xs generalizing s with
  | nil => simp at h; subst t; rfl
  | cons a as ih =>
    simp only [List.foldlM_cons] at h
    cases hs : f s a with
    | none => simp [hs] at h
    | some u => exact (ih (s:=u) (by simpa [hs] using h)).trans (hf s a u hs)

theorem body_preserves (body : Imperative.Cmd) (safe : a ∉ writes body)
    (h : body.eval i x y s ls = some t) : t.arrays a = s.arrays a := by
  induction body generalizing s t ls with
  | skip => cases h; rfl
  | assign r e =>
    cases he : e.eval i x y s ls <;> simp [Imperative.Cmd.eval,he] at h
    subst t; rfl
  | store b j e =>
    cases hj : j.eval i x y s ls <;> simp [Imperative.Cmd.eval,hj] at h
    cases he : e.eval i x y s ls <;> simp [he] at h
    exact write_other h (by simpa [writes] using safe)
  | letValue e b ih =>
    cases he : e.eval i x y s ls <;> simp [Imperative.Cmd.eval,he] at h
    exact ih safe h
  | seq b c hb hc =>
    simp only [writes,List.mem_append,not_or] at safe
    cases he : b.eval i x y s ls <;> simp [Imperative.Cmd.eval,he] at h
    exact (hc safe.2 h).trans (hb safe.1 he)
  | branch e b c hb hc =>
    simp only [writes,List.mem_append,not_or] at safe
    cases he : e.eval i x y s ls <;> simp [Imperative.Cmd.eval,he] at h
    split at h
    · exact hc safe.2 h
    · exact hb safe.1 h
  | «repeat» n b ih => exact fold_preserves (fun _ _ _ h => ih safe h) _ h
  | forRange n b ih =>
    cases he : n.eval i x y s ls <;> simp [Imperative.Cmd.eval,he] at h
    exact fold_preserves (fun _ _ _ h => ih safe h) _ h

def blockWrites (blocks : List WindowTransport.Block) := blocks.flatMap (fun b => writes b.body)

theorem blocks_preserve (blocks : List WindowTransport.Block) (safe : a ∉ blockWrites blocks)
    (h : WindowTransport.eval input x y blocks old s q = some (t,rest)) : t.arrays a = s.arrays a := by
  induction blocks generalizing old s q with
  | nil => simp [WindowTransport.eval] at h; obtain ⟨rfl,_⟩ := h; rfl
  | cons b bs ih =>
    simp only [blockWrites,List.flatMap_cons,List.mem_append,not_or] at safe
    cases hl : WindowFIFO.execute input old b.loads q <;> simp [WindowTransport.eval,hl] at h
    rename_i pair
    obtain ⟨vs,qs⟩ := pair
    cases hb : b.body.eval b.index x y s vs <;> simp [hb] at h
    exact (ih safe.2 h).trans (body_preserves b.body safe.1 hb)

theorem stage_preserves (p : Stage) (safe : a ∉ blockWrites p.code) (ready : p.Ready s)
    (h : p.source x y s = some t) : t.arrays a = s.arrays a := by
  obtain ⟨q,_,hc⟩ := p.queue_ready s ready
  have he := p.correct s ready.1 x y q hc
  rw [h] at he
  cases hb : WindowTransport.eval (arrayInput (s.arrays p.array)) x y p.code [] s q with
  | none => simp [hb] at he
  | some pair =>
    obtain ⟨u,rest⟩ := pair
    simp [hb] at he
    subst u
    exact blocks_preserve p.code safe hb

end IRComparison.GlobalEffects
