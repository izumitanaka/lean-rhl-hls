import IRComparison.Memory.StreamFusion

namespace IRComparison.PipelineShapes
open WindowPipeline

def Same (s t : State) : Prop := ∀ a, (s.arrays a).size = (t.arrays a).size

theorem write_same (h : s.write a j v = some t) : Same s t := by
  unfold State.write at h
  split at h
  · simp at h
  · split at h
    · simp at h; subst t; intro b; by_cases hb : b = a <;> simp [hb]
    · simp at h

theorem fold_same {f : State → α → Option State}
    (hf : ∀ s a t, f s a = some t → Same s t) (xs : List α) (h : xs.foldlM f s = some t) : Same s t := by
  induction xs generalizing s with
  | nil => simp at h; subst t; intro a; rfl
  | cons a xs ih =>
    simp only [List.foldlM_cons] at h
    cases hs : f s a with
    | none => simp [hs] at h
    | some u =>
      have tail := ih (s:=u) (by simpa [hs] using h)
      exact fun b => (hf s a u hs b).trans (tail b)

theorem body_same (b : Imperative.Cmd) (h : b.eval i x y s ls = some t) : Same s t := by
  induction b generalizing s t ls with
  | skip => cases h; intro a; rfl
  | assign r e =>
    cases he : e.eval i x y s ls <;> simp [Imperative.Cmd.eval,he] at h
    subst t; intro a; rfl
  | store a j e =>
    cases hj : j.eval i x y s ls <;> simp [Imperative.Cmd.eval,hj] at h
    cases he : e.eval i x y s ls <;> simp [he] at h
    exact write_same h
  | letValue e b ih =>
    cases he : e.eval i x y s ls <;> simp [Imperative.Cmd.eval,he] at h
    exact ih h
  | seq a b ha hb =>
    cases he : a.eval i x y s ls <;> simp [Imperative.Cmd.eval,he] at h
    exact fun k => (ha he k).trans (hb h k)
  | branch e a b ha hb =>
    cases he : e.eval i x y s ls <;> simp [Imperative.Cmd.eval,he] at h
    split at h
    · exact hb h
    · exact ha h
  | «repeat» n b ih => exact fold_same (fun _ _ _ h => ih h) _ h
  | forRange n b ih =>
    cases he : n.eval i x y s ls <;> simp [Imperative.Cmd.eval,he] at h
    exact fold_same (fun _ _ _ h => ih h) _ h

theorem blocks_same (blocks : List WindowTransport.Block)
    (h : WindowTransport.eval input x y blocks old s q = some (t,rest)) : Same s t := by
  induction blocks generalizing old s q with
  | nil => simp [WindowTransport.eval] at h; obtain ⟨rfl,_⟩ := h; intro a; rfl
  | cons b bs ih =>
    cases hl : WindowFIFO.execute input old b.loads q <;> simp [WindowTransport.eval,hl] at h
    rename_i pair
    obtain ⟨vs,qs⟩ := pair
    cases hb : b.body.eval b.index x y s vs <;> simp [hb] at h
    exact fun a => (body_same b.body hb a).trans (ih h a)

theorem stage_same (p : Stage) (ready : p.Ready s) (h : p.source x y s = some t) : Same s t := by
  obtain ⟨q,hq,hc⟩ := p.queue_ready s ready
  have he := p.correct s ready.1 x y q hc
  rw [h] at he
  cases hb : WindowTransport.eval (arrayInput (s.arrays p.array)) x y p.code [] s q with
  | none => simp [hb] at he
  | some pair =>
    obtain ⟨u,rest⟩ := pair
    simp [hb] at he
    subst u
    exact blocks_same p.code hb

/-- Static allocation metadata shared by all regions. -/
def Layout (sizes : Nat → Nat) (s : State) : Prop := ∀ a, (s.arrays a).size = sizes a

theorem Layout.after (h : Layout sizes s) (same : Same s t) : Layout sizes t :=
  fun a => (same a).symm.trans (h a)

end IRComparison.PipelineShapes
