import IRComparison.Circuit.Layout

namespace IRComparison.Circuit

/-- Hide compiler-private snapshot IDs when comparing observable states.
Original arrays and every scalar register retain their original values. -/
def trimState (limit : Nat) (s : State) : State :=
  { s with arrays := fun a => if a < limit then s.arrays a else #[] }

theorem trim_set : trimState limit (s.set r v) = (trimState limit s).set r v := rfl

theorem trim_write (ha : a < limit) :
    (s.write a i v).map (trimState limit) = (trimState limit s).write a i v := by
  by_cases neg : i < 0
  · simp [State.write,neg]
  · by_cases hi : i.toNat < (s.arrays a).size
    · simp only [State.write,neg,↓reduceIte,trimState,ha,hi,↓reduceDIte,Option.map_some]
      congr 2
      funext k
      by_cases hk : k = a
      · subst k; simp [ha]
      · simp [hk]
    · simp [State.write,trimState,neg,hi,ha]

theorem read_trim (e : HybridIR.ReadCode) (safe : ∀ a ∈ readArrays e, a < limit) :
    e.eval i x y (trimState limit s) ls ts = e.eval i x y s ls ts := by
  induction e generalizing ts with
  | pure | register => rfl
  | memory a j =>
    have ha := safe a (by simp [readArrays])
    simp [HybridIR.ReadCode.eval,trimState,ha]
  | bind a b ia ib =>
    have ha : ∀ n ∈ readArrays a, n < limit := fun n hn => safe n (List.mem_append_left _ hn)
    have hb : ∀ n ∈ readArrays b, n < limit := fun n hn => safe n (List.mem_append_right _ hn)
    simp only [HybridIR.ReadCode.eval,ia ha,ib hb]
  | branch e a b ia ib =>
    have ha : ∀ n ∈ readArrays a, n < limit := fun n hn => safe n (List.mem_append_left _ hn)
    have hb : ∀ n ∈ readArrays b, n < limit := fun n hn => safe n (List.mem_append_right _ hn)
    simp only [HybridIR.ReadCode.eval,ia ha,ib hb]

theorem fold_project {f : α → β → Option α} {g : γ → β → Option γ} {project : α → γ}
    (step : ∀ s a, (f s a).map project = g (project s) a) (xs : List β) (s : α) :
    (xs.foldlM f s).map project = xs.foldlM g (project s) := by
  induction xs generalizing s with
  | nil => rfl
  | cons a xs ih =>
    rw [List.foldlM_cons,List.foldlM_cons,← step]
    cases f s a with
    | none => rfl
    | some t => exact ih t

def trimResult (limit : Nat) (p : State × List Int) := (trimState limit p.1,p.2)

theorem command_trim (c : HybridIR.Cmd) (safe : ∀ a ∈ allCommandArrays c, a < limit) :
    (c.eval i x y s q ls).map (trimResult limit) = c.eval i x y (trimState limit s) q ls := by
  induction c generalizing s q ls with
  | skip => rfl
  | assign r e =>
    have hh := read_trim (s:=s) (i:=i) (x:=x) (y:=y) (ls:=ls) (ts:=[]) e safe
    simp only [HybridIR.Cmd.eval,hh]
    cases e.eval i x y s ls [] <;> rfl
  | store a j e =>
    have ha := safe a (by simp [allCommandArrays])
    have hj : ∀ n ∈ readArrays j, n < limit := fun n hn => safe n (by simp [allCommandArrays,hn])
    have hv : ∀ n ∈ readArrays e, n < limit := fun n hn => safe n (by simp [allCommandArrays,hn])
    simp only [HybridIR.Cmd.eval,read_trim j hj,read_trim e hv]
    cases j.eval i x y s ls [] with
    | none => rfl
    | some index =>
      cases e.eval i x y s ls [] with
      | none => rfl
      | some value =>
        have hw := trim_write (s:=s) (i:=index) (v:=value) ha
        simp only [bind,Option.bind]
        rw [← hw]
        cases s.write a index value <;> rfl
  | send e =>
    simp only [HybridIR.Cmd.eval,read_trim e safe]
    cases e.eval i x y s ls [] <;> rfl
  | letValue e b ih =>
    have he : ∀ n ∈ readArrays e, n < limit := fun n hn => safe n (List.mem_append_left _ hn)
    have hb : ∀ n ∈ allCommandArrays b, n < limit := fun n hn => safe n (List.mem_append_right _ hn)
    simp only [HybridIR.Cmd.eval,read_trim e he]
    cases e.eval i x y s ls [] with
    | none => rfl
    | some v => exact ih hb
  | seq a b ia ib =>
    have ha : ∀ n ∈ allCommandArrays a, n < limit := fun n hn => safe n (List.mem_append_left _ hn)
    have hb : ∀ n ∈ allCommandArrays b, n < limit := fun n hn => safe n (List.mem_append_right _ hn)
    simp only [HybridIR.Cmd.eval,← ia ha]
    cases a.eval i x y s q ls with
    | none => rfl
    | some pair => obtain ⟨t,qs⟩ := pair; exact ib hb
  | branch e a b ia ib =>
    have he : ∀ n ∈ readArrays e, n < limit := fun n hn => safe n (by simp [allCommandArrays,hn])
    have ha : ∀ n ∈ allCommandArrays a, n < limit := fun n hn => safe n (by simp [allCommandArrays,hn])
    have hb : ∀ n ∈ allCommandArrays b, n < limit := fun n hn => safe n (by simp [allCommandArrays,hn])
    simp only [HybridIR.Cmd.eval,read_trim e he]
    cases e.eval i x y s ls [] with
    | none => rfl
    | some v =>
      simp only [bind,Option.bind]
      split
      · exact ia ha
      · exact ib hb
  | «repeat» n b ih => exact fold_project (fun st _ => ih safe (s:=st.1) (q:=st.2)) (List.range n) (s,q)
  | forRange e b ih =>
    have he : ∀ n ∈ readArrays e, n < limit := fun n hn => safe n (List.mem_append_left _ hn)
    have hb : ∀ n ∈ allCommandArrays b, n < limit := fun n hn => safe n (List.mem_append_right _ hn)
    simp only [HybridIR.Cmd.eval,read_trim e he]
    cases e.eval i x y s ls [] with
    | none => rfl
    | some n => exact fold_project (fun st (j:Nat) => ih hb (s:=st.1) (q:=st.2) (ls:=(j:Int)::ls)) (List.range n.toNat) (s,q)

end IRComparison.Circuit
