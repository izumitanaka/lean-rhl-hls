import IRComparison.Hybrid.HybridWordCommand

/-! Fixed source buffers: declarations are external to execution. Copying writes
an existing destination, including inside loops; it never declares storage. -/
namespace IRComparison.FixedMemory
open HybridWord

abbrev Declarations := Array (Nat × Nat)
def lookup (ds : Declarations) (a : Nat) : Option Nat := ds.toList.lookup a
def sizes (ds : Declarations) (a : Nat) : Nat := (lookup ds a).getD 0
def unique (ds : Declarations) : Bool := decide (ds.toList.map Prod.fst).Nodup

def exprDeclared (ds : Declarations) : HybridWord.Expr → Bool
  | .lit _ | .index | .left | .right | .local _ | .reg _ => true
  | .add a b | .sub a b | .mul a b | .div a b => exprDeclared ds a && exprDeclared ds b
  | .read a j => (lookup ds a).isSome && exprDeclared ds j
  | .readNat a _ => (lookup ds a).isSome
  | .select c a b => exprDeclared ds c && exprDeclared ds a && exprDeclared ds b

/-- Validate every branch and loop body, not just the executed path. In this
entry copy is a WHOLE-array operation, so both declarations must match count. -/
def declared (ds : Declarations) : HybridWord.Cmd → Bool
  | .skip => true
  | .assign _ e => exprDeclared ds e
  | .store a j e => (lookup ds a).isSome && exprDeclared ds j && exprDeclared ds e
  | .letValue e b => exprDeclared ds e && declared ds b
  | .seq a b => declared ds a && declared ds b
  | .branch c a b => exprDeclared ds c && declared ds a && declared ds b
  | .repeat _ b | .forStatic _ _ _ b => declared ds b
  | .forRange e b => exprDeclared ds e && declared ds b
  | .copy dst src n => decide (lookup ds dst = some n ∧ lookup ds src = some n)

theorem declared_copy (h : declared ds (.copy dst src n) = true) :
    lookup ds dst = some n ∧ lookup ds src = some n := by
  simpa [declared] using h

def SameSizes (s t : HybridWord.State) : Prop := ∀ a, (t.arrays a).size = (s.arrays a).size

theorem SameSizes.refl (s : HybridWord.State) : SameSizes s s := fun _ => rfl
theorem SameSizes.trans (h : SameSizes s t) (g : SameSizes t u) : SameSizes s u :=
  fun a => (g a).trans (h a)

theorem write_sizes (h : s.write a j v = some t) : SameSizes s t := by
  simp only [HybridWord.State.write] at h
  split at h
  · cases h
    intro k
    by_cases hk : k = a <;> simp [hk]
  · contradiction

theorem writeNat_sizes (h : s.writeNat a j v = some t) : SameSizes s t := by
  simp only [HybridWord.State.writeNat] at h
  split at h
  · cases h
    intro k
    by_cases hk : k = a <;> simp [hk]
  · contradiction

theorem fold_sizes (f : HybridWord.State → α → Option HybridWord.State)
    (step : ∀ s a t, f s a = some t → SameSizes s t)
    (xs : List α) (h : xs.foldlM f s = some t) : SameSizes s t := by
  induction xs generalizing s with
  | nil => cases h; exact .refl _
  | cons a rest ih =>
    simp only [List.foldlM_cons] at h
    cases he : f s a with
    | none => simp [he] at h
    | some u =>
      simp only [he, bind, Option.bind] at h
      exact (step _ _ _ he).trans (ih h)

theorem copy_sizes (h : s.copy dst src n = some t) : SameSizes s t := by
  apply fold_sizes _ ?_ _ h
  intro u j v he
  cases hr : (u.arrays src)[j]? with
  | none => simp [hr] at he
  | some w =>
    simp only [hr, bind, Option.bind] at he
    exact writeNat_sizes he

/-- Prefix invariant for the executable copy, including copying a region to
itself. It refers to the ORIGINAL source array, not a changing memory view. -/
theorem copy_prefix (s : HybridWord.State) (dst src n : Nat)
    (hs : n ≤ (s.arrays src).size) (hd : n ≤ (s.arrays dst).size) :
    ∃ t, s.copy dst src n = some t ∧ t.regs = s.regs ∧
      (∀ a, a ≠ dst → t.arrays a = s.arrays a) ∧
      (∀ j, (t.arrays dst)[j]? =
        if j < n then (s.arrays src)[j]? else (s.arrays dst)[j]?) := by
  induction n with
  | zero => exact ⟨s,rfl,rfl,fun _ _ => rfl,by simp⟩
  | succ n ih =>
    obtain ⟨t,run,regs,frame,initialPart⟩ := ih (by omega) (by omega)
    have hs' : n < (s.arrays src).size := by omega
    have hd' : n < (t.arrays dst).size := by rw [copy_sizes run dst]; omega
    have read : (t.arrays src)[n]? = some (s.arrays src)[n] := by
      by_cases h : src = dst
      · subst src
        rw [initialPart]
        simp [Array.getElem?_eq_getElem hs']
      · rw [frame src h,Array.getElem?_eq_getElem hs']
    let u : HybridWord.State := { t with arrays := fun a =>
      if a = dst then (Array.set (t.arrays dst) n ((s.arrays src)[n]) hd') else t.arrays a }
    refine ⟨u,?_,regs,?_,?_⟩
    · change (List.range n).foldlM _ s = some t at run
      rw [HybridWord.State.copy,List.range_succ,List.foldlM_append,run]
      simp [read,HybridWord.State.writeNat,hd',u]
    · intro a ha
      simpa [u,ha] using frame a ha
    · intro j
      simp only [u,↓reduceIte,Array.getElem?_set]
      by_cases hj : n = j
      · subst j
        simp [Array.getElem?_eq_getElem hs']
      · rw [if_neg hj,initialPart]
        have : (j < n) = (j < n+1) := propext (by omega)
        simp only [this]

/-- Whole-array copy, with fixed pre-existing equal-size regions. -/
theorem copy_complete (s : HybridWord.State) (dst src n : Nat)
    (hs : (s.arrays src).size = n) (hd : (s.arrays dst).size = n) :
    ∃ t, s.copy dst src n = some t ∧ t.regs = s.regs ∧
      t.arrays dst = s.arrays src ∧ (∀ a, a ≠ dst → t.arrays a = s.arrays a) := by
  obtain ⟨t,run,regs,frame,initialPart⟩ := copy_prefix s dst src n (by omega) (by omega)
  refine ⟨t,run,regs,?_,frame⟩
  apply Array.ext_getElem?
  intro j
  rw [initialPart]
  split
  · rfl
  · rw [Array.getElem?_eq_none (by omega),Array.getElem?_eq_none (by omega)]

/-- All accepted commands preserve array lengths, including failed bounds checks
on other paths, self copies, nested loops, and ordinary element updates. -/
theorem eval_sizes (c : HybridWord.Cmd) (h : c.eval i x y s ls = some t) : SameSizes s t := by
  induction c generalizing s ls t with
  | skip => cases h; exact .refl _
  | assign r e =>
    simp only [HybridWord.Cmd.eval] at h
    cases he : e.eval i x y s ls with
    | none => simp [he] at h
    | some v => simp [he] at h; cases h; exact .refl _
  | store a j e =>
    simp only [HybridWord.Cmd.eval] at h
    cases hj : j.eval i x y s ls <;> cases he : e.eval i x y s ls <;>
      simp [hj,he] at h
    exact write_sizes h
  | letValue e b ih =>
    simp only [HybridWord.Cmd.eval] at h
    cases he : e.eval i x y s ls with
    | none => simp [he] at h
    | some v => simp only [he,bind,Option.bind] at h; exact ih h
  | seq a b ha hb =>
    simp only [HybridWord.Cmd.eval] at h
    cases he : a.eval i x y s ls with
    | none => simp [he] at h
    | some u =>
      simp only [he,bind,Option.bind] at h
      exact (ha he).trans (hb h)
  | branch e a b ha hb =>
    simp only [HybridWord.Cmd.eval] at h
    cases he : e.eval i x y s ls with
    | none => simp [he] at h
    | some v =>
      simp only [he,bind,Option.bind] at h
      split at h
      · exact ha h
      · exact hb h
  | «repeat» n b ih => exact fold_sizes _ (fun _ _ _ h => ih h) _ h
  | forRange e b ih =>
    simp only [HybridWord.Cmd.eval] at h
    cases he : e.eval i x y s ls with
    | none => simp [he] at h
    | some v =>
      simp only [he,bind,Option.bind] at h
      exact fold_sizes _ (fun _ _ _ h => ih h) _ h
  | forStatic start stop stride b ih => exact fold_sizes _ (fun _ _ _ h => ih h) _ h
  | copy dst src n => exact copy_sizes h

end IRComparison.FixedMemory
