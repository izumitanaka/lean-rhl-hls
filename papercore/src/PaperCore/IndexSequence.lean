import PaperCore.Correspondence

namespace PaperCore.IndexSequence

/-- Internal finite arithmetic sequence representation for the automation
    templates in auto.tex. Signed step is unrestricted here; zero step is
    also represented (and may fail the separate no-duplicates obligation).
    Count describes a witness sequence, not a source loop restriction. -/
def entries (first step : Int) : Nat → List Int
  | 0 => []
  | n + 1 => first :: entries (first + step) step n

@[simp] theorem length_entries (first step : Int) (count : Nat) :
    (entries first step count).length = count := by
  induction count generalizing first with
  | zero => rfl
  | succ n ih => simp [entries, ih]

theorem mem_entries (first step value : Int) (count : Nat) :
    value ∈ entries first step count ↔
      ∃ k : Nat, k < count ∧ value = first + (k : Int) * step := by
  induction count generalizing first with
  | zero => simp [entries]
  | succ n ih =>
    simp only [entries, List.mem_cons, ih]
    constructor
    · intro present
      rcases present with eq | ⟨k,lt,eq⟩
      · exact ⟨0,by omega,by simpa using eq⟩
      · refine ⟨k+1,by omega,?_⟩
        simp only [Int.natCast_add, Int.natCast_succ, Int.ofNat_one, Int.add_mul, Int.one_mul]
        omega
    · rintro ⟨k,lt,eq⟩
      cases k with
      | zero => left; simpa using eq
      | succ k =>
        right
        refine ⟨k,by omega,?_⟩
        simp only [Int.natCast_add, Int.natCast_succ, Int.ofNat_one, Int.add_mul, Int.one_mul] at eq
        omega

/-- The integer encoding includes a bounded position, so it preserves empty
    sequences, order direction, and gaps without assuming a positive step. -/
theorem mem_entries_integer (first step value : Int) (count : Nat) :
    value ∈ entries first step count ↔
      ∃ k : Int, 0 ≤ k ∧ k < (count : Int) ∧ value = first + k * step := by
  rw [mem_entries]
  constructor
  · rintro ⟨k,lt,eq⟩
    exact ⟨k,by omega,by omega,eq⟩
  · rintro ⟨k,nonneg,lt,eq⟩
    refine ⟨k.toNat,by omega,?_⟩
    simpa [Int.toNat_of_nonneg nonneg] using eq

@[simp] theorem head_entries (first step : Int) (n : Nat) :
    (entries first step (n+1)).head? = some first := rfl

/-- No arbitrary canonical representation: for empty sequences neither
    first nor step matters; for singleton sequences step does not matter. -/
theorem eq_entries_iff (first step otherFirst otherStep : Int) (count otherCount : Nat) :
    entries first step count = entries otherFirst otherStep otherCount ↔
      count = otherCount ∧ (count = 0 ∨ first = otherFirst) ∧
        (count ≤ 1 ∨ step = otherStep) := by
  constructor
  · intro same
    have lengths := congrArg List.length same
    simp only [length_entries] at lengths
    subst otherCount
    refine ⟨rfl,?_⟩
    cases count with
    | zero => simp
    | succ n =>
      have heads := (List.cons.inj same).1
      refine ⟨Or.inr heads,?_⟩
      cases n with
      | zero => exact Or.inl (by omega)
      | succ n =>
        have nextHeads := (List.cons.inj (List.cons.inj same).2).1
        right
        change first + step = otherFirst + otherStep at nextHeads
        omega
  · rintro ⟨lengths,heads,steps⟩
    subst otherCount
    cases count with
    | zero => rfl
    | succ n =>
      have sameFirst : first = otherFirst := heads.resolve_left (by omega)
      subst otherFirst
      cases n with
      | zero => rfl
      | succ n =>
        have sameStep : step = otherStep := steps.resolve_left (by omega)
        subst otherStep
        rfl

theorem append_entries (first step : Int) (count : Nat) :
    entries first step (count+1) = entries first step count ++ [first + (count : Int) * step] := by
  induction count generalizing first with
  | zero => simp [entries]
  | succ n ih =>
    change first :: entries (first + step) step (n+1) =
      first :: (entries (first + step) step n ++ [first + ((n+1 : Nat) : Int) * step])
    rw [ih]
    have last : first + step + (n : Int) * step = first + ((n+1 : Nat) : Int) * step := by
      simp only [Int.natCast_add, Int.ofNat_one, Int.add_mul, Int.one_mul]
      omega
    rw [last]

/-- Exact append characterization; the after-state may choose a different
    representation when the old sequence is empty or a singleton. -/
theorem snoc_eq_iff (f s g t value : Int) (n m : Nat) :
    entries f s n ++ [value] = entries g t m ↔
      m = n+1 ∧ entries f s n = entries g t n ∧ value = g + (n : Int) * t := by
  constructor
  · intro same
    have lengths := congrArg List.length same
    simp only [List.length_append, length_entries, List.length_singleton] at lengths
    have count : m = n+1 := lengths.symm
    subst m
    rw [append_entries] at same
    obtain ⟨left,right⟩ := List.append_inj' same rfl
    exact ⟨rfl,left,by simpa using right⟩
  · rintro ⟨rfl,left,rfl⟩
    rw [left, ← append_entries]

theorem cons_eq_iff (f s g t value : Int) (n m : Nat) :
    entries f s n = value :: entries g t m ↔
      0 < n ∧ value = f ∧ entries (f+s) s (n-1) = entries g t m := by
  cases n with
  | zero => simp [entries]
  | succ n => simp [entries, eq_comm]

theorem map_add_entries (first step offset : Int) (count : Nat) :
    (entries first step count).map (fun x => x + offset) = entries (first+offset) step count := by
  induction count generalizing first with
  | zero => rfl
  | succ n ih =>
    simp only [entries, List.map_cons, ih]
    congr 2
    omega

theorem nodup_entries_iff (first step : Int) (count : Nat) :
    (entries first step count).Nodup ↔ count ≤ 1 ∨ step ≠ 0 := by
  constructor
  · intro distinct
    by_cases small : count ≤ 1
    · exact Or.inl small
    · right
      intro zero
      subst step
      cases count with
      | zero => omega
      | succ n =>
        cases n with
        | zero => omega
        | succ n => simp [entries] at distinct
  · intro condition
    rcases condition with small | nonzero
    · cases count with
      | zero => simp [entries]
      | succ n =>
        have : n = 0 := by omega
        subst n
        simp [entries]
    · induction count generalizing first with
      | zero => simp [entries]
      | succ n ih =>
        apply List.nodup_cons.mpr
        refine ⟨?_,ih (first+step)⟩
        intro member
        obtain ⟨k,lt,eq⟩ := (mem_entries (first+step) step first n).mp member
        have product : ((k : Int)+1)*step = 0 := by
          rw [Int.add_mul, Int.one_mul]
          omega
        rcases Int.mul_eq_zero.mp product with bad | bad
        · omega
        · exact nonzero bad

example : entries 0 2 4 = [0,2,4,6] := rfl
example : entries 6 (-2) 4 = [6,4,2,0] := rfl
example : entries 6 (-2) 0 = [] := rfl
example : entries 6 0 3 = [6,6,6] := rfl

#print axioms mem_entries_integer
#print axioms eq_entries_iff
#print axioms append_entries
end PaperCore.IndexSequence
