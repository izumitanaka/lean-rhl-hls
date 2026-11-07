import IRComparison.Circuit.RTL.LowerSound

namespace IRComparison.Circuit.RTL

/-- Nonblocking fixed-range cell assignments: every RHS is supplied from the
pre-clock bank, while pending destination cells are updated independently. -/
def writeRange (n : Nat) (source pending : Nat → α) : Nat → α :=
  (List.range n).foldl (fun acc i => fun k => if k = i then source i else acc k) pending

theorem writeRange_correct (n : Nat) (source pending : Nat → α) (k : Nat) :
    writeRange n source pending k = if k < n then source k else pending k := by
  induction n with
  | zero => simp [writeRange]
  | succ n ih =>
    simp only [writeRange,List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]
    change (if k = n then source n else writeRange n source pending k) = _
    rw [ih]
    by_cases eq : k = n
    · subst k; simp
    · by_cases lt : k < n
      · simp [eq,lt,show k < n+1 by omega]
      · simp [eq,lt,show ¬k < n+1 by omega]

structure Bank (α : Type) where
  cells : Nat → α
  used : Nat

def Bank.contents (b : Bank α) : List α := List.ofFn fun i : Fin b.used => b.cells i.val
def Bank.clear (b : Bank α) : Bank α := {b with used := 0}
def Bank.copy (capacity : Nat) (source destination : Bank α) : Bank α :=
  ⟨writeRange capacity source.cells destination.cells,source.used⟩
def Bank.push (b : Bank α) (value : α) : Bank α :=
  ⟨fun k => if k = b.used then value else b.cells k,b.used+1⟩
def Bank.store (b : Bank α) (index : Nat) (value : α) : Bank α :=
  ⟨fun k => if k = index then value else b.cells k,b.used⟩
def Bank.shift (capacity : Nat) (b : Bank α) : Bank α :=
  ⟨writeRange (capacity-1) (fun k => b.cells (k+1)) b.cells,b.used-1⟩

theorem Bank.clear_correct (b : Bank α) : b.clear.contents = [] := rfl

theorem Bank.copy_correct (source destination : Bank α) (fits : source.used ≤ capacity) :
    (Bank.copy capacity source destination).contents = source.contents := by
  unfold copy contents
  congr 1
  funext i
  exact (writeRange_correct _ _ _ i.val).trans (if_pos (by have hi : i.val < source.used := i.isLt; omega))

theorem Bank.push_correct (b : Bank α) (value : α) : (b.push value).contents = b.contents ++ [value] := by
  simp only [push,contents,List.ofFn_succ_last]
  congr 1
  · congr 1
    funext i
    have ne : i.val ≠ b.used := by have := i.isLt; omega
    simp [ne]
  · simp

theorem Bank.store_correct (b : Bank α) (index : Nat) (value : α) :
    (b.store index value).contents = b.contents.set index value := by
  apply List.ext_getElem
  · simp [contents,store]
  · intro i hi hj
    simp only [contents,store,List.getElem_ofFn,List.getElem_set]
    by_cases he : i = index
    · subst i; simp
    · simp [he,Ne.symm he]

theorem Bank.head_correct (b : Bank α) (fill : α) (nonempty : 0 < b.used) :
    b.contents.headD fill = b.cells 0 := by
  rcases b with ⟨cells,used⟩
  cases used with
  | zero => contradiction
  | succ n => simp [contents,List.ofFn_succ]

/-- The emitted loop leaves the final unused cell unchanged. The theorem
does not assume that unused physical FIFO cells contain zero. -/
theorem Bank.shift_correct (b : Bank α) (fits : b.used ≤ capacity) :
    (b.shift capacity).contents = b.contents.tail := by
  rcases b with ⟨cells,used⟩
  cases used with
  | zero => rfl
  | succ n =>
    simp only [shift,contents,Nat.add_sub_cancel,List.ofFn_succ,List.tail_cons]
    congr 1
    funext i
    have inside : i.val < capacity-1 := by have := i.isLt; dsimp at fits; omega
    simp only [writeRange_correct,inside,↓reduceIte,Fin.val_succ]

theorem Bank.length_fits (b : Bank α) (fits : b.used ≤ capacity) :
    (BitVec.ofNat (bits capacity) b.used).toNat = b.used := by
  have room := bits_fits capacity
  simp only [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by omega)

end IRComparison.Circuit.RTL
