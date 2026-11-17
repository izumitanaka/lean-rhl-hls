import Std

namespace IRComparison.Circuit

/-- A fixed number of physical cells and an occupancy counter. The suffix
outside `used` is unobservable, so dequeue need not clear unused cells. -/
structure FIFO (α : Type) (capacity : Nat) where
  cells : List α
  size : cells.length = capacity
  used : Nat
  bounded : used ≤ capacity

def FIFO.contents (q : FIFO α n) := q.cells.take q.used

def FIFO.empty (capacity : Nat) (fill : α) : FIFO α capacity :=
  ⟨List.replicate capacity fill,by simp,0,by omega⟩

def FIFO.push (q : FIFO α n) (v : α) : Option (FIFO α n) :=
  if h : q.used < n then
    some ⟨q.cells.set q.used v,by simpa using q.size,q.used+1,by omega⟩
  else none

def FIFO.pop (q : FIFO α n) (fill : α) : Option (α × FIFO α n) :=
  match he : q.cells with
  | [] => none
  | v::vs =>
    if h : 0 < q.used then
      some (v,⟨vs++[fill],by have := q.size; simp [he] at *; omega,q.used-1,by have := q.bounded; omega⟩)
    else none

theorem take_set_append (cells : List α) (n : Nat) (h : n < cells.length) :
    (cells.set n v).take (n+1) = cells.take n ++ [v] := by
  induction n generalizing cells with
  | zero => cases cells <;> simp_all
  | succ n ih =>
      cases cells with
      | nil => simp at h
      | cons x xs => simpa using ih xs (by simpa using h)

theorem FIFO.push_correct (q : FIFO α n) (h : q.used < n) :
    (q.push v).map FIFO.contents = some (q.contents ++ [v]) := by
  simp only [push,h,↓reduceDIte,Option.map_some,contents]
  congr 1
  exact take_set_append q.cells q.used (by rw [q.size]; exact h)

theorem FIFO.full (q : FIFO α n) (h : q.used = n) : q.push v = none := by
  simp [push,h]

theorem FIFO.pop_correct (q : FIFO α n) (fill : α) :
    (q.pop fill).map (fun (v,t) => (v,t.contents)) =
      match q.contents with
      | [] => none
      | v::vs => some (v,vs) := by
  rcases q with ⟨cells,sz,used,bounded⟩
  cases cells with
  | nil => simp [pop,contents]
  | cons x xs =>
    cases used with
    | zero => simp [pop,contents]
    | succ k =>
      have hk : k ≤ xs.length := by simp at sz; omega
      simp [pop,contents,List.take_append_of_le_length hk]

theorem FIFO.contents_length (q : FIFO α n) : q.contents.length = q.used := by
  simp [contents,q.size,Nat.min_eq_left q.bounded]

theorem FIFO.occupancy_fits (q : FIFO α n) (w : Nat) (h : n < 2^w) :
    (BitVec.ofNat w q.used).toNat = q.used := by
  simp [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt q.bounded h)]

end IRComparison.Circuit
