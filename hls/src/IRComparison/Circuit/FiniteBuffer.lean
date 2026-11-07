import IRComparison.Circuit.BitMachine
import IRComparison.Circuit.FIFO

namespace IRComparison.Circuit

/-- Fixed physical cells with a bounded live prefix. Unused cells have no
semantic value; arrays and queues share this storage representation. -/
structure WordBuffer (capacity : Nat) where
  cells : Fin capacity → BitVec 32
  used : Fin (capacity+1)

def WordBuffer.contents (b : WordBuffer capacity) : Array Int :=
  Array.ofFn fun i : Fin b.used.val => (b.cells ⟨i.val,by have := i.isLt; have := b.used.isLt; omega⟩).toNat

def WordBuffer.pack (capacity : Nat) (xs : Array Int) : WordBuffer capacity where
  cells := fun i => BitVec.ofInt 32 (xs[i.val]?.getD 0)
  used := ⟨min xs.size capacity,by omega⟩

/-- Change only cells outside the live prefix. These words remain fixed
until overwritten; they are not fresh choices at each read. -/
def WordBuffer.withUnused (b : WordBuffer capacity) (values : Fin capacity → BitVec 32) : WordBuffer capacity :=
  { b with cells := fun i => if i.val < b.used.val then b.cells i else values i }

theorem WordBuffer.withUnused_contents (b : WordBuffer capacity) (values : Fin capacity → BitVec 32) :
    (b.withUnused values).contents = b.contents := by
  apply Array.ext
  · simp [contents,withUnused]
  · intro i hi hj
    simp [contents,withUnused]

theorem word_roundtrip (h : wordRange.Contains v) : (BitVec.ofInt 32 v).toNat = v := by
  simp only [wordRange,Interval.Contains] at h
  have hh : 0 ≤ v ∧ v < (2:Int)^32 := by change 0 ≤ v ∧ v < 4294967296; omega
  simp only [BitVec.toNat_ofInt]
  change ((v % (2:Int)^32).toNat : Int) = v
  have hm : v % (2:Int)^32 = v := Int.emod_eq_of_lt hh.1 hh.2
  rw [hm,Int.toNat_of_nonneg h.1]

theorem WordBuffer.pack_correct (capacity : Nat) (xs : Array Int) (fits : xs.size ≤ capacity)
    (words : ∀ (n : Nat) (v : Int), xs[n]? = some v → wordRange.Contains v) :
    (pack capacity xs).contents = xs := by
  apply Array.ext
  · simp [contents,pack,Nat.min_eq_left fits]
  · intro i hi hj
    simp only [contents,Array.getElem_ofFn,pack]
    have hget : xs[i]? = some xs[i] := Array.getElem?_eq_getElem hj
    rw [hget,Option.getD_some]
    exact word_roundtrip (words i xs[i] hget)

theorem WordBuffer.contents_size (b : WordBuffer capacity) : b.contents.size ≤ capacity := by
  simp only [contents,Array.size_ofFn]
  exact Nat.le_of_lt_succ b.used.isLt

end IRComparison.Circuit
