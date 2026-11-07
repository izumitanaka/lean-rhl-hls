import PaperCore.BufferMemory
import PaperCore.IndexSequence

namespace PaperCore.OrientedWindow


/-- The contiguous window represented by scalar buffer registers. -/
def Held (stride : Int) (heap : Heap) (regs : Registers) (array : Array) (first : Int) : List Var → Prop
  | [] => True
  | buffer :: rest => ∃ value, heap.lookup (array,first) = some value ∧
      regs.lookup buffer = some value ∧ Held stride heap regs array (first+stride) rest


theorem Held.congr_regs (held : Held stride heap regs array first buffers)
    (same : ∀ b ∈ buffers, other.lookup b = regs.lookup b) : Held stride heap other array first buffers := by
  induction buffers generalizing first with
  | nil => trivial
  | cons b rest ih =>
    obtain ⟨value,cell,reg,tail⟩ := held
    exact ⟨value,cell,(same b (by simp)).trans reg,
      ih tail (fun v hv => same v (List.mem_cons_of_mem _ hv))⟩

theorem Held.set_other (held : Held stride heap regs array first buffers) (other : dest ∉ buffers) :
    Held stride heap (put regs dest value) array first buffers := by
  apply held.congr_regs
  intro b member
  apply lookup_put_other
  intro same
  subst b
  exact other member


theorem Held.get {n : Nat} (held : Held stride heap regs array first buffers) (found : buffers[n]? = some buffer) :
    ∃ value, heap.lookup (array,first+(n:Int)*stride) = some value ∧ regs.lookup buffer = some value := by
  induction buffers generalizing first n with
  | nil => simp at found
  | cons b rest ih =>
    obtain ⟨value,cell,reg,heldTail⟩ := held
    cases n with
    | zero => simp at found; subst buffer; exact ⟨value,by simpa using cell,reg⟩
    | succ n =>
      have later := ih heldTail (by simpa using found)
      simpa [Int.natCast_add,Int.add_mul,Int.one_mul,Int.add_assoc,Int.add_left_comm,Int.add_comm] using later

theorem Held.of_get (all : ∀ (n : Nat) buffer, buffers[n]? = some buffer →
    ∃ value, heap.lookup (array,first+(n:Int)*stride) = some value ∧ regs.lookup buffer = some value) :
    Held stride heap regs array first buffers := by
  induction buffers generalizing first with
  | nil => trivial
  | cons b rest ih =>
    obtain ⟨value,cell,reg⟩ := all 0 b rfl
    refine ⟨value,by simpa using cell,reg,ih ?_⟩
    intro n buffer found
    have point := all (n+1) buffer (by simpa using found)
    simpa [Int.natCast_add,Int.add_mul,Int.one_mul,Int.add_assoc,Int.add_left_comm,Int.add_comm] using point

theorem Held.append : Held stride heap regs array first (left ++ right) ↔
    Held stride heap regs array first left ∧ Held stride heap regs array (first+(left.length:Int)*stride) right := by
  induction left generalizing first with
  | nil => simp [Held]
  | cons b rest ih =>
    simp only [List.cons_append,Held,List.length_cons]
    constructor
    · rintro ⟨value,cell,reg,tail⟩
      obtain ⟨headHeld,tailHeld⟩ := ih.mp tail
      exact ⟨⟨value,cell,reg,headHeld⟩,by simpa [Int.natCast_add,Int.add_mul,Int.one_mul,Int.add_assoc,Int.add_comm,Int.add_left_comm] using tailHeld⟩
    · rintro ⟨⟨value,cell,reg,headHeld⟩,tailHeld⟩
      exact ⟨value,cell,reg,ih.mpr ⟨headHeld,by simpa [Int.natCast_add,Int.add_mul,Int.one_mul,Int.add_assoc,Int.add_comm,Int.add_left_comm] using tailHeld⟩⟩


theorem entries_split (first : Int) (left right : Nat) :
    IndexSequence.entries first stride (left+right) =
      IndexSequence.entries first stride left ++ IndexSequence.entries (first+(left:Int)*stride) stride right := by
  induction left generalizing first with
  | zero => simp [IndexSequence.entries]
  | succ n ih =>
    simp only [Nat.succ_add,IndexSequence.entries,List.cons_append]
    rw [ih]
    congr 2
    congr 1
    simp [Int.natCast_add, Int.add_mul, Int.add_assoc, Int.add_comm, Int.add_left_comm, Int.one_mul]


/-- Buffers are numbered in FIFO order, independently of the source access order. -/
structure Layout where
  array : Array
  first : Int
  scale : Int
  reverse : Bool
  buffers : List Var

def direction (reverse : Bool) : Int := if reverse then -1 else 1

def Layout.stride (l : Layout) : Int := direction l.reverse

def Layout.offset (l : Layout) (offset : Int) : Int :=
  if l.reverse then l.first-offset else offset-l.first

def Layout.slots (l : Layout) : BufferView.Slots := fun array index =>
  if array = l.array ∧ index.scale = l.scale ∧ 0 ≤ l.offset index.offset then
    l.buffers[(l.offset index.offset).toNat]?
  else none

theorem Layout.fresh (l : Layout) (fresh : ∀ b ∈ l.buffers, ¬ ordinary b) :
    BufferView.Fresh l.slots ordinary := by
  intro array index buffer found
  unfold Layout.slots at found
  split at found
  · exact fresh buffer (List.mem_of_getElem? found)
  · simp at found

theorem Layout.slots_for (l : Layout) : BufferMemory.SlotsFor l.slots l.array := by
  intro array index buffer found
  unfold Layout.slots at found
  split at found
  · rename_i h; exact h.1
  · simp at found

theorem Layout.view (l : Layout)
    (held : Held l.stride heap regs l.array (l.scale*counter+l.first) l.buffers) :
    BufferView.View l.slots counter heap regs := by
  intro array index buffer found
  unfold Layout.slots at found
  split at found
  · rename_i h
    obtain ⟨rfl,scale,nonneg⟩ := h
    have point := held.get found
    have address : l.scale*counter+l.first +
        ((l.offset index.offset).toNat:Int)*l.stride =
        index.eval counter := by
      cases rev : l.reverse <;>
        simp [Layout.offset,Layout.stride,direction,rev,AccessAnalysis.Affine.eval,scale] at * <;> omega
    simpa only [address] using point
  · simp at found

theorem Layout.held (l : Layout) (view : BufferView.View l.slots counter heap regs) :
    Held l.stride heap regs l.array (l.scale*counter+l.first) l.buffers := by
  apply Held.of_get
  intro n buffer found
  have slot : l.slots l.array ⟨l.scale,l.first+(n:Int)*l.stride⟩ = some buffer := by
    have offset : l.offset (l.first+(n:Int)*l.stride) = (n:Int) := by
      cases rev : l.reverse <;> simp [Layout.offset,Layout.stride,direction,rev] <;> omega
    simpa [Layout.slots,offset] using found
  have point := view l.array ⟨l.scale,l.first+(n:Int)*l.stride⟩ buffer slot
  simpa [AccessAnalysis.Affine.eval,Int.add_assoc] using point

end PaperCore.OrientedWindow
