import PaperCore.AccessAnalysis

namespace PaperCore.MemoryCoverage
open AccessAnalysis

/-- Definedness, not equality of values: overwriting a cell preserves this fact. -/
def Defined (heap : Heap) (array : Array) (index : Int) : Prop :=
  ∃ value, heap.lookup (array,index) = some value

theorem put_preserves (defined : Defined heap array index) :
    Defined (put heap (other,address) value) array index := by
  by_cases same : (array,index) = (other,address)
  · exact ⟨value,by rw [same,lookup_put_same]⟩
  · simpa [Defined,lookup_put_other _ _ _ _ same] using defined

theorem execution_preserves (run : SourceExec meaning code initial final)
    (defined : Defined initial.memory array index) : Defined final.memory array index := by
  induction run with
  | action step =>
    cases step with
    | read index cell => exact defined
    | write index value => exact put_preserves defined
  | assign value => exact defined
  | seq first second ihFirst ihSecond => exact ihSecond (ihFirst defined)
  | ifTrue condition nonzero body ih => exact ih defined
  | ifFalse condition body ih => exact ih defined
  | forExit value => exact defined
  | forLoop value nonzero body counter rest ihBody ihRest => exact ihRest (ihBody defined)
  | kernel body ih => exact ih defined

/-- A completed traced access establishes definedness, even if its value is
subsequently overwritten. This supports producer-derived prefetch coverage. -/
theorem trace_exec (trace : AccessTrace meaning code initial final events) :
    SourceExec meaning code initial final := by
  induction trace with
  | assign run => exact run
  | read run index => exact .action run
  | write run index => exact .action run
  | seq left right ihLeft ihRight => exact .seq ihLeft ihRight
  | branchTrue condition nonzero body ih => exact .ifTrue condition nonzero ih
  | branchFalse condition body ih => exact .ifFalse condition ih

theorem trace_defines (trace : AccessTrace meaning code initial final events)
    (member : event ∈ events) : Defined final.memory event.array event.index := by
  induction trace with
  | assign run => simp at member
  | read run index =>
    simp only [List.mem_singleton] at member
    subst event
    cases run with
    | read actual cell =>
      have same := Option.some.inj (actual.symm.trans index)
      subst_vars
      exact ⟨_,cell⟩
  | write run index =>
    simp only [List.mem_singleton] at member
    subst event
    cases run with
    | write actual value =>
      have same := Option.some.inj (actual.symm.trans index)
      subst_vars
      exact ⟨_,lookup_put_same ..⟩
  | seq left right ihLeft ihRight =>
    rcases List.mem_append.mp member with hl | hr
    · exact execution_preserves (trace_exec right) (ihLeft hl)
    · exact ihRight hr
  | branchTrue condition nonzero body ih => exact ih member
  | branchFalse condition body ih => exact ih member

/-- Continuous windows require every cell, including holes between accesses.
This is a verification condition for insertion, never an input-language restriction. -/
def Covers (heap : Heap) (array : Array) (first stride : Int) (count : Nat) : Prop :=
  ∀ n : Nat, n < count → Defined heap array (first + (n:Int)*stride)

theorem covers_preserved (run : SourceExec meaning code initial final)
    (coverage : Covers initial.memory array first stride count) :
    Covers final.memory array first stride count :=
  fun n hn => execution_preserves run (coverage n hn)

theorem Covers.subrange (coverage : Covers heap array first stride count)
    (fits : offset+length ≤ count) :
    Covers heap array (first+(offset:Int)*stride) stride length := by
  intro n hn
  have cell := coverage (offset+n) (by omega)
  simpa [Int.natCast_add,Int.add_mul,Int.add_assoc] using cell

#print axioms execution_preserves
#print axioms trace_defines
end PaperCore.MemoryCoverage
