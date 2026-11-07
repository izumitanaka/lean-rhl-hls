import PaperCore.Evaluator

namespace PaperCore.CorrespondenceAudit

/-- The array-content premises printed in correctness-journal.tex: every
    index in I has a defined source value, and that value equals S at the
    same position. This does NOT add a stream-length equality. We isolate
    one array; unrelated arrays and ordinary registers can be unchanged. -/
def PrintedContents (heap : List (Int × Int)) (indices values : List Int) : Prop :=
  ∀ i : Fin indices.length,
    (heap.lookup indices[i]).isSome = true ∧
    heap.lookup indices[i] = values[i.val]?

instance (heap : List (Int × Int)) (indices values : List Int) :
    Decidable (PrintedContents heap indices values) := inferInstanceAs (Decidable (∀ i : Fin indices.length, _))

def heap : List (Int × Int) := [(0,10),(1,20)]

/-- All printed content premises hold despite the unrepresented suffix 99. -/
theorem before_write : PrintedContents heap [0] [10,99] := by decide

/-- Tr-InsWBuf's new index is fresh and its source value equals buffer b=20. -/
theorem write_preconditions :
    ([0] : List Int).Nodup ∧ (1 : Int) ∉ [0] ∧ heap.lookup 1 = some 20 := by decide

def before : State Streams := ⟨[("b",20)],[("a",[10,99])]⟩
def after : State Streams := ⟨[("b",20)],[("a",[10,99,20])]⟩

theorem actual_write : StreamStep (.write "a" "b") before after := by
  apply streamRun_sound
  decide

/-- Appending the fresh index as in Tr-InsWBuf no longer corresponds to
    appending the buffer value to the actual stream. -/
theorem after_write_fails : ¬ PrintedContents heap [0,1] [10,99,20] := by decide

/-- The approved equal-length condition excludes this state. The actual
    structural relation is now defined in PaperCore.Correspondence. -/
theorem equal_length_excludes_counterexample :
    ([0] : List Int).length ≠ ([10,99] : List Int).length := by decide

#print axioms before_write
#print axioms write_preconditions
#print axioms actual_write
#print axioms after_write_fails
end PaperCore.CorrespondenceAudit
