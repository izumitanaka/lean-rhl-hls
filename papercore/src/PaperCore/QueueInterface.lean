import PaperCore.SequenceTransitions
import PaperCore.Rules

namespace PaperCore.QueueInterface
open IndexSequence

abbrev Queues := Array → Values

def Holds (arrays : List Array) (queues : Queues) : Assertion :=
  fun _ _ indices => ∀ a ∈ arrays, indices.lookup a = some (queues a).sequence

/-- Compare represented sequences, not their parameter tuples. This does not
    enumerate cells and does not fix empty/singleton parameter freedom. -/
def sameValues (left right : Values) : Bool := decide (
  left.count.toNat = right.count.toNat ∧
  (left.count.toNat = 0 ∨ left.first = right.first) ∧
  (left.count.toNat ≤ 1 ∨ left.step = right.step))

theorem sameValues_correct : sameValues left right = true ↔ left.sequence = right.sequence := by
  simp only [sameValues,decide_eq_true_eq,Values.sequence]
  exact (eq_entries_iff ..).symm

def equal (arrays : List Array) (left right : Queues) : Bool :=
  arrays.all (fun a => sameValues (left a) (right a))

theorem equal_correct : equal arrays left right = true ↔
    ∀ a ∈ arrays, (left a).sequence = (right a).sequence := by
  simp only [equal,List.all_eq_true,sameValues_correct]

theorem holds_transfer (same : equal arrays left right = true)
    (holds : Holds arrays left regs heap indices) : Holds arrays right regs heap indices := by
  intro a member
  exact (holds a member).trans (congrArg some (equal_correct.mp same a member))

def empty : Queues := fun _ => ⟨0,1,0⟩

def drop (v : Values) (n : Nat) : Values :=
  ⟨v.first+(n:Int)*v.step,v.step,((v.count.toNat-n:Nat):Int)⟩

theorem entries_drop (first step : Int) (count n : Nat) :
    (entries first step count).drop n = entries (first+(n:Int)*step) step (count-n) := by
  induction n generalizing first count with
  | zero => simp [entries]
  | succ n ih =>
    cases count with
    | zero => simp [entries]
    | succ count => simpa [entries,Int.add_mul,Int.add_assoc,Int.add_comm,Int.add_left_comm] using ih (first+step) count

theorem drop_sequence : (drop v n).sequence = v.sequence.drop n := by
  simp [drop,Values.sequence,entries_drop]


end PaperCore.QueueInterface
