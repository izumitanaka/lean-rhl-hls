import PaperCore.IndexSequenceSMT
import PaperCore.SMT.VCLogic

namespace PaperCore.IndexSequence
open PaperCore (SMT)
open PaperCore.SMTMeaning (eval conj_member)

structure Template where
  first : SMT
  step : SMT
  count : SMT

structure Values where
  first : Int
  step : Int
  count : Int

def Values.sequence (v : Values) : List Int := entries v.first v.step v.count.toNat

structure Template.Evaluates (t : Template) (v : Values)
    (zero : PaperCore.SMTMeaning.ZeroDivision) (params vars : String → Int) : Prop where
  first : eval zero params vars t.first = .integer v.first
  step : eval zero params vars t.step = .integer v.step
  count : eval zero params vars t.count = .integer v.count

/-- Pop one index; retain the exact freedom of the after-sequence's
    representation instead of fixing its step when empty or singleton. -/
def popConstraint (before after : Template) (address : SMT) : SMT :=
  SMT.conj [SMT.lt (.num 0) before.count, SMT.eq address before.first,
    equality (SMT.add before.first before.step) before.step (SMT.sub before.count (.num 1))
      after.first after.step after.count]

theorem popConstraint_sound (hb : before.Evaluates b zero params vars)
    (ha : after.Evaluates a zero params vars)
    (hx : eval zero params vars address = .integer x)
    (model : eval zero params vars (popConstraint before after address) = .boolean true) :
    0 < b.count ∧ 0 ≤ a.count ∧ b.sequence = x :: a.sequence := by
  have part := fun q hq => conj_member _ q zero params vars model hq
  have positive := part (SMT.lt (.num 0) before.count) (by simp [popConstraint])
  have head := part (SMT.eq address before.first) (by simp [popConstraint])
  have tail := part (equality (SMT.add before.first before.step) before.step
    (SMT.sub before.count (.num 1)) after.first after.step after.count) (by simp [popConstraint])
  have firstEval : eval zero params vars (SMT.add before.first before.step) = .integer (b.first+b.step) := by
    simp [SMT.add, SMT.op, eval, hb.first, hb.step, PaperCore.SMTMeaning.operation]
  have countEval : eval zero params vars (SMT.sub before.count (.num 1)) = .integer (b.count-1) := by
    simp [SMT.sub, SMT.op, eval, hb.count, PaperCore.SMTMeaning.operation]
  have eqs := (equality_correct firstEval hb.step countEval ha.first ha.step ha.count).mp tail
  have pos : 0 < b.count := by
    simpa [SMT.lt, SMT.op, eval, hb.count, PaperCore.SMTMeaning.operation] using positive
  have eqHead : x = b.first := by
    simpa [SMT.eq, SMT.op, eval, hx, hb.first, PaperCore.SMTMeaning.operation] using head
  refine ⟨pos,eqs.2.1,?_⟩
  apply (cons_eq_iff _ _ _ _ _ _ _).mpr
  refine ⟨by omega,eqHead,?_⟩
  have counts : b.count.toNat - 1 = (b.count-1).toNat := by omega
  rw [counts]
  exact eqs.2.2

/-- Append one index. Matching the old prefix against the new progression
    allows the first appended element to determine a previously irrelevant
    step. Freshness is deliberately a separate RHL obligation. -/
def pushConstraint (before after : Template) (address : SMT) : SMT :=
  SMT.conj [equality before.first before.step before.count after.first after.step before.count,
    SMT.eq after.count (SMT.add before.count (.num 1)),
    SMT.eq address (SMT.add after.first (SMT.mul before.count after.step))]

theorem pushConstraint_sound (hb : before.Evaluates b zero params vars)
    (ha : after.Evaluates a zero params vars)
    (hx : eval zero params vars address = .integer x)
    (model : eval zero params vars (pushConstraint before after address) = .boolean true) :
    0 ≤ b.count ∧ 0 ≤ a.count ∧ b.sequence ++ [x] = a.sequence := by
  have part := fun q hq => conj_member _ q zero params vars model hq
  have same := part (equality before.first before.step before.count after.first after.step before.count)
    (by simp [pushConstraint])
  have count := part (SMT.eq after.count (SMT.add before.count (.num 1))) (by simp [pushConstraint])
  have last := part (SMT.eq address (SMT.add after.first (SMT.mul before.count after.step)))
    (by simp [pushConstraint])
  have eqs := (equality_correct hb.first hb.step hb.count ha.first ha.step hb.count).mp same
  have counts : a.count = b.count + 1 := by
    simpa [SMT.eq, SMT.add, SMT.op, eval, hb.count, ha.count, PaperCore.SMTMeaning.operation] using count
  have lastValue : x = a.first + b.count * a.step := by
    simpa [SMT.eq, SMT.add, SMT.mul, SMT.op, eval, hx, ha.first, hb.count, ha.step,
      PaperCore.SMTMeaning.operation] using last
  refine ⟨eqs.1,by omega,?_⟩
  apply (snoc_eq_iff _ _ _ _ _ _ _).mpr
  exact ⟨by omega,eqs.2.2,by simpa [Int.toNat_of_nonneg eqs.1] using lastValue⟩

def distinctConstraint (t : Template) : SMT :=
  SMT.disj [SMT.le t.count (.num 1), SMT.neg (SMT.eq t.step (.num 0))]

theorem distinctConstraint_sound (ha : after.Evaluates a zero params vars)
    (model : eval zero params vars (distinctConstraint after) = .boolean true) :
    a.sequence.Nodup := by
  have condition : a.count ≤ 1 ∨ a.step ≠ 0 := by
    simpa [distinctConstraint, SMT.disj, SMT.le, SMT.neg, SMT.eq, SMT.op, eval,
      ha.count, ha.step, PaperCore.SMTMeaning.operation, PaperCore.SMTMeaning.booleans] using model
  apply (nodup_entries_iff _ _ _).mpr
  rcases condition with small | nonzero
  · left; omega
  · exact Or.inr nonzero

/-- Freshness is enforced by the exact no-duplicates criterion for the
    resulting progression, not by requiring a positive or fixed step. -/
def safePushConstraint (before after : Template) (address : SMT) : SMT :=
  SMT.conj [pushConstraint before after address, distinctConstraint after]

theorem safePushConstraint_sound (hb : before.Evaluates b zero params vars)
    (ha : after.Evaluates a zero params vars)
    (hx : eval zero params vars address = .integer x)
    (model : eval zero params vars (safePushConstraint before after address) = .boolean true) :
    0 ≤ b.count ∧ 0 ≤ a.count ∧ b.sequence ++ [x] = a.sequence ∧ x ∉ b.sequence := by
  have push := conj_member _ (pushConstraint before after address) zero params vars model (by simp [safePushConstraint])
  have distinct := conj_member _ (distinctConstraint after) zero params vars model (by simp [safePushConstraint])
  obtain ⟨bn,an,same⟩ := pushConstraint_sound hb ha hx push
  have nodup := distinctConstraint_sound ha distinct
  rw [← same] at nodup
  refine ⟨bn,an,same,?_⟩
  intro member
  exact (List.nodup_append.mp nodup).2.2 x member x (by simp) rfl

/-- Link the computed sequence transition to the actual FIFO read and the
    full source/target state relation. Cell existence follows from that
    relation, not from an assumed total memory. -/
theorem pop_corresponds {a b : Values} (corr : Corresponds ordinary arrays source target indices)
    (tracked : arrays array) (buffer : ¬ ordinary dest)
    (witness : indices.lookup array = some b.sequence)
    (transition : b.sequence = x :: a.sequence) :
    ∃ value target', source.memory.lookup (array,x) = some value ∧
      StreamStep (.read dest array) target target' ∧
      target'.regs = put target.regs dest value ∧
      Corresponds ordinary arrays source target' (put indices array a.sequence) := by
  apply corr.read_buffer tracked buffer
  simpa [transition] using witness

theorem push_corresponds {a b : Values} (corr : Corresponds ordinary arrays source target indices)
    (tracked : arrays array) (witness : indices.lookup array = some b.sequence)
    (transition : b.sequence ++ [x] = a.sequence)
    (fresh : x ∉ b.sequence) (cell : source.memory.lookup (array,x) = some value)
    (held : target.regs.lookup dest = some value) :
    ∃ target', StreamStep (.write array dest) target target' ∧ target'.regs = target.regs ∧
      Corresponds ordinary arrays source target' (put indices array a.sequence) := by
  simpa [transition] using corr.write_buffer tracked witness fresh cell held

#print axioms popConstraint_sound
#print axioms pushConstraint_sound
#print axioms pop_corresponds
#print axioms push_corresponds
end PaperCore.IndexSequence
