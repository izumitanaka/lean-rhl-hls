import IRComparison.Hybrid.HybridWindowRead
import IRComparison.Hybrid.HybridSource

namespace IRComparison.HybridWindowBody
open WindowSchedule HybridIR

structure Compiled (i : Int) (array depth : Nat) (keys : List Int) (source : MemoryCmd) where
  code : MemoryCmd
  frame : ∀ x y s locals out, source.eval i x y s locals = some out → out.arrays array = s.arrays array
  correct : ∀ (data : Array Int) (values locals : List Int) (s : State) (x y : Int),
    s.arrays array = data → Matches (arrayInput data) keys values → locals.length = depth →
    code.eval i x y s (locals++values) = source.eval i x y s locals

theorem write_other {s out : State} (different : a ≠ array) (h : s.write a j v = some out) : out.arrays array = s.arrays array := by
  unfold State.write at h
  split at h
  · simp at h
  · split at h
    · simp at h; subst out; simp [Ne.symm different]
    · simp at h

def compile (i : Int) (array depth : Nat) (keys : List Int) :
    (source : MemoryCmd) → Option (Compiled i array depth keys source)
  | .skip => some ⟨.skip,by intros; simp_all [MemoryCmd.eval],by intros; rfl⟩
  | .assign r e => do
      let c ← HybridWindowRead.compileRoot i array depth keys e
      return ⟨.assign r c.code,by
        intro x y s ls out h
        cases he : e.eval i x y s ls [] <;> simp [MemoryCmd.eval,he] at h
        subst out; rfl,by
        intro data values locals s x y frozen held len
        simp only [MemoryCmd.eval,c.correct data values locals s x y frozen held len]⟩
  | .store a j e =>
      if different : a ≠ array then do
        let cj ← HybridWindowRead.compileRoot i array depth keys j
        let ce ← HybridWindowRead.compileRoot i array depth keys e
        return ⟨.store a cj.code ce.code,by
          intro x y s ls out h
          cases hj : j.eval i x y s ls [] <;> simp [MemoryCmd.eval,hj] at h
          cases he : e.eval i x y s ls [] <;> simp [he] at h
          exact write_other different h,by
          intro data values locals s x y frozen held len
          simp only [MemoryCmd.eval,cj.correct data values locals s x y frozen held len,ce.correct data values locals s x y frozen held len]⟩
      else none
  | .letValue e b => do
      let ce ← HybridWindowRead.compileRoot i array depth keys e
      let cb ← compile i array (depth+1) keys b
      return ⟨.letValue ce.code cb.code,by
        intro x y s ls out h
        cases he : e.eval i x y s ls [] <;> simp [MemoryCmd.eval,he] at h
        exact cb.frame _ _ _ _ _ h,by
        intro data values locals s x y frozen held len
        simp only [MemoryCmd.eval,ce.correct data values locals s x y frozen held len]
        cases he : e.eval i x y s locals [] with
        | none => rfl
        | some value =>
          simpa only [bind,Option.bind,List.cons_append] using
            cb.correct data values (value::locals) s x y frozen held (by simp [len])⟩
  | .seq a b => do
      let ca ← compile i array depth keys a
      let cb ← compile i array depth keys b
      return ⟨.seq ca.code cb.code,by
        intro x y s ls out h
        cases ha : a.eval i x y s ls <;> simp [MemoryCmd.eval,ha] at h
        exact (cb.frame _ _ _ _ _ h).trans (ca.frame _ _ _ _ _ ha),by
        intro data values locals s x y frozen held len
        simp only [MemoryCmd.eval,ca.correct data values locals s x y frozen held len]
        cases ha : a.eval i x y s locals with
        | none => rfl
        | some mid =>
          exact cb.correct data values locals mid x y ((ca.frame _ _ _ _ _ ha).trans frozen) held len⟩
  | .branch e a b => do
      let ce ← HybridWindowRead.compileRoot i array depth keys e
      let ca ← compile i array depth keys a
      let cb ← compile i array depth keys b
      return ⟨.branch ce.code ca.code cb.code,by
        intro x y s ls out h
        cases he : e.eval i x y s ls [] <;> simp [MemoryCmd.eval,he] at h
        split at h
        · exact cb.frame _ _ _ _ _ h
        · exact ca.frame _ _ _ _ _ h,by
        intro data values locals s x y frozen held len
        simp only [MemoryCmd.eval,ce.correct data values locals s x y frozen held len]
        cases he : e.eval i x y s locals [] with
        | none => rfl
        | some value =>
          simp only [bind,Option.bind]
          split
          · exact ca.correct data values locals s x y frozen held len
          · exact cb.correct data values locals s x y frozen held len⟩
  | .repeat .. | .forRange .. => none

/-- All candidate reads, including reads in expressions/conditions. Unknown
    addresses or writes to the candidate input make that region a miss. -/
def exprAccesses (i : Int) (array : Nat) (e : ReadCode) : Option (List Int) :=
  HybridWindowRead.accesses i array [] e

def accesses (i : Int) (array : Nat) : MemoryCmd → Option (List Int)
  | .skip => some []
  | .assign _ e => exprAccesses i array e
  | .letValue e b => return (← exprAccesses i array e) ++ (← accesses i array b)
  | .store a j e => if a = array then none else return (← exprAccesses i array j) ++ (← exprAccesses i array e)
  | .seq a b => return (← accesses i array a) ++ (← accesses i array b)
  | .branch e a b => return (← exprAccesses i array e) ++ (← accesses i array a) ++ (← accesses i array b)
  | .repeat .. | .forRange .. => none

end IRComparison.HybridWindowBody
