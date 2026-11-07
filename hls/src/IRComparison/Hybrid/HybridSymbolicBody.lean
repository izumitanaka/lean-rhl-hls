import IRComparison.Hybrid.HybridSymbolicRead
import IRComparison.Hybrid.HybridSource
import IRComparison.Frontend.NativeWindowBody

namespace IRComparison.HybridSymbolicBody
open WindowSchedule AffineAddress SymbolicWindowExpr HybridIR

structure Compiled (array depth : Nat) (coefficient : Int) (offsets : List Int) (source : MemoryCmd) where
  code : MemoryCmd
  guards : List Linear
  frame : ∀ i x y s locals out, source.eval i x y s locals = some out → out.arrays array = s.arrays array
  correct : ∀ i, Valid guards i → ∀ (data : Array Int) (values locals : List Int) (s : State) (x y : Int),
    s.arrays array = data → Matches (arrayInput data) (keys coefficient offsets i) values → locals.length = depth →
    code.eval i x y s (locals++values) = source.eval i x y s locals

def compile (array depth : Nat) (coefficient : Int) (offsets : List Int) :
    (source : MemoryCmd) → Option (Compiled array depth coefficient offsets source)
  | .skip => some ⟨.skip,[],by intros; simp_all [MemoryCmd.eval],by intros; rfl⟩
  | .assign r e => do
      let c ← HybridSymbolicRead.compileRoot array depth coefficient offsets e
      return ⟨.assign r c.code,c.guards,by
        intro i x y s ls out h
        cases he : e.eval i x y s ls [] <;> simp [MemoryCmd.eval,he] at h
        subst out; rfl,by
        intro i valid data values locals s x y frozen held len
        simp only [MemoryCmd.eval,c.correct i valid data values locals s x y frozen held len]⟩
  | .store a j e =>
      if different : a ≠ array then do
        let cj ← HybridSymbolicRead.compileRoot array depth coefficient offsets j
        let ce ← HybridSymbolicRead.compileRoot array depth coefficient offsets e
        return ⟨.store a cj.code ce.code,cj.guards++ce.guards,by
          intro i x y s ls out h
          cases hj : j.eval i x y s ls [] <;> simp [MemoryCmd.eval,hj] at h
          cases he : e.eval i x y s ls [] <;> simp [he] at h
          exact NativeWindowBody.write_other different h,by
          intro i valid data values locals s x y frozen held len
          obtain ⟨hj,he⟩ := valid_append.mp valid
          simp only [MemoryCmd.eval,cj.correct i hj data values locals s x y frozen held len,ce.correct i he data values locals s x y frozen held len]⟩
      else none
  | .letValue e b => do
      let ce ← HybridSymbolicRead.compileRoot array depth coefficient offsets e
      let cb ← compile array (depth+1) coefficient offsets b
      return ⟨.letValue ce.code cb.code,ce.guards++cb.guards,by
        intro i x y s ls out h
        cases he : e.eval i x y s ls [] <;> simp [MemoryCmd.eval,he] at h
        exact cb.frame i _ _ _ _ _ h,by
        intro i valid data values locals s x y frozen held len
        obtain ⟨hv,hb⟩ := valid_append.mp valid
        simp only [MemoryCmd.eval,ce.correct i hv data values locals s x y frozen held len]
        cases he : e.eval i x y s locals [] with
        | none => rfl
        | some value =>
          simpa only [bind,Option.bind,List.cons_append] using
            cb.correct i hb data values (value::locals) s x y frozen held (by simp [len])⟩
  | .seq a b => do
      let ca ← compile array depth coefficient offsets a
      let cb ← compile array depth coefficient offsets b
      return ⟨.seq ca.code cb.code,ca.guards++cb.guards,by
        intro i x y s ls out h
        cases ha : a.eval i x y s ls <;> simp [MemoryCmd.eval,ha] at h
        exact (cb.frame i _ _ _ _ _ h).trans (ca.frame i _ _ _ _ _ ha),by
        intro i valid data values locals s x y frozen held len
        obtain ⟨hv,hb⟩ := valid_append.mp valid
        simp only [MemoryCmd.eval,ca.correct i hv data values locals s x y frozen held len]
        cases ha : a.eval i x y s locals with
        | none => rfl
        | some mid =>
          exact cb.correct i hb data values locals mid x y ((ca.frame i _ _ _ _ _ ha).trans frozen) held len⟩
  | .branch e a b => do
      let ce ← HybridSymbolicRead.compileRoot array depth coefficient offsets e
      let ca ← compile array depth coefficient offsets a
      let cb ← compile array depth coefficient offsets b
      return ⟨.branch ce.code ca.code cb.code,ce.guards++(ca.guards++cb.guards),by
        intro i x y s ls out h
        cases he : e.eval i x y s ls [] <;> simp [MemoryCmd.eval,he] at h
        split at h
        · exact cb.frame i _ _ _ _ _ h
        · exact ca.frame i _ _ _ _ _ h,by
        intro i valid data values locals s x y frozen held len
        obtain ⟨hv,hab⟩ := valid_append.mp valid
        obtain ⟨ha,hb⟩ := valid_append.mp hab
        simp only [MemoryCmd.eval,ce.correct i hv data values locals s x y frozen held len]
        cases he : e.eval i x y s locals [] with
        | none => rfl
        | some value =>
          simp only [bind,Option.bind]
          split
          · exact ca.correct i ha data values locals s x y frozen held len
          · exact cb.correct i hb data values locals s x y frozen held len⟩
  | .repeat .. | .forRange .. => none

/-- All candidate reads, including reads in expressions/conditions. Unknown
    addresses or writes to the candidate input make that region a miss. -/
def exprAccesses (array : Nat) (e : ReadCode) : Option (List Linear) := HybridSymbolicRead.accesses array [] e

def accesses (array : Nat) : MemoryCmd → Option (List Linear)
  | .skip => some []
  | .assign _ e => exprAccesses array e
  | .letValue e b => return (← exprAccesses array e) ++ (← accesses array b)
  | .store a j e => if a = array then none else return (← exprAccesses array j) ++ (← exprAccesses array e)
  | .seq a b => return (← accesses array a) ++ (← accesses array b)
  | .branch e a b => return (← exprAccesses array e) ++ (← accesses array a) ++ (← accesses array b)
  | .repeat .. | .forRange .. => none

end IRComparison.HybridSymbolicBody
