import IRComparison.Hybrid.HybridSymbolicRead
import IRComparison.Hybrid.HybridSource
import IRComparison.Frontend.NativeWindowBody

namespace IRComparison.HybridSymbolicBody
open WindowSchedule AffineAddress SymbolicWindowExpr HybridIR

structure Compiled (array depth : Nat) (coefficient : Int) (offsets : List Int) (source : MemoryCmd) where
  code : MemoryCmd
  guards : List Linear
  arrays : ∀ allowed, source.target.ArraysWithin allowed → code.target.ArraysWithin allowed
  word : ∀ locals, WordCommand locals source.target → WordCommand (bufferWords depth locals) code.target
  frame : ∀ i x y s locals out, source.eval i x y s locals = some out → out.arrays array = s.arrays array
  correct : ∀ i, Valid guards i → ∀ (data : Array Int) (values locals : List Int) (s : State) (x y : Int),
    s.arrays array = data → Matches (arrayInput data) (keys coefficient offsets i) values → locals.length = depth →
    code.eval i x y s (locals++values) = source.eval i x y s locals

/-- State relation used by structural RHL composition. The source input array
stays fixed; the target's extra buffer bindings are supplied separately. -/
def Stable (array : Nat) (data : Array Int) (s t : State) : Prop :=
  s = t ∧ s.arrays array = data

theorem Compiled.translation (c : Compiled array depth coefficient offsets source)
    (valid : Valid c.guards i)
    (held : Matches (arrayInput data) (keys coefficient offsets i) values)
    (len : locals.length = depth) :
    Relational.Translation (Stable array data) (fun s => source.eval i x y s locals)
      (fun t => c.code.eval i x y t (locals++values)) (Stable array data) := by
  intro s t h
  obtain ⟨rfl,frozen⟩ := h
  dsimp only
  rw [c.correct i valid data values locals s x y frozen held len]
  cases he : source.eval i x y s locals with
  | none => exact .none
  | some out => exact .some ⟨rfl,(c.frame _ _ _ _ _ _ he).trans frozen⟩

def compile (array depth : Nat) (coefficient : Int) (offsets : List Int) :
    (source : MemoryCmd) → Option (Compiled array depth coefficient offsets source)
  | .skip => some ⟨.skip,[],by intros; trivial,by intros; exact .skip,by intros; simp_all [MemoryCmd.eval],by intros; rfl⟩
  | .assign r e => do
      let c ← HybridSymbolicRead.compileRoot array depth coefficient offsets e
      return ⟨.assign r c.code,c.guards,by intro allowed h; exact c.arrays _ h,by
        intro locals typed
        cases typed with | assign h => exact .assign (c.word _ _ h),by
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
          intro allowed h; exact ⟨h.1,cj.arrays _ h.2.1,ce.arrays _ h.2.2⟩,by
          intro locals typed
          cases typed with | store h => exact .store (ce.word _ _ h),by
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
        intro allowed h; exact ⟨ce.arrays _ h.1,cb.arrays _ h.2⟩,by
        intro locals typed
        cases typed with
        | letValue he hb => exact .letValue (ce.word _ _ he) (by simpa only [bufferWords_push] using cb.word _ hb),by
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
        intro allowed h; exact ⟨ca.arrays _ h.1,cb.arrays _ h.2⟩,by
        intro locals typed
        cases typed with | seq ha hb => exact .seq (ca.word _ ha) (cb.word _ hb),by
        intro i x y s ls out h
        cases ha : a.eval i x y s ls <;> simp [MemoryCmd.eval,ha] at h
        exact (cb.frame i _ _ _ _ _ h).trans (ca.frame i _ _ _ _ _ ha),by
        intro i valid data values locals s x y frozen held len
        obtain ⟨hv,hb⟩ := valid_append.mp valid
        have translated := Relational.seq
          (ca.translation (x:=x) (y:=y) hv held len) (cb.translation (x:=x) (y:=y) hb held len)
        have observed := Relational.consequence translated (fun _ _ h => h) (fun _ _ h => h.1)
        exact (Relational.result_eq (observed s s ⟨rfl,frozen⟩)).symm⟩
  | .branch e a b => do
      let ce ← HybridSymbolicRead.compileRoot array depth coefficient offsets e
      let ca ← compile array depth coefficient offsets a
      let cb ← compile array depth coefficient offsets b
      return ⟨.branch ce.code ca.code cb.code,ce.guards++(ca.guards++cb.guards),by
        intro allowed h; exact ⟨ce.arrays _ h.1,ca.arrays _ h.2.1,cb.arrays _ h.2.2⟩,by
        intro locals typed
        cases typed with | branch ha hb => exact .branch (ca.word _ ha) (cb.word _ hb),by
        intro i x y s ls out h
        cases he : e.eval i x y s ls [] <;> simp [MemoryCmd.eval,he] at h
        split at h
        · exact cb.frame i _ _ _ _ _ h
        · exact ca.frame i _ _ _ _ _ h,by
        intro i valid data values locals s x y frozen held len
        obtain ⟨hv,hab⟩ := valid_append.mp valid
        obtain ⟨ha,hb⟩ := valid_append.mp hab
        have guards : ∀ s t, Stable array data s t →
            (e.eval i x y s locals []).map (· != 0) =
              (ce.code.eval i x y t (locals++values) []).map (· != 0) := by
          intro u v h
          obtain ⟨rfl,hf⟩ := h
          rw [ce.correct i hv data values locals u x y hf held len]
        have translated := Relational.branch_rule guards
          (Relational.consequence (ca.translation (x:=x) (y:=y) ha held len)
            (fun _ _ h => h.1) (fun _ _ h => h))
          (Relational.consequence (cb.translation (x:=x) (y:=y) hb held len)
            (fun _ _ h => h.1) (fun _ _ h => h))
        have observed := Relational.consequence translated (fun _ _ h => h) (fun _ _ h => h.1)
        simpa only [Relational.branch,MemoryCmd.eval,bind,Option.bind_map,Function.comp_def]
          using (Relational.result_eq (observed s s ⟨rfl,frozen⟩)).symm⟩
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
