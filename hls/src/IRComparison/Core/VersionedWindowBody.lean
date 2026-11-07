import IRComparison.Hybrid.HybridSymbolicBody
import IRComparison.Core.VersionedAllocation

namespace IRComparison.VersionedWindowBody
open WindowSchedule AffineAddress SymbolicWindowExpr

/-- The functional rewrite runs on Term directly. It preserves functional
    bindings; allocation is a later pass. Older source-state references remain
    a conservative optimization miss in this current-version pass. -/
structure Compiled (array depth : Nat) (coefficient : Int) (offsets : List Int) (source : VersionedHybrid.Term) where
  code : VersionedHybrid.Term
  guards : List Linear
  frame : ∀ i x y s rest locals out, source.eval i x y (s::rest) locals = some out → out.arrays array = s.arrays array
  correct : ∀ i, Valid guards i → ∀ (data : Array Int) (values locals : List Int) (s : State) (rest : List State) (x y : Int),
    s.arrays array = data → Matches (arrayInput data) (keys coefficient offsets i) values → locals.length = depth →
    code.eval i x y (s::rest) (locals++values) = source.eval i x y (s::rest) locals

def sequence (singleton : Bool) (a b : VersionedHybrid.Term) : VersionedHybrid.Term :=
  if singleton then .letResult 0 a b else .bindResult a b

def compose (singleton : Bool) (ca : Compiled array depth coefficient offsets a) (cb : Compiled array depth coefficient offsets b) :
    Compiled array depth coefficient offsets (sequence singleton a b) where
  code := sequence singleton ca.code cb.code
  guards := ca.guards++cb.guards
  frame := by
    intro i x y s rest ls out h
    cases singleton <;> simp only [sequence,Bool.false_eq_true,Bool.true_eq,↓reduceIte,VersionedHybrid.Term.eval,List.getElem?_cons_zero,bind,Option.bind] at h
    · cases resultA : a.eval i x y (s::rest) ls <;> simp only [resultA,Option.bind_none,Option.bind_some] at h
      · contradiction
      · exact (cb.frame i _ _ _ _ _ _ h).trans (ca.frame i _ _ _ _ _ _ resultA)
    · cases resultA : a.eval i x y [s] ls <;> simp only [resultA,Option.bind_none,Option.bind_some] at h
      · contradiction
      · exact (cb.frame i _ _ _ _ _ _ h).trans (ca.frame i _ _ _ _ _ _ resultA)
  correct := by
    intro i valid data values locals s rest x y frozen held len
    obtain ⟨ha,hb⟩ := valid_append.mp valid
    cases singleton <;> simp only [sequence,Bool.false_eq_true,Bool.true_eq,↓reduceIte,VersionedHybrid.Term.eval,List.getElem?_cons_zero,bind,Option.bind]
    · rw [ca.correct i ha data values locals s rest x y frozen held len]
      cases resultA : a.eval i x y (s::rest) locals with
      | none => rfl
      | some t => exact cb.correct i hb data values locals t (s::rest) x y ((ca.frame i _ _ _ _ _ _ resultA).trans frozen) held len
    · rw [ca.correct i ha data values locals s [] x y frozen held len]
      cases resultA : a.eval i x y [s] locals with
      | none => rfl
      | some t => exact cb.correct i hb data values locals t (s::rest) x y ((ca.frame i _ _ _ _ _ _ resultA).trans frozen) held len

def compile (array depth : Nat) (coefficient : Int) (offsets : List Int) :
    (source : VersionedHybrid.Term) → Option (Compiled array depth coefficient offsets source)
  | .yield 0 => some ⟨.yield 0,[],by intros; simp_all [VersionedHybrid.Term.eval],by intros; rfl⟩
  | .letValue 0 e b => do
      let ce ← HybridSymbolicRead.compileRoot array depth coefficient offsets e
      let cb ← compile array (depth+1) coefficient offsets b
      return ⟨.letValue 0 ce.code cb.code,ce.guards++cb.guards,by
        intro i x y s rest ls out h
        cases he : e.eval i x y s ls [] <;> simp [VersionedHybrid.Term.eval,he] at h
        exact cb.frame i _ _ _ _ _ _ h,by
        intro i valid data values locals s rest x y frozen held len
        obtain ⟨hv,hb⟩ := valid_append.mp valid
        simp only [VersionedHybrid.Term.eval,List.getElem?_cons_zero,bind,Option.bind,
          ce.correct i hv data values locals s x y frozen held len]
        cases he : e.eval i x y s locals [] with
        | none => rfl
        | some v => simpa only [List.cons_append] using cb.correct i hb data values (v::locals) s rest x y frozen held (by simp [len])⟩
  | .letSet 0 r e b => do
      let ce ← HybridSymbolicRead.compileRoot array depth coefficient offsets e
      let cb ← compile array depth coefficient offsets b
      return ⟨.letSet 0 r ce.code cb.code,ce.guards++cb.guards,by
        intro i x y s rest ls out h
        cases he : e.eval i x y s ls [] <;> simp [VersionedHybrid.Term.eval,he] at h
        simpa only [State.set] using cb.frame i x y (s.set r _) (s::rest) ls out h,by
        intro i valid data values locals s rest x y frozen held len
        obtain ⟨hv,hb⟩ := valid_append.mp valid
        simp only [VersionedHybrid.Term.eval,List.getElem?_cons_zero,bind,Option.bind,
          ce.correct i hv data values locals s x y frozen held len]
        cases he : e.eval i x y s locals [] with
        | none => rfl
        | some v => exact cb.correct i hb data values locals (s.set r v) (s::rest) x y frozen held len⟩
  | .letWrite 0 a j e b =>
      if different : a ≠ array then do
        let cj ← HybridSymbolicRead.compileRoot array depth coefficient offsets j
        let ce ← HybridSymbolicRead.compileRoot array depth coefficient offsets e
        let cb ← compile array depth coefficient offsets b
        return ⟨.letWrite 0 a cj.code ce.code cb.code,cj.guards++(ce.guards++cb.guards),by
          intro i x y s rest ls out h
          cases hj : j.eval i x y s ls [] with
          | none => simp [VersionedHybrid.Term.eval,hj] at h
          | some index =>
            cases he : e.eval i x y s ls [] with
            | none => simp [VersionedHybrid.Term.eval,hj,he] at h
            | some v =>
              cases hw : s.write a index v <;> simp [VersionedHybrid.Term.eval,hj,he,hw] at h
              exact (cb.frame i _ _ _ _ _ _ h).trans (NativeWindowBody.write_other different hw),by
          intro i valid data values locals s rest x y frozen held len
          obtain ⟨hj,hvb⟩ := valid_append.mp valid
          obtain ⟨hv,hb⟩ := valid_append.mp hvb
          simp only [VersionedHybrid.Term.eval,List.getElem?_cons_zero,bind,Option.bind,
            cj.correct i hj data values locals s x y frozen held len,ce.correct i hv data values locals s x y frozen held len]
          cases hj : j.eval i x y s locals [] with
          | none => rfl
          | some index =>
            cases he : e.eval i x y s locals [] with
            | none => rfl
            | some v =>
              simp only [Option.bind]
              cases hw : s.write a index v with
              | none => rfl
              | some t => exact cb.correct i hb data values locals t (s::rest) x y ((NativeWindowBody.write_other different hw).trans frozen) held len⟩
      else none
  | .letResult 0 a b => return compose true (← compile array depth coefficient offsets a) (← compile array depth coefficient offsets b)
  | .bindResult a b => return compose false (← compile array depth coefficient offsets a) (← compile array depth coefficient offsets b)
  | .branch 0 e a b => do
      let ce ← HybridSymbolicRead.compileRoot array depth coefficient offsets e
      let ca ← compile array depth coefficient offsets a
      let cb ← compile array depth coefficient offsets b
      return ⟨.branch 0 ce.code ca.code cb.code,ce.guards++(ca.guards++cb.guards),by
        intro i x y s rest ls out h
        cases he : e.eval i x y s ls [] <;> simp [VersionedHybrid.Term.eval,he] at h
        split at h
        · exact cb.frame i _ _ _ _ _ _ h
        · exact ca.frame i _ _ _ _ _ _ h,by
        intro i valid data values locals s rest x y frozen held len
        obtain ⟨hv,hab⟩ := valid_append.mp valid
        obtain ⟨ha,hb⟩ := valid_append.mp hab
        simp only [VersionedHybrid.Term.eval,List.getElem?_cons_zero,bind,Option.bind,
          ce.correct i hv data values locals s x y frozen held len]
        cases he : e.eval i x y s locals [] with
        | none => rfl
        | some v =>
          simp only [Option.bind]
          split
          · exact ca.correct i ha data values locals s rest x y frozen held len
          · exact cb.correct i hb data values locals s rest x y frozen held len⟩
  | _ => none

def accesses (array : Nat) : VersionedHybrid.Term → Option (List Linear)
  | .yield 0 => some []
  | .letValue 0 e b | .letSet 0 _ e b => return (← HybridSymbolicBody.exprAccesses array e) ++ (← accesses array b)
  | .letWrite 0 a j e b => if a = array then none else do
      return (← HybridSymbolicBody.exprAccesses array j) ++ (← HybridSymbolicBody.exprAccesses array e) ++ (← accesses array b)
  | .letResult 0 a b | .bindResult a b => return (← accesses array a) ++ (← accesses array b)
  | .branch 0 e a b => return (← HybridSymbolicBody.exprAccesses array e) ++ (← accesses array a) ++ (← accesses array b)
  | _ => none

end IRComparison.VersionedWindowBody
