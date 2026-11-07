import IRComparison.Frontend.NativeWindowBody

namespace IRComparison.FunctionalWindowBody
open WindowSchedule

/-- The functional rewrite runs on Term directly. It preserves functional
    bindings; allocation is a later pass. Older source-state references remain
    a conservative optimization miss in this current-version pass. -/
structure Compiled (i : Int) (array depth : Nat) (keys : List Int) (source : Functional.Term) where
  code : Functional.Term
  frame : ∀ x y s rest locals out, source.eval i x y (s::rest) locals = some out → out.arrays array = s.arrays array
  correct : ∀ (data : Array Int) (values locals : List Int) (s : State) (rest : List State) (x y : Int),
    s.arrays array = data → Matches (arrayInput data) keys values → locals.length = depth →
    code.eval i x y (s::rest) (locals++values) = source.eval i x y (s::rest) locals

def sequence (singleton : Bool) (a b : Functional.Term) : Functional.Term :=
  if singleton then .letResult 0 a b else .bindResult a b

def compose (singleton : Bool) (ca : Compiled i array depth keys a) (cb : Compiled i array depth keys b) :
    Compiled i array depth keys (sequence singleton a b) where
  code := sequence singleton ca.code cb.code
  frame := by
    intro x y s rest ls out h
    cases singleton <;> simp only [sequence,Bool.false_eq_true,Bool.true_eq,↓reduceIte,Functional.Term.eval,List.getElem?_cons_zero,bind,Option.bind] at h
    · cases ha : a.eval i x y (s::rest) ls <;> simp only [ha,Option.bind_none,Option.bind_some] at h
      · contradiction
      · exact (cb.frame _ _ _ _ _ _ h).trans (ca.frame _ _ _ _ _ _ ha)
    · cases ha : a.eval i x y [s] ls <;> simp only [ha,Option.bind_none,Option.bind_some] at h
      · contradiction
      · exact (cb.frame _ _ _ _ _ _ h).trans (ca.frame _ _ _ _ _ _ ha)
  correct := by
    intro data values locals s rest x y frozen held len
    cases singleton <;> simp only [sequence,Bool.false_eq_true,Bool.true_eq,↓reduceIte,Functional.Term.eval,List.getElem?_cons_zero,bind,Option.bind]
    · rw [ca.correct data values locals s rest x y frozen held len]
      cases ha : a.eval i x y (s::rest) locals with
      | none => rfl
      | some t => exact cb.correct data values locals t (s::rest) x y ((ca.frame _ _ _ _ _ _ ha).trans frozen) held len
    · rw [ca.correct data values locals s [] x y frozen held len]
      cases ha : a.eval i x y [s] locals with
      | none => rfl
      | some t => exact cb.correct data values locals t (s::rest) x y ((ca.frame _ _ _ _ _ _ ha).trans frozen) held len

def compile (i : Int) (array depth : Nat) (keys : List Int) :
    (source : Functional.Term) → Option (Compiled i array depth keys source)
  | .yield 0 => some ⟨.yield 0,by intros; simp_all [Functional.Term.eval],by intros; rfl⟩
  | .letValue 0 e b => do
      let ce ← NativeWindowExpr.compile i array depth keys e
      let cb ← compile i array (depth+1) keys b
      return ⟨.letValue 0 ce.code cb.code,by
        intro x y s rest ls out h
        cases he : e.eval i x y s ls <;> simp [Functional.Term.eval,he] at h
        exact cb.frame _ _ _ _ _ _ h,by
        intro data values locals s rest x y frozen held len
        simp only [Functional.Term.eval,List.getElem?_cons_zero,bind,Option.bind,
          ce.correct data values locals s x y frozen held len]
        cases he : e.eval i x y s locals with
        | none => rfl
        | some v => simpa only [List.cons_append] using cb.correct data values (v::locals) s rest x y frozen held (by simp [len])⟩
  | .letSet 0 r e b => do
      let ce ← NativeWindowExpr.compile i array depth keys e
      let cb ← compile i array depth keys b
      return ⟨.letSet 0 r ce.code cb.code,by
        intro x y s rest ls out h
        cases he : e.eval i x y s ls <;> simp [Functional.Term.eval,he] at h
        simpa only [State.set] using cb.frame x y (s.set r _) (s::rest) ls out h,by
        intro data values locals s rest x y frozen held len
        simp only [Functional.Term.eval,List.getElem?_cons_zero,bind,Option.bind,
          ce.correct data values locals s x y frozen held len]
        cases he : e.eval i x y s locals with
        | none => rfl
        | some v => exact cb.correct data values locals (s.set r v) (s::rest) x y frozen held len⟩
  | .letWrite 0 a j e b =>
      if different : a ≠ array then do
        let cj ← NativeWindowExpr.compile i array depth keys j
        let ce ← NativeWindowExpr.compile i array depth keys e
        let cb ← compile i array depth keys b
        return ⟨.letWrite 0 a cj.code ce.code cb.code,by
          intro x y s rest ls out h
          cases hj : j.eval i x y s ls with
          | none => simp [Functional.Term.eval,hj] at h
          | some index =>
            cases he : e.eval i x y s ls with
            | none => simp [Functional.Term.eval,hj,he] at h
            | some v =>
              cases hw : s.write a index v <;> simp [Functional.Term.eval,hj,he,hw] at h
              exact (cb.frame _ _ _ _ _ _ h).trans (NativeWindowBody.write_other different hw),by
          intro data values locals s rest x y frozen held len
          simp only [Functional.Term.eval,List.getElem?_cons_zero,bind,Option.bind,
            cj.correct data values locals s x y frozen held len,ce.correct data values locals s x y frozen held len]
          cases hj : j.eval i x y s locals with
          | none => rfl
          | some index =>
            cases he : e.eval i x y s locals with
            | none => rfl
            | some v =>
              simp only [Option.bind]
              cases hw : s.write a index v with
              | none => rfl
              | some t => exact cb.correct data values locals t (s::rest) x y ((NativeWindowBody.write_other different hw).trans frozen) held len⟩
      else none
  | .letResult 0 a b => return compose true (← compile i array depth keys a) (← compile i array depth keys b)
  | .bindResult a b => return compose false (← compile i array depth keys a) (← compile i array depth keys b)
  | .branch 0 e a b => do
      let ce ← NativeWindowExpr.compile i array depth keys e
      let ca ← compile i array depth keys a
      let cb ← compile i array depth keys b
      return ⟨.branch 0 ce.code ca.code cb.code,by
        intro x y s rest ls out h
        cases he : e.eval i x y s ls <;> simp [Functional.Term.eval,he] at h
        split at h
        · exact cb.frame _ _ _ _ _ _ h
        · exact ca.frame _ _ _ _ _ _ h,by
        intro data values locals s rest x y frozen held len
        simp only [Functional.Term.eval,List.getElem?_cons_zero,bind,Option.bind,
          ce.correct data values locals s x y frozen held len]
        cases he : e.eval i x y s locals with
        | none => rfl
        | some v =>
          simp only [Option.bind]
          split
          · exact ca.correct data values locals s rest x y frozen held len
          · exact cb.correct data values locals s rest x y frozen held len⟩
  | _ => none

def accesses (i : Int) (array : Nat) : Functional.Term → Option (List Int)
  | .yield 0 => some []
  | .letValue 0 e b | .letSet 0 _ e b => return (← NativeWindowBody.exprAccesses i array e) ++ (← accesses i array b)
  | .letWrite 0 a j e b => if a = array then none else do
      return (← NativeWindowBody.exprAccesses i array j) ++ (← NativeWindowBody.exprAccesses i array e) ++ (← accesses i array b)
  | .letResult 0 a b | .bindResult a b => return (← accesses i array a) ++ (← accesses i array b)
  | .branch 0 e a b => return (← NativeWindowBody.exprAccesses i array e) ++ (← accesses i array a) ++ (← accesses i array b)
  | _ => none

end IRComparison.FunctionalWindowBody
