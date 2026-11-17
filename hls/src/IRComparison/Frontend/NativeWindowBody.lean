import IRComparison.Frontend.NativeWindowExpr

namespace IRComparison.NativeWindowBody
open WindowSchedule

structure Compiled (i : Int) (array depth : Nat) (keys : List Int) (source : Imperative.Cmd) where
  code : Imperative.Cmd
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
    (source : Imperative.Cmd) → Option (Compiled i array depth keys source)
  | .skip => some ⟨.skip,by intros; simp_all [Imperative.Cmd.eval],by intros; rfl⟩
  | .assign r e => do
      let c ← NativeWindowExpr.compile i array depth keys e
      return ⟨.assign r c.code,by
        intro x y s ls out h
        cases he : e.eval i x y s ls <;> simp [Imperative.Cmd.eval,he] at h
        subst out; rfl,by
        intro data values locals s x y frozen held len
        simp only [Imperative.Cmd.eval,c.correct data values locals s x y frozen held len]⟩
  | .store a j e =>
      if different : a ≠ array then do
        let cj ← NativeWindowExpr.compile i array depth keys j
        let ce ← NativeWindowExpr.compile i array depth keys e
        return ⟨.store a cj.code ce.code,by
          intro x y s ls out h
          cases hj : j.eval i x y s ls <;> simp [Imperative.Cmd.eval,hj] at h
          cases he : e.eval i x y s ls <;> simp [he] at h
          exact write_other different h,by
          intro data values locals s x y frozen held len
          simp only [Imperative.Cmd.eval,cj.correct data values locals s x y frozen held len,ce.correct data values locals s x y frozen held len]⟩
      else none
  | .letValue e b => do
      let ce ← NativeWindowExpr.compile i array depth keys e
      let cb ← compile i array (depth+1) keys b
      return ⟨.letValue ce.code cb.code,by
        intro x y s ls out h
        cases he : e.eval i x y s ls <;> simp [Imperative.Cmd.eval,he] at h
        exact cb.frame _ _ _ _ _ h,by
        intro data values locals s x y frozen held len
        simp only [Imperative.Cmd.eval,ce.correct data values locals s x y frozen held len]
        cases he : e.eval i x y s locals with
        | none => rfl
        | some value =>
          simpa only [bind,Option.bind,List.cons_append] using
            cb.correct data values (value::locals) s x y frozen held (by simp [len])⟩
  | .seq a b => do
      let ca ← compile i array depth keys a
      let cb ← compile i array depth keys b
      return ⟨.seq ca.code cb.code,by
        intro x y s ls out h
        cases ha : a.eval i x y s ls <;> simp [Imperative.Cmd.eval,ha] at h
        exact (cb.frame _ _ _ _ _ h).trans (ca.frame _ _ _ _ _ ha),by
        intro data values locals s x y frozen held len
        simp only [Imperative.Cmd.eval,ca.correct data values locals s x y frozen held len]
        cases ha : a.eval i x y s locals with
        | none => rfl
        | some mid =>
          exact cb.correct data values locals mid x y ((ca.frame _ _ _ _ _ ha).trans frozen) held len⟩
  | .branch e a b => do
      let ce ← NativeWindowExpr.compile i array depth keys e
      let ca ← compile i array depth keys a
      let cb ← compile i array depth keys b
      return ⟨.branch ce.code ca.code cb.code,by
        intro x y s ls out h
        cases he : e.eval i x y s ls <;> simp [Imperative.Cmd.eval,he] at h
        split at h
        · exact cb.frame _ _ _ _ _ h
        · exact ca.frame _ _ _ _ _ h,by
        intro data values locals s x y frozen held len
        simp only [Imperative.Cmd.eval,ce.correct data values locals s x y frozen held len]
        cases he : e.eval i x y s locals with
        | none => rfl
        | some value =>
          simp only [bind,Option.bind]
          split
          · exact ca.correct data values locals s x y frozen held len
          · exact cb.correct data values locals s x y frozen held len⟩
  | .repeat .. | .forRange .. => none

/-- All candidate reads, including reads in expressions/conditions. Unknown
    addresses or writes to the candidate input make that region a miss. -/
def exprAccesses (i : Int) (array : Nat) : Expr → Option (List Int)
  | .lit .. | .index | .left | .right | .local .. | .reg .. => some []
  | .natIndex e => exprAccesses i array e
  | .add a b | .sub a b | .mul a b | .div a b => return (← exprAccesses i array a) ++ (← exprAccesses i array b)
  | .select c a b => return (← exprAccesses i array c) ++ (← exprAccesses i array a) ++ (← exprAccesses i array b)
  | .read a e => if a = array then return [← NativeWindowExpr.address i e] else exprAccesses i array e

def accesses (i : Int) (array : Nat) : Imperative.Cmd → Option (List Int)
  | .skip => some []
  | .assign _ e => exprAccesses i array e
  | .letValue e b => return (← exprAccesses i array e) ++ (← accesses i array b)
  | .store a j e => if a = array then none else return (← exprAccesses i array j) ++ (← exprAccesses i array e)
  | .seq a b => return (← accesses i array a) ++ (← accesses i array b)
  | .branch e a b => return (← exprAccesses i array e) ++ (← accesses i array a) ++ (← accesses i array b)
  | .repeat .. | .forRange .. => none

end IRComparison.NativeWindowBody
