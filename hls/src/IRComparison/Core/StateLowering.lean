import IRComparison.Core.Imperative
import IRComparison.Core.Functional

namespace IRComparison.StateLowering

/-- A sufficient condition for using a single mutable state. This rejects
    unsupported version uses; it does not change their source meaning. -/
def lower : Functional.Term → Option Imperative.Cmd
  | .yield 0 => some .skip
  | .letValue 0 e b => return .letValue e (← lower b)
  | .letSet 0 r e b => return .seq (.assign r e) (← lower b)
  | .letWrite 0 a j e b => return .seq (.store a j e) (← lower b)
  | .bindResult b next => return .seq (← lower b) (← lower next)
  | .letResult 0 b next => return .seq (← lower b) (← lower next)
  | .branch 0 e a b => return .branch e (← lower a) (← lower b)
  | .iterate 0 n b next => return .seq (.repeat n (← lower b)) (← lower next)
  | .forRange 0 e b next => return .seq (.forRange e (← lower b)) (← lower next)
  | _ => none

/-- Successful lowering is valid even in an environment containing arbitrary
    older versions. There is no hypothesis identifying them with current state. -/
theorem lower_correct (term : Functional.Term) (code : Imperative.Cmd)
    (h : lower term = some code) (i x y : Int) (s : State)
    (older : List State) (locals : List Int) :
    code.eval i x y s locals = term.eval i x y (s :: older) locals := by
  induction term generalizing code s older locals with
  | yield v =>
    cases v <;> simp [lower] at h
    subst code
    rfl
  | letValue v e b ih =>
    cases v <;> simp only [lower] at h
    · cases hb : lower b <;> simp [hb] at h
      subst code
      simp only [Imperative.Cmd.eval, Functional.Term.eval, List.getElem?_cons_zero, Option.bind_some]
      cases he : e.eval i x y s locals <;> simp [he]
      exact ih _ hb _ _ _
    · cases h
  | letSet v r e b ih =>
    cases v <;> simp only [lower] at h
    · cases hb : lower b <;> simp [hb] at h
      subst code
      simp only [Imperative.Cmd.eval, Functional.Term.eval, List.getElem?_cons_zero, Option.bind_some]
      cases he : e.eval i x y s locals <;> simp [he]
      exact ih _ hb _ _ _
    · cases h
  | letWrite v a j e b ih =>
    cases v <;> simp only [lower] at h
    · cases hb : lower b <;> simp [hb] at h
      subst code
      simp only [Imperative.Cmd.eval, Functional.Term.eval, List.getElem?_cons_zero, Option.bind_some]
      cases hj : j.eval i x y s locals <;> simp [hj]
      cases he : e.eval i x y s locals <;> simp [he]
      cases hw : s.write a _ _ <;> simp [hw]
      exact ih _ hb _ _ _
    · cases h
  | bindResult b next ihb ihn =>
    cases hb : lower b <;> simp [lower,hb] at h
    cases hn : lower next <;> simp [hn] at h
    subst code
    simp only [Imperative.Cmd.eval,Functional.Term.eval]
    rw [ihb _ hb s older locals]
    cases ht : b.eval i x y (s::older) locals <;> simp [ht]
    exact ihn _ hn _ (s::older) locals
  | letResult v b next ihb ihn =>
    cases v <;> simp only [lower] at h
    · cases hb : lower b <;> simp [hb] at h
      cases hn : lower next <;> simp [hn] at h
      subst code
      simp only [Imperative.Cmd.eval, Functional.Term.eval, List.getElem?_cons_zero, Option.bind_some]
      rw [ihb _ hb s [] locals]
      cases ht : b.eval i x y [s] locals <;> simp [ht]
      exact ihn _ hn _ _ _
    · cases h
  | branch v e a b iha ihb =>
    cases v <;> simp only [lower] at h
    · cases ha : lower a <;> simp [ha] at h
      cases hb : lower b <;> simp [hb] at h
      subst code
      simp only [Imperative.Cmd.eval, Functional.Term.eval, List.getElem?_cons_zero, Option.bind_some]
      cases he : e.eval i x y s locals <;> simp [he]
      split
      · exact ihb _ hb _ _ _
      · exact iha _ ha _ _ _
    · cases h
  | iterate v n b next ihb ihn =>
    cases v <;> simp only [lower] at h
    · cases hb : lower b <;> simp [hb] at h
      cases hn : lower next <;> simp [hn] at h
      subst code
      simp only [Imperative.Cmd.eval, Functional.Term.eval, List.getElem?_cons_zero, Option.bind_some]
      have same := funext (fun t => funext (fun (_ : Nat) => ihb _ hb t [] locals))
      rw [same]
      cases ht : (List.range n).foldlM (fun t _ => b.eval i x y [t] locals) s <;> simp [ht]
      exact ihn _ hn _ _ _
    · cases h
  | forRange v e b next ihb ihn =>
    cases v <;> simp only [lower] at h
    · cases hb : lower b <;> simp [hb] at h
      cases hn : lower next <;> simp [hn] at h
      subst code
      simp only [Imperative.Cmd.eval, Functional.Term.eval, List.getElem?_cons_zero]
      cases he : e.eval i x y s locals <;> simp [he]
      have same := funext (fun t => funext (fun (k : Nat) => ihb _ hb t [] (Int.ofNat k :: locals)))
      simp only [Int.ofNat_eq_natCast] at same
      rw [same]
      cases ht : (List.range _).foldlM (fun t k => b.eval i x y [t] (Int.ofNat k :: locals)) s <;> simp [ht]
      exact ihn _ hn _ _ _
    · cases h

  | forRangeCaptured => simp [lower] at h

end IRComparison.StateLowering
