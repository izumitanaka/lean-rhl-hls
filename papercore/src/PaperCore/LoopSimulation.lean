import PaperCore.ControlRules

namespace PaperCore

/-- Proof infrastructure only: a lockstep loop simulation for arbitrary
    atomic relations and memories. No trip count, stride sign, or counter
    stability is assumed. The invariant is at the initialized loop head. -/
theorem loop_simulation
    (meaning : Op → Int → Int → Int)
    (left : A → State M → State M → Prop)
    (right : B → State N → State N → Prop)
    (invariant : State M → State N → Prop)
    (body : ∀ s t, invariant s t → ∀ k, s.regs.lookup x = some k → k ≠ stop →
      ∀ s', Exec meaning left leftBody s s' →
      ∃ t', Exec meaning right rightBody t t' ∧
        ∀ next, s'.regs.lookup x = some next →
          t'.regs.lookup x = some next ∧
          invariant (s'.setReg x (next+step)) (t'.setReg x (next+step)))
    (run : Exec meaning left (.loop x e stop step leftBody) source out)
    (equal : e.eval meaning source.regs = e.eval meaning target.regs)
    (initial : ∀ k, e.eval meaning source.regs = some k →
      invariant (source.setReg x k) (target.setReg x k)) :
    ∃ target', Exec meaning right (.loop x e stop step rightBody) target target' ∧
      invariant out target' ∧ out.regs.lookup x = some stop ∧ target'.regs.lookup x = some stop := by
  generalize codeEq : Stmt.loop x e stop step leftBody = code at run
  induction run generalizing e target with
  | action h => cases codeEq
  | assign h => cases codeEq
  | seq h₁ h₂ ih₁ ih₂ => cases codeEq
  | ifTrue h₁ h₂ h₃ ih => cases codeEq
  | ifFalse h₁ h₂ ih => cases codeEq
  | kernel h ih => cases codeEq
  | @forExit bound counter init delta codeBody s value =>
    cases codeEq
    have targetValue := equal ▸ value
    refine ⟨target.setReg x stop,.forExit targetValue,initial stop value,?_,?_⟩ <;>
      simp [State.setReg]
  | @forLoop k bound codeBody mid counter next delta result init s value nonzero bodyRun counterValue rest ihBody ihRest =>
    cases codeEq
    have atHead := initial k value
    have setCounter : (s.setReg x k).regs.lookup x = some k := by simp [State.setReg]
    obtain ⟨tm,htm,advance⟩ := body _ _ atHead k setCounter nonzero _ bodyRun
    obtain ⟨targetCounter,nextHead⟩ := advance next counterValue
    obtain ⟨tt,htt,inv,finishLeft,finishRight⟩ := ihRest (e := .num (next+step))
      (target := tm) rfl (by intro n hn; simp [Expr.eval] at hn; subst n; exact nextHead) rfl
    exact ⟨tt,.forLoop (equal ▸ value) nonzero htm targetCounter htt,inv,finishLeft,finishRight⟩

#print axioms loop_simulation
end PaperCore
