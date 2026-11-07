import PaperCore.SourcePass

namespace PaperCore.SourcePass

theorem Agrees.symm (h : Agrees ordinary left right) : Agrees ordinary right left :=
  ⟨fun x hx => (h.registers x hx).symm,h.memory.symm⟩

theorem Agrees.trans (first : Agrees ordinary left middle) (second : Agrees ordinary middle right) :
    Agrees ordinary left right :=
  ⟨fun x hx => (first.registers x hx).trans (second.registers x hx),first.memory.trans second.memory⟩

theorem Agrees.setReg (h : Agrees ordinary left right) (x : Var) (value : Int) :
    Agrees ordinary (left.setReg x value) (right.setReg x value) := by
  refine ⟨?_,h.memory⟩
  intro y hy
  by_cases same : y = x
  · subst y; simp [State.setReg]
  · simpa [State.setReg,lookup_put_other _ _ _ _ same] using h.registers y hy

theorem Agrees.eval_eq {e : Expr Op} {meaning : Op → Int → Int → Int} (h : Agrees ordinary left right) (typed : e.ordinary ordinary) :
    e.eval meaning left.regs = e.eval meaning right.regs := by
  cases e with
  | num value => rfl
  | var x => exact h.registers x typed
  | bin op x y => simp only [Expr.eval,h.registers x typed.1,h.registers y typed.2]

/-- Source execution ignores fresh buffer and address registers. This is a
simulation of the existing semantics, not a new meaning for source programs. -/
theorem execute_frame (run : SourceExec meaning code left leftOut)
    (typed : BufferView.Typed ordinary code) (agrees : Agrees ordinary left right) :
    ∃ rightOut, SourceExec meaning code right rightOut ∧ Agrees ordinary leftOut rightOut := by
  induction run generalizing right with
  | action step =>
    cases step with
    | read index cell =>
      refine ⟨right.setReg _ _,.action (.read ((agrees.eval_eq typed.2).symm.trans index) ?_),agrees.setReg _ _⟩
      simpa only [agrees.memory] using cell
    | write index value =>
      refine ⟨{right with memory := put right.memory _ _},
        .action (.write ((agrees.eval_eq typed.2).symm.trans index)
          ((agrees.registers _ typed.1).symm.trans value)),⟨agrees.registers,?_⟩⟩
      rw [agrees.memory]
  | assign value =>
    exact ⟨right.setReg _ _,.assign ((agrees.eval_eq typed.2).symm.trans value),agrees.setReg _ _⟩
  | seq first second ihFirst ihSecond =>
    obtain ⟨middle,runMiddle,agreeMiddle⟩ := ihFirst typed.1 agrees
    obtain ⟨final,runFinal,agreeFinal⟩ := ihSecond typed.2 agreeMiddle
    exact ⟨final,.seq runMiddle runFinal,agreeFinal⟩
  | ifTrue condition nonzero body ih =>
    obtain ⟨final,runFinal,agreeFinal⟩ := ih typed.2.1 agrees
    exact ⟨final,.ifTrue ((agrees.registers _ typed.1).symm.trans condition) nonzero runFinal,agreeFinal⟩
  | ifFalse condition body ih =>
    obtain ⟨final,runFinal,agreeFinal⟩ := ih typed.2.2 agrees
    exact ⟨final,.ifFalse ((agrees.registers _ typed.1).symm.trans condition) runFinal,agreeFinal⟩
  | forExit value =>
    exact ⟨right.setReg _ _,.forExit ((agrees.eval_eq typed.2.1).symm.trans value),agrees.setReg _ _⟩
  | forLoop value nonzero body counter rest ihBody ihRest =>
    obtain ⟨middle,runMiddle,agreeMiddle⟩ := ihBody typed.2.2 (agrees.setReg _ _)
    obtain ⟨final,runFinal,agreeFinal⟩ := ihRest ⟨typed.1,True.intro,typed.2.2⟩ agreeMiddle
    exact ⟨final,.forLoop ((agrees.eval_eq typed.2.1).symm.trans value) nonzero runMiddle
      ((agreeMiddle.registers _ typed.1).symm.trans counter) runFinal,agreeFinal⟩
  | kernel body ih =>
    obtain ⟨final,runFinal,agreeFinal⟩ := ih typed agrees
    exact ⟨final,.kernel runFinal,agreeFinal⟩

#print axioms execute_frame
end PaperCore.SourcePass
