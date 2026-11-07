import PaperCore.LoopSimulation

namespace PaperCore

def loopGuard (inv : Assertion) (x : Var) (stop : Int) : Assertion :=
  fun regs heap indices => inv regs heap indices ∧
    ∃ k, regs.lookup x = some k ∧ k ≠ stop

/-- Semantic form of [x+step/x]inv; x+step is metalevel arithmetic here,
    not a newly added source-expression constructor. -/
def advancePre (inv : Assertion) (x : Var) (step : Int) : Assertion :=
  fun regs heap indices => ∀ next, regs.lookup x = some next →
    inv (put regs x (next+step)) heap indices

def loopPost (inv : Assertion) (x : Var) (stop : Int) : Assertion :=
  fun regs heap indices => inv regs heap indices ∧ regs.lookup x = some stop

/-- Tr-For for the agreed != semantics, in both execution directions.
    No assumption that the loop terminates, reaches its bound, has positive
    stride, or leaves its counter unchanged in the body is introduced. -/
theorem Translation.loop (meaning : Op → Int → Int → Int)
    (typed : e.ordinary ordinary) (counterTyped : ordinary x)
    (body : Translation meaning ordinary arrays (loopGuard inv x stop)
      sourceBody targetBody (advancePre inv x step)) :
    Translation meaning ordinary arrays (assignPre meaning x e inv)
      (.loop x e stop step sourceBody) (.loop x e stop step targetBody)
      (loopPost inv x stop) := by
  intro source target indices related
  have equal := related.1.eval_eq meaning e typed
  constructor
  · intro source' execution
    have transfer : ∀ s t,
        (∃ is, Related ordinary arrays inv s t is) →
        ∀ k, s.regs.lookup x = some k → k ≠ stop →
        ∀ s', SourceExec meaning sourceBody s s' →
        ∃ t', TargetExec meaning targetBody t t' ∧
          ∀ next, s'.regs.lookup x = some next → t'.regs.lookup x = some next ∧
            ∃ is, Related ordinary arrays inv (s'.setReg x (next+step))
              (t'.setReg x (next+step)) is := by
      rintro s t ⟨is,corr,holds⟩ k counter nonzero s' run
      have targetCounter := corr.registers x counterTyped ▸ counter
      obtain ⟨t',js,rt,after⟩ := (body s t is ⟨corr,holds,k,targetCounter,nonzero⟩).1 s' run
      refine ⟨t',rt,?_⟩
      intro next value
      have targetValue := after.1.registers x counterTyped ▸ value
      exact ⟨targetValue,js,after.1.setReg x _,after.2 next targetValue⟩
    have initial : ∀ k, e.eval meaning source.regs = some k →
        ∃ is, Related ordinary arrays inv (source.setReg x k) (target.setReg x k) is := by
      intro k value
      exact ⟨indices,related.1.setReg x k,related.2 k (equal ▸ value)⟩
    obtain ⟨t',run,⟨is,corr,holds⟩,leftEnd,rightEnd⟩ :=
      loop_simulation meaning (MemoryStep meaning) StreamStep
        (fun s t => ∃ is, Related ordinary arrays inv s t is) transfer execution equal initial
    exact ⟨t',is,run,corr,holds,rightEnd⟩
  · intro target' execution
    have transfer : ∀ t s,
        (∃ is, Related ordinary arrays inv s t is) →
        ∀ k, t.regs.lookup x = some k → k ≠ stop →
        ∀ t', TargetExec meaning targetBody t t' →
        ∃ s', SourceExec meaning sourceBody s s' ∧
          ∀ next, t'.regs.lookup x = some next → s'.regs.lookup x = some next ∧
            ∃ is, Related ordinary arrays inv (s'.setReg x (next+step))
              (t'.setReg x (next+step)) is := by
      rintro t s ⟨is,corr,holds⟩ k counter nonzero t' run
      obtain ⟨s',js,rs,after⟩ := (body s t is ⟨corr,holds,k,counter,nonzero⟩).2 t' run
      refine ⟨s',rs,?_⟩
      intro next value
      have sourceValue := (after.1.registers x counterTyped).symm ▸ value
      exact ⟨sourceValue,js,after.1.setReg x _,after.2 next value⟩
    have initial : ∀ k, e.eval meaning target.regs = some k →
        ∃ is, Related ordinary arrays inv (source.setReg x k) (target.setReg x k) is := by
      intro k value
      exact ⟨indices,related.1.setReg x k,related.2 k value⟩
    obtain ⟨s',run,⟨is,corr,holds⟩,leftEnd,rightEnd⟩ :=
      loop_simulation meaning StreamStep (MemoryStep meaning)
        (fun t s => ∃ is, Related ordinary arrays inv s t is) transfer execution equal.symm initial
    exact ⟨s',is,run,corr,holds,leftEnd⟩

#print axioms Translation.loop
end PaperCore
