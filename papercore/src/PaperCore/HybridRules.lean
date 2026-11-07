import PaperCore.HybridCorrespondence
import PaperCore.LoopRule

namespace PaperCore.Hybrid
open MixedTarget

def Related (ordinary : Var → Prop) (arrays : Array → Prop) (assertion : Assertion)
    (source : State Heap) (target : State Storage) (indices : IndexMap) : Prop :=
  Corresponds ordinary arrays source target indices ∧ assertion target.regs source.memory indices

/-- The two terminating-execution directions stated in the paper.
    This is semantic validity, not an assumed rule or a solver answer. -/
def Translation (meaning : Op → Int → Int → Int) (ordinary : Var → Prop)
    (arrays : Array → Prop) (pre : Assertion) (sourceCode : Source Op)
    (targetCode : Code Op) (post : Assertion) : Prop :=
  ∀ source target indices, Related ordinary arrays pre source target indices →
    (∀ source', SourceExec meaning sourceCode source source' →
      ∃ target' indices', Execution meaning targetCode target target' ∧
        Related ordinary arrays post source' target' indices') ∧
    (∀ target', Execution meaning targetCode target target' →
      ∃ source' indices', SourceExec meaning sourceCode source source' ∧
        Related ordinary arrays post source' target' indices')

theorem Translation.seq
    (first : Translation meaning ordinary arrays pre a ta mid)
    (second : Translation meaning ordinary arrays mid b tb post) :
    Translation meaning ordinary arrays pre (.seq a b) (.seq ta tb) post := by
  intro source target indices related
  constructor
  · intro source' run
    cases run with
    | seq ha hb =>
      obtain ⟨tm,im,hta,rm⟩ := (first _ _ _ related).1 _ ha
      obtain ⟨tt,it,htb,rt⟩ := (second _ _ _ rm).1 _ hb
      exact ⟨tt,it,.seq hta htb,rt⟩
  · intro target' run
    cases run with
    | seq ha hb =>
      obtain ⟨sm,im,hsa,rm⟩ := (first _ _ _ related).2 _ ha
      obtain ⟨st,it,hsb,rt⟩ := (second _ _ _ rm).2 _ hb
      exact ⟨st,it,.seq hsa hsb,rt⟩

theorem Translation.consequence
    (body : Translation meaning ordinary arrays pre sourceCode targetCode post)
    (before : ∀ r h i, pre' r h i → pre r h i)
    (after : ∀ r h i, post r h i → post' r h i) :
    Translation meaning ordinary arrays pre' sourceCode targetCode post' := by
  intro source target indices related
  have initial : Related ordinary arrays pre source target indices :=
    ⟨related.1,before _ _ _ related.2⟩
  constructor
  · intro source' run
    obtain ⟨tt,it,ht,rt⟩ := (body _ _ _ initial).1 _ run
    exact ⟨tt,it,ht,rt.1,after _ _ _ rt.2⟩
  · intro target' run
    obtain ⟨ss,is,hs,rs⟩ := (body _ _ _ initial).2 _ run
    exact ⟨ss,is,hs,rs.1,after _ _ _ rs.2⟩

theorem assign_valid (meaning : Op → Int → Int → Int) (typed : e.ordinary ordinary) :
    Translation meaning ordinary arrays (assignPre meaning x e post)
      (.assign x e) (.assign x e) post := by
  intro source target indices related
  obtain ⟨corr,pre⟩ := related
  have equal := corr.eval_eq meaning e typed
  constructor
  · intro source' run
    cases run with
    | assign value =>
      have targetValue := equal ▸ value
      exact ⟨_,indices,.assign targetValue,corr.setReg x _,pre _ targetValue⟩
  · intro target' run
    cases run with
    | assign value =>
      have sourceValue := equal.symm ▸ value
      exact ⟨_,indices,.assign sourceValue,corr.setReg x _,pre _ value⟩

theorem Translation.branch (typed : ordinary x)
    (yes : Translation meaning ordinary arrays (trueGuard pre x) a ta post)
    (no : Translation meaning ordinary arrays (falseGuard pre x) b tb post) :
    Translation meaning ordinary arrays pre (.branch x a b) (.branch x ta tb) post := by
  intro source target indices related
  have equal := related.1.registers x typed
  constructor
  · intro source' run
    cases run with
    | ifTrue value nonzero body =>
      have targetValue := equal ▸ value
      obtain ⟨tt,it,ht,rt⟩ := (yes _ _ _ ⟨related.1,related.2,_,targetValue,nonzero⟩).1 _ body
      exact ⟨tt,it,.ifTrue targetValue nonzero ht,rt⟩
    | ifFalse value body =>
      have targetValue := equal ▸ value
      obtain ⟨tt,it,ht,rt⟩ := (no _ _ _ ⟨related.1,related.2,targetValue⟩).1 _ body
      exact ⟨tt,it,.ifFalse targetValue ht,rt⟩
  · intro target' run
    cases run with
    | ifTrue value nonzero body =>
      have sourceValue := equal.symm ▸ value
      obtain ⟨ss,is,hs,rs⟩ := (yes _ _ _ ⟨related.1,related.2,_,value,nonzero⟩).2 _ body
      exact ⟨ss,is,.ifTrue sourceValue nonzero hs,rs⟩
    | ifFalse value body =>
      have sourceValue := equal.symm ▸ value
      obtain ⟨ss,is,hs,rs⟩ := (no _ _ _ ⟨related.1,related.2,value⟩).2 _ body
      exact ⟨ss,is,.ifFalse sourceValue hs,rs⟩

/-- The execution part of Tr-Kernel. Array-role flipping belongs to the
    typing/derivation layer; this lemma does not silently omit that premise. -/
theorem Translation.kernel
    (body : Translation meaning ordinary arrays pre sourceCode targetCode post) :
    Translation meaning ordinary arrays pre (.kernel sourceCode) (.kernel targetCode) post := by
  intro source target indices related
  constructor
  · intro source' run
    cases run with
    | kernel h =>
      obtain ⟨tt,it,ht,rt⟩ := (body _ _ _ related).1 _ h
      exact ⟨tt,it,.kernel ht,rt⟩
  · intro target' run
    cases run with
    | kernel h =>
      obtain ⟨ss,is,hs,rs⟩ := (body _ _ _ related).2 _ h
      exact ⟨ss,is,.kernel hs,rs⟩

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
        ∃ t', Execution meaning targetBody t t' ∧
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
      loop_simulation meaning (MemoryStep meaning) (Step meaning)
        (fun s t => ∃ is, Related ordinary arrays inv s t is) transfer execution equal initial
    exact ⟨t',is,run,corr,holds,rightEnd⟩
  · intro target' execution
    have transfer : ∀ t s,
        (∃ is, Related ordinary arrays inv s t is) →
        ∀ k, t.regs.lookup x = some k → k ≠ stop →
        ∀ t', Execution meaning targetBody t t' →
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
      loop_simulation meaning (Step meaning) (MemoryStep meaning)
        (fun t s => ∃ is, Related ordinary arrays inv s t is) transfer execution equal.symm initial
    exact ⟨s',is,run,corr,holds,leftEnd⟩


#print axioms Translation.loop
end PaperCore.Hybrid
