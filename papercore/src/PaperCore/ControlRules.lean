import PaperCore.AtomicRules

namespace PaperCore

/-- Semantic substitution on successful evaluation. Unlike target-only
    insertion, corresponding assignments need not be forced to execute:
    when e is undefined on one side it is undefined on both sides. -/
def assignPre (meaning : Op → Int → Int → Int) (x : Var) (e : Expr Op)
    (post : Assertion) : Assertion :=
  fun regs heap indices => ∀ v, e.eval meaning regs = some v →
    post (put regs x v) heap indices

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

def trueGuard (pre : Assertion) (x : Var) : Assertion :=
  fun regs heap indices => pre regs heap indices ∧ ∃ v, regs.lookup x = some v ∧ v ≠ 0

def falseGuard (pre : Assertion) (x : Var) : Assertion :=
  fun regs heap indices => pre regs heap indices ∧ regs.lookup x = some 0

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

#print axioms assign_valid
#print axioms Translation.branch
#print axioms Translation.kernel
end PaperCore
