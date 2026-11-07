import PaperCore.AtomicRules

namespace PaperCore

def movePre (dest source : Var) (post : Assertion) : Assertion :=
  fun regs heap indices => ∃ value, regs.lookup source = some value ∧
    post (put regs dest value) heap indices

def insertMove (dest source : Var) : Target Op := .assign dest (.var source)

theorem movePre_rejects_undefined (missing : regs.lookup source = none) :
    ¬ movePre dest source post regs heap indices := by
  rintro ⟨value,existsValue,postHolds⟩
  simp [missing] at existsValue

theorem movePre_true_iff :
    movePre dest source (fun _ _ _ => True) regs heap indices ↔
      ∃ value, regs.lookup source = some value := by
  simp [movePre]

theorem Corresponds.setBuffer (corr : Corresponds ordinary arrays source target indices)
    (buffer : ¬ ordinary b) (value : Int) :
    Corresponds ordinary arrays source (target.setReg b value) indices := by
  constructor
  · intro x typed
    have ne : x ≠ b := by intro eq; subst x; exact buffer typed
    simpa [State.setReg,lookup_put_other _ _ _ _ ne] using corr.registers x typed
  · exact corr.streams

theorem insertMove_valid (meaning : Op → Int → Int → Int) (buffer : ¬ ordinary dest) :
    Insertion meaning ordinary arrays (movePre dest origin post) (insertMove dest origin) post := by
  intro source target indices related
  obtain ⟨corr,value,defined,postHolds⟩ := related
  have executed : TargetExec meaning (insertMove dest origin) target (target.setReg dest value) :=
    .assign defined
  refine ⟨target.setReg dest value,indices,executed,⟨corr.setBuffer buffer value,postHolds⟩,?_⟩
  intro other execution
  exact assign_unique execution executed

theorem Insertion.seq
    (first : Insertion meaning ordinary arrays pre a mid)
    (second : Insertion meaning ordinary arrays mid b post) :
    Insertion meaning ordinary arrays pre (.seq a b) post := by
  intro source target indices related
  obtain ⟨tm,im,ha,rm,uniqueA⟩ := first _ _ _ related
  obtain ⟨tt,it,hb,rt,uniqueB⟩ := second _ _ _ rm
  refine ⟨tt,it,.seq ha hb,rt,?_⟩
  intro other run
  cases run with
  | seq ra rb =>
    have same := uniqueA _ ra
    subst_vars
    exact uniqueB _ rb

theorem Insertion.consequence
    (body : Insertion meaning ordinary arrays pre code post)
    (before : ∀ r h i, pre' r h i → pre r h i)
    (after : ∀ r h i, post r h i → post' r h i) :
    Insertion meaning ordinary arrays pre' code post' := by
  intro source target indices related
  obtain ⟨tt,it,run,rt,unique⟩ := body _ _ _ ⟨related.1,before _ _ _ related.2⟩
  exact ⟨tt,it,run,⟨rt.1,after _ _ _ rt.2⟩,unique⟩

#print axioms movePre_rejects_undefined
#print axioms insertMove_valid
#print axioms Insertion.seq
#print axioms Insertion.consequence
end PaperCore
