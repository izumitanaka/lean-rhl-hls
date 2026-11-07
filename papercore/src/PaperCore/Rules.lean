import PaperCore.Insertion

namespace PaperCore

/-- The two terminating-execution directions stated in the paper.
    This is semantic validity, not an assumed rule or a solver answer. -/
def Translation (meaning : Op → Int → Int → Int) (ordinary : Var → Prop)
    (arrays : Array → Prop) (pre : Assertion) (sourceCode : Source Op)
    (targetCode : Target Op) (post : Assertion) : Prop :=
  ∀ source target indices, Related ordinary arrays pre source target indices →
    (∀ source', SourceExec meaning sourceCode source source' →
      ∃ target' indices', TargetExec meaning targetCode target target' ∧
        Related ordinary arrays post source' target' indices') ∧
    (∀ target', TargetExec meaning targetCode target target' →
      ∃ source' indices', SourceExec meaning sourceCode source source' ∧
        Related ordinary arrays post source' target' indices')

/-- An inserted target command must execute, preserve the relation, and have
    a unique result. This is essential even if its postcondition is True. -/
def Insertion (meaning : Op → Int → Int → Int) (ordinary : Var → Prop)
    (arrays : Array → Prop) (pre : Assertion) (code : Target Op) (post : Assertion) : Prop :=
  ∀ source target indices, Related ordinary arrays pre source target indices →
    ∃ target' indices', TargetExec meaning code target target' ∧
      Related ordinary arrays post source target' indices' ∧
      ∀ other, TargetExec meaning code target other → other = target'

theorem insertRead_valid (meaning : Op → Int → Int → Int)
    (tracked : arrays a) (buffer : ¬ ordinary b) :
    Insertion meaning ordinary arrays (readPre a b post) (insertRead a b) post := by
  intro source target indices related
  obtain ⟨target',indices',run,after⟩ := insertRead_sound meaning related tracked buffer
  exact ⟨target',indices',run,after,fun _ other => insertRead_unique meaning other run⟩

theorem insertWrite_valid (meaning : Op → Int → Int → Int) (tracked : arrays a) :
    Insertion meaning ordinary arrays (writePre a b index post) (insertWrite a b) post := by
  intro source target indices related
  obtain ⟨target',indices',run,after⟩ := insertWrite_sound meaning related tracked
  exact ⟨target',indices',run,after,fun _ other => insertWrite_unique meaning other run⟩

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

/-- Tr-InsertL, including the backward direction. -/
theorem Translation.insertLeft
    (insert : Insertion meaning ordinary arrays pre beforeCode mid)
    (body : Translation meaning ordinary arrays mid sourceCode targetCode post) :
    Translation meaning ordinary arrays pre sourceCode (.seq beforeCode targetCode) post := by
  intro source target indices related
  obtain ⟨tm,im,hprefix,rm,unique⟩ := insert _ _ _ related
  constructor
  · intro source' run
    obtain ⟨tt,it,hbody,rt⟩ := (body _ _ _ rm).1 _ run
    exact ⟨tt,it,.seq hprefix hbody,rt⟩
  · intro target' run
    cases run with
    | seq hp hb =>
      have same := unique _ hp
      subst_vars
      exact (body _ _ _ rm).2 _ hb

/-- Tr-InsertR, including the backward direction. -/
theorem Translation.insertRight
    (body : Translation meaning ordinary arrays pre sourceCode targetCode mid)
    (insert : Insertion meaning ordinary arrays mid suffix post) :
    Translation meaning ordinary arrays pre sourceCode (.seq targetCode suffix) post := by
  intro source target indices related
  constructor
  · intro source' run
    obtain ⟨tm,im,hbody,rm⟩ := (body _ _ _ related).1 _ run
    obtain ⟨tt,it,hsuffix,rt,unique⟩ := insert _ _ _ rm
    exact ⟨tt,it,.seq hbody hsuffix,rt⟩
  · intro target' run
    cases run with
    | seq hb hs =>
      obtain ⟨sm,im,hsource,rm⟩ := (body _ _ _ related).2 _ hb
      obtain ⟨tt,it,hsuffix,rt,unique⟩ := insert _ _ _ rm
      have same := unique _ hs
      subst_vars
      exact ⟨sm,it,hsource,rt⟩

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

#print axioms insertRead_valid
#print axioms Translation.seq
#print axioms Translation.insertLeft
#print axioms Translation.insertRight
#print axioms Translation.consequence
end PaperCore
