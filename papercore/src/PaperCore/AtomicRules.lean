import PaperCore.Rules
import PaperCore.ReadMem

namespace PaperCore

theorem memoryStep_deterministic (h : MemoryStep meaning cmd s t)
    (h' : MemoryStep meaning cmd s u) : t = u := by
  cases h <;> cases h' <;> simp_all

theorem memoryAction_unique (h : SourceExec meaning (.action cmd) s t)
    (h' : SourceExec meaning (.action cmd) s u) : t = u := by
  cases h with
  | action step =>
    cases h' with
    | action step' => exact memoryStep_deterministic step step'

theorem assign_unique (h : Exec meaning action (.assign x e) s t)
    (h' : Exec meaning action (.assign x e) s u) : t = u := by
  cases h <;> cases h' <;> simp_all

/-- Semantic interpretation of b=a[e] AND [b/x]Q. Definedness is included
    in the equality, as required by the paper's partial-term convention. -/
def readMemPre (meaning : Op → Int → Int → Int) (dest : Var) (a : Array)
    (e : Expr Op) (b : Var) (post : Assertion) : Assertion :=
  fun regs heap indices => ∃ index value,
    e.eval meaning regs = some index ∧ heap.lookup (a,index) = some value ∧
    regs.lookup b = some value ∧ post (put regs dest value) heap indices

/-- Tr-ReadMem with both execution directions and the assertion component.
    The generated code is the actual pure function readMem. -/
theorem readMem_valid (meaning : Op → Int → Int → Int) (typed : e.ordinary ordinary) :
    Translation meaning ordinary arrays (readMemPre meaning dest a e b post)
      (.action (.read dest a e)) (readMem dest b) post := by
  intro source target indices related
  obtain ⟨corr,index,value,address,cell,held,postHolds⟩ := related
  have sourceAddress : e.eval meaning source.regs = some index := by
    rw [corr.eval_eq meaning e typed]
    exact address
  obtain ⟨hs,ht,after⟩ := readMem_correct meaning corr sourceAddress cell held (dest := dest)
  have full : Related ordinary arrays post (source.setReg dest value)
      (target.setReg dest value) indices := ⟨after,postHolds⟩
  constructor
  · intro source' run
    have same := memoryAction_unique run hs
    subst source'
    exact ⟨_,indices,ht,full⟩
  · intro target' run
    have same := assign_unique run ht
    subst target'
    exact ⟨_,indices,hs,full⟩

/-- The first concrete buffered-read transformer in the minimal core. No
    peek, flag, allocation or extra source constructor is involved. -/
def bufferedRead (dest : Var) (a : Array) (b : Var) : Target Op :=
  .seq (insertRead a b) (readMem dest b)

/-- The generated precondition requires a nonempty FIFO AND that its saved
    head represents the source read's index. The implication can later be
    discharged by a verified VC generator/SMT connection. -/
theorem bufferedRead_valid (meaning : Op → Int → Int → Int)
    (typed : e.ordinary ordinary) (tracked : arrays a) (buffer : ¬ ordinary b) :
    Translation meaning ordinary arrays
      (readPre a b (readMemPre meaning dest a e b post))
      (.action (.read dest a e)) (bufferedRead dest a b) post := by
  exact Translation.insertLeft (insertRead_valid meaning tracked buffer)
    (readMem_valid meaning typed)

#print axioms readMem_valid
#print axioms bufferedRead_valid
end PaperCore
