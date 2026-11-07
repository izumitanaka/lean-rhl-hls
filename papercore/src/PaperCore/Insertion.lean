import PaperCore.Correspondence

namespace PaperCore

/-- Semantic assertions: proof data over the three components used in the
    paper, not additional statements or runtime state. SMT syntax/encoding
    is a separate layer and is not assumed verified here. -/
abbrev Assertion := Registers → Heap → IndexMap → Prop

def Related (ordinary : Var → Prop) (arrays : Array → Prop) (post : Assertion)
    (source : State Heap) (target : State Streams) (indices : IndexMap) : Prop :=
  Corresponds ordinary arrays source target indices ∧ post target.regs source.memory indices

/-- Strict read-insertion precondition. The existential head/tail and defined
    cell remain even when post=True. This is the explicitly approved
    definedness addition to Tr-InsRBuf, not ordinary vacuous substitution. -/
def readPre (array : Array) (buffer : Var) (post : Assertion) : Assertion :=
  fun regs heap indices => ∃ index tail value,
    indices.lookup array = some (index :: tail) ∧
    heap.lookup (array,index) = some value ∧
    post (put regs buffer value) heap (put indices array tail)

def insertRead (array : Array) (buffer : Var) : Target Op := .action (.read buffer array)

theorem readPre_nonempty (h : readPre a b post regs heap indices) :
    ∃ index tail, indices.lookup a = some (index :: tail) := by
  obtain ⟨index,tail,value,head,cell,post⟩ := h
  exact ⟨index,tail,head⟩

/-- Empty witnesses are rejected regardless of the chosen postcondition. -/
theorem readPre_rejects_empty (empty : indices.lookup a = some []) :
    ¬ readPre a b post regs heap indices := by
  intro h
  obtain ⟨index,tail,head⟩ := readPre_nonempty h
  simp [empty] at head

/-- In particular, True does not erase the approved safety condition.
    Under correspondence, its strict read precondition is exactly nonempty I. -/
theorem readPre_true_iff (corr : Corresponds ordinary arrays source target indices)
    (tracked : arrays a) :
    readPre a b (fun _ _ _ => True) target.regs source.memory indices ↔
      ∃ index tail, indices.lookup a = some (index :: tail) := by
  constructor
  · exact readPre_nonempty
  · rintro ⟨index,tail,head⟩
    obtain ⟨is,vs,hi,hv,distinct,contents⟩ := corr.streams a tracked
    rw [head] at hi
    cases Option.some.inj hi
    obtain ⟨value,rest,eq,cell,remaining⟩ := contents.read
    exact ⟨index,tail,value,head,cell,True.intro⟩

/-- A single inserted FIFO read is executable and preserves the complete
    relation, including its assertion. Source state is unchanged. -/
theorem insertRead_sound (meaning : Op → Int → Int → Int)
    (related : Related ordinary arrays (readPre a b post) source target indices)
    (tracked : arrays a) (buffer : ¬ ordinary b) :
    ∃ target' indices', TargetExec meaning (insertRead a b) target target' ∧
      Related ordinary arrays post source target' indices' := by
  obtain ⟨corresponds,index,tail,value,head,cell,postHolds⟩ := related
  obtain ⟨readValue,target',actualCell,step,regs,after⟩ :=
    corresponds.read_buffer tracked buffer head
  have same : readValue = value := Option.some.inj (actualCell.symm.trans cell)
  subst readValue
  refine ⟨target',put indices a tail,.action step,after,?_⟩
  rw [regs]
  exact postHolds

/-- Consequence for this computed precondition: implication is proved in
    Lean; a future SMT adapter must justify it rather than simply assert it. -/
theorem insertRead_sound_of_implies (meaning : Op → Int → Int → Int)
    (entails : ∀ r h i, pre r h i → readPre a b post r h i)
    (related : Related ordinary arrays pre source target indices)
    (tracked : arrays a) (buffer : ¬ ordinary b) :
    ∃ target' indices', TargetExec meaning (insertRead a b) target target' ∧
      Related ordinary arrays post source target' indices' := by
  exact insertRead_sound meaning ⟨related.1,entails _ _ _ related.2⟩ tracked buffer

/-- The index is a logical parameter, not an extra operand of the generated
    FIFO write. Definedness and freshness remain explicit for any post. -/
def writePre (a : Array) (b : Var) (index : Int) (post : Assertion) : Assertion :=
  fun regs heap indices => ∃ is value,
    indices.lookup a = some is ∧ index ∉ is ∧
    heap.lookup (a,index) = some value ∧ regs.lookup b = some value ∧
    post regs heap (put indices a (is ++ [index]))

def insertWrite (a : Array) (b : Var) : Target Op := .action (.write a b)

theorem insertWrite_sound (meaning : Op → Int → Int → Int)
    (related : Related ordinary arrays (writePre a b index post) source target indices)
    (tracked : arrays a) :
    ∃ target' indices', TargetExec meaning (insertWrite a b) target target' ∧
      Related ordinary arrays post source target' indices' := by
  obtain ⟨corresponds,is,value,witness,fresh,cell,held,postHolds⟩ := related
  obtain ⟨target',step,regs,after⟩ := corresponds.write_buffer tracked witness fresh cell held
  refine ⟨target',put indices a (is ++ [index]),.action step,after,?_⟩
  rw [regs]
  exact postHolds

/-- Determinism of the actual primitive operations, used when composing
    insertion with the backward direction of a relational proof. -/
theorem streamStep_deterministic (h : StreamStep cmd s t) (h' : StreamStep cmd s u) : t = u := by
  cases h <;> cases h' <;> simp_all

theorem insertRead_unique (meaning : Op → Int → Int → Int)
    (h : TargetExec meaning (insertRead a b) s t)
    (h' : TargetExec meaning (insertRead a b) s u) : t = u := by
  cases h with
  | action step =>
    cases h' with
    | action step' => exact streamStep_deterministic step step'

theorem insertWrite_unique (meaning : Op → Int → Int → Int)
    (h : TargetExec meaning (insertWrite a b) s t)
    (h' : TargetExec meaning (insertWrite a b) s u) : t = u := by
  cases h with
  | action step =>
    cases h' with
    | action step' => exact streamStep_deterministic step step'

#print axioms readPre_rejects_empty
#print axioms readPre_true_iff
#print axioms insertRead_sound
#print axioms insertRead_sound_of_implies
#print axioms insertWrite_sound
#print axioms insertRead_unique
end PaperCore
