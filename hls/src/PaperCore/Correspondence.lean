import PaperCore.Semantics

namespace PaperCore

@[simp] theorem lookup_put_same [BEq K] [LawfulBEq K]
    (entries : List (K × V)) (key : K) (value : V) :
    (put entries key value).lookup key = some value := by
  simp [put,List.lookup]

theorem lookup_put_other [BEq K] [LawfulBEq K]
    (entries : List (K × V)) (key query : K) (value : V) (ne : query ≠ key) :
    (put entries key value).lookup query = entries.lookup query := by
  have hn : (query == key) = false := beq_eq_false_iff_ne.mpr ne
  induction entries with
  | nil => simp [put,List.lookup,ne,hn]
  | cons entry rest ih =>
    obtain ⟨k,v⟩ := entry
    by_cases hk : k = key
    · subst k
      simpa [put,List.lookup,ne,hn] using ih
    · have hkn : (k == key) = false := beq_eq_false_iff_ne.mpr hk
      by_cases hq : query = k
      · subst query
        simp [put,List.lookup,hk,hn,hkn]
      · have hqn : (query == k) = false := beq_eq_false_iff_ne.mpr hq
        simpa [put,List.lookup,hn,hkn,hqn] using ih

/-- Exact content correspondence, including the equal-length condition
    approved by the user. Undefined source cells cannot represent FIFO data.
    This is proof data, not an extension of either program language. -/
inductive Contents (heap : Int → Option Int) : List Int → List Int → Prop where
  | nil : Contents heap [] []
  | cons (cell : heap index = some value) (rest : Contents heap indices values) :
      Contents heap (index :: indices) (value :: values)

namespace Contents

theorem length_eq (h : Contents heap indices values) : indices.length = values.length := by
  induction h with
  | nil => rfl
  | cons cell rest ih => simpa using ih

theorem defined (h : Contents heap indices values) (member : index ∈ indices) :
    ∃ value, heap index = some value := by
  induction h with
  | nil => simp at member
  | cons cell rest ih =>
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · exact ⟨_,cell⟩
    · exact ih member

/-- A source index at the head has a matching physical FIFO head. -/
theorem read (h : Contents heap (index :: indices) values) :
    ∃ value tail, values = value :: tail ∧ heap index = some value ∧ Contents heap indices tail := by
  cases h with
  | cons cell rest => exact ⟨_,_,rfl,cell,rest⟩

theorem append (h : Contents heap indices values) (cell : heap index = some value) :
    Contents heap (indices ++ [index]) (values ++ [value]) := by
  induction h with
  | nil => exact .cons cell .nil
  | cons head rest ih => exact .cons head ih

/-- Used by Tr-WriteMem: changing a source cell outside I does not change
    any value currently represented by the FIFO. -/
theorem congr (h : Contents heap indices values)
    (same : ∀ index ∈ indices, heap' index = heap index) : Contents heap' indices values := by
  induction h with
  | nil => exact .nil
  | @cons index value indices values cell rest ih =>
    apply Contents.cons
    · rw [same index (by simp),cell]
    · exact ih (fun i hi => same i (by simp [hi]))

theorem update_unrepresented (h : Contents heap indices values) (fresh : index ∉ indices) :
    Contents (fun i => if i = index then some value else heap i) indices values := by
  apply h.congr
  intro i hi
  have ne : i ≠ index := by intro eq; subst i; exact fresh hi
  simp [ne]

end Contents

abbrev IndexMap := List (Array × List Int)

/-- The structural part of the paper's state relation. Assertions will be
    interpreted over target registers, the source heap and these witnesses.
    Ordinary/buffer and array roles are supplied by the typing environment;
    no target buffer is required to exist as a source register. -/
structure Corresponds (ordinary : Var → Prop) (arrays : Array → Prop)
    (source : State Heap) (target : State Streams) (indices : IndexMap) : Prop where
  registers : ∀ x, ordinary x → source.regs.lookup x = target.regs.lookup x
  streams : ∀ a, arrays a → ∃ is vs,
    indices.lookup a = some is ∧ target.memory.lookup a = some vs ∧
    is.Nodup ∧ Contents (fun i => source.memory.lookup (a,i)) is vs

/-- Tr-InsRBuf at the actual primitive command: the FIFO read exists,
    returns the source cell, and leaves the tail correspondence. -/
theorem read_buffer {source : State Heap} {target : State Streams} (h : Contents (fun i => source.memory.lookup (a,i)) (index :: indices) values)
    (queue : target.memory.lookup a = some values) :
    ∃ value tail,
      source.memory.lookup (a,index) = some value ∧
      StreamStep (.read buffer a) target
        {regs := put target.regs buffer value, memory := put target.memory a tail} ∧
      Contents (fun i => source.memory.lookup (a,i)) indices tail := by
  obtain ⟨value,tail,rfl,cell,rest⟩ := h.read
  exact ⟨value,tail,cell,StreamStep.read queue,rest⟩

/-- Tr-InsWBuf at the actual primitive command, with the explicit I update.
    Equal lengths are enforced by Contents; no arbitrary FIFO suffix remains. -/
theorem write_buffer {source : State Heap} {target : State Streams} (h : Contents (fun i => source.memory.lookup (a,i)) indices values)
    (queue : target.memory.lookup a = some values)
    (cell : source.memory.lookup (a,index) = some value)
    (bufferValue : target.regs.lookup buffer = some value)
    (distinct : indices.Nodup) (fresh : index ∉ indices) :
    StreamStep (.write a buffer) target
      {target with memory := put target.memory a (values ++ [value])} ∧
    (indices ++ [index]).Nodup ∧
    Contents (fun i => source.memory.lookup (a,i)) (indices ++ [index]) (values ++ [value]) := by
  refine ⟨StreamStep.write queue bufferValue,?_,h.append cell⟩
  apply List.nodup_append.mpr
  refine ⟨distinct,by simp,?_⟩
  intro i hi j hj eq
  simp only [List.mem_singleton] at hj
  subst j
  subst i
  exact fresh hi

/-- Full structural state correspondence after Tr-InsRBuf. The register
    receiving the head is a buffer, not an ordinary source variable. -/
theorem Corresponds.read_buffer
    (h : Corresponds ordinary arrays source target indices)
    (tracked : arrays a) (buffer : ¬ ordinary b)
    (head : indices.lookup a = some (index :: tail)) :
    ∃ value target',
      source.memory.lookup (a,index) = some value ∧
      StreamStep (.read b a) target target' ∧
      target'.regs = put target.regs b value ∧
      Corresponds ordinary arrays source target' (put indices a tail) := by
  obtain ⟨is,vs,hi,hv,distinct,contents⟩ := h.streams a tracked
  rw [head] at hi
  cases Option.some.inj hi
  obtain ⟨value,rest,rfl,cell,remaining⟩ := contents.read
  refine ⟨value,{regs := put target.regs b value, memory := put target.memory a rest},
    cell,StreamStep.read hv,rfl,?_⟩
  constructor
  · intro x ordinaryX
    have ne : x ≠ b := by intro eq; subst x; exact buffer ordinaryX
    rw [lookup_put_other _ _ _ _ ne]
    exact h.registers x ordinaryX
  · intro other trackedOther
    by_cases same : other = a
    · subst other
      exact ⟨tail,rest,lookup_put_same ..,lookup_put_same ..,
        (List.nodup_cons.mp distinct).2,remaining⟩
    · obtain ⟨js,ws,hj,hw,hd,hc⟩ := h.streams other trackedOther
      exact ⟨js,ws,by simpa [lookup_put_other _ _ _ _ same] using hj,
        by simpa [lookup_put_other _ _ _ _ same] using hw,hd,hc⟩

/-- Full structural correspondence after Tr-InsWBuf, updating only the
    selected array's index witness; ordinary registers stay unchanged. -/
theorem Corresponds.write_buffer
    (h : Corresponds ordinary arrays source target indices)
    (tracked : arrays a) (witness : indices.lookup a = some is)
    (fresh : index ∉ is) (cell : source.memory.lookup (a,index) = some value)
    (held : target.regs.lookup b = some value) :
    ∃ target', StreamStep (.write a b) target target' ∧ target'.regs = target.regs ∧
      Corresponds ordinary arrays source target' (put indices a (is ++ [index])) := by
  obtain ⟨js,vs,hj,hv,distinct,contents⟩ := h.streams a tracked
  rw [witness] at hj
  cases Option.some.inj hj
  obtain ⟨step,nodup,remaining⟩ := PaperCore.write_buffer contents hv cell held distinct fresh
  refine ⟨{target with memory := put target.memory a (vs ++ [value])},step,rfl,?_⟩
  constructor
  · exact h.registers
  · intro other trackedOther
    by_cases same : other = a
    · subst other
      exact ⟨is ++ [index],vs ++ [value],lookup_put_same ..,lookup_put_same ..,nodup,remaining⟩
    · obtain ⟨ks,ws,hk,hw,hd,hc⟩ := h.streams other trackedOther
      exact ⟨ks,ws,by simpa [lookup_put_other _ _ _ _ same] using hk,
        by simpa [lookup_put_other _ _ _ _ same] using hw,hd,hc⟩

#print axioms Contents.length_eq
#print axioms Contents.update_unrepresented
#print axioms read_buffer
#print axioms write_buffer
#print axioms Corresponds.read_buffer
#print axioms Corresponds.write_buffer
end PaperCore
