import PaperCore.BufferView
import PaperCore.AtomicRules

namespace PaperCore.DirectBody
open AccessAnalysis

/-- Shared logical queue transitions and atomic correspondence, not a compiler. -/
def consumeOne (indices : IndexMap) (access : Access) : Option IndexMap := do
  let values ← indices.lookup access.array
  match access.direction with
  | .read =>
    let head :: tail := values | none
    if head = access.index then some (put indices access.array tail) else none
  | .write =>
    if access.index ∈ values then none else some (put indices access.array (values ++ [access.index]))

def consume (indices : IndexMap) : List Access → Option IndexMap
  | [] => some indices
  | event :: rest => do consume (← consumeOne indices event) rest

theorem consume_append (first second : List Access) (indices : IndexMap) :
    consume indices (first ++ second) = (consume indices first).bind (fun mid => consume mid second) := by
  induction first generalizing indices with
  | nil => rfl
  | cons event rest ih =>
    simp only [List.cons_append,consume]
    cases he : consumeOne indices event <;> simp [ih]

theorem consume_read (success : consume indices [⟨.read,array,index⟩] = some finalIndices) :
    ∃ tail, indices.lookup array = some (index :: tail) ∧ finalIndices = put indices array tail := by
  cases hi : indices.lookup array with
  | none => simp [consume,consumeOne,hi] at success
  | some values =>
    cases values with
    | nil => simp [consume,consumeOne,hi] at success
    | cons head tail =>
      by_cases same : head = index
      · subst head
        simp [consume,consumeOne,hi] at success
        exact ⟨tail,rfl,success.symm⟩
      · simp [consume,consumeOne,hi,same] at success

theorem consume_write (success : consume indices [⟨.write,array,index⟩] = some finalIndices) :
    ∃ values, indices.lookup array = some values ∧ index ∉ values ∧ finalIndices = put indices array (values ++ [index]) := by
  cases hi : indices.lookup array with
  | none => simp [consume,consumeOne,hi] at success
  | some values =>
    by_cases member : index ∈ values
    · simp [consume,consumeOne,hi,member] at success
    · simp [consume,consumeOne,hi,member] at success
      exact ⟨values,rfl,member,success.symm⟩

theorem consume_frame (events : List Access)
    (other : ∀ event ∈ events, array ≠ event.array)
    (success : consume indices events = some afterIndices) :
    afterIndices.lookup array = indices.lookup array := by
  induction events generalizing indices with
  | nil => simp [consume] at success; subst afterIndices; rfl
  | cons event rest ih =>
    cases hc : consumeOne indices event with
    | none => simp [consume,hc] at success
    | some mid =>
      have stepFrame : mid.lookup array = indices.lookup array := by
        cases found : indices.lookup event.array with
        | none => simp [consumeOne,found] at hc
        | some values =>
          cases hd : event.direction with
          | write =>
            by_cases member : event.index ∈ values
            · simp [consumeOne,found,hd,member] at hc
            · simp [consumeOne,found,hd,member] at hc
              subst mid
              exact lookup_put_other _ _ _ _ (other event (by simp))
          | read =>
            cases values with
            | nil => simp [consumeOne,found,hd] at hc
            | cons head tail =>
              by_cases same : head = event.index
              · simp [consumeOne,found,hd,same] at hc
                subst mid
                exact lookup_put_other _ _ _ _ (other event (by simp))
              · simp [consumeOne,found,hd,same] at hc
      have restRun : consume mid rest = some afterIndices := by simpa [consume,hc] using success
      exact (ih (fun e he => other e (List.mem_cons_of_mem _ he)) restRun).trans stepFrame

theorem pop_ordinary (corr : Corresponds ordinary arrays left right indices) (tracked : arrays array)
    (head : indices.lookup array = some (index :: tail)) (dest : Var) :
    ∃ value rest, left.memory.lookup (array,index) = some value ∧
      right.memory.lookup array = some (value :: rest) ∧
      Corresponds ordinary arrays (left.setReg dest value)
        {regs := put right.regs dest value, memory := put right.memory array rest}
        (put indices array tail) := by
  obtain ⟨js,vs,hj,hv,distinct,contents⟩ := corr.streams array tracked
  have same : js = index :: tail := Option.some.inj (hj.symm.trans head)
  subst js
  obtain ⟨value,rest,values,cell,remaining⟩ := contents.read
  subst vs
  refine ⟨value,rest,cell,hv,?_⟩
  constructor
  · intro x hx
    by_cases same : x = dest
    · subst x; simp [State.setReg]
    · simpa [State.setReg,lookup_put_other _ _ _ _ same] using corr.registers x hx
  · intro other isTracked
    by_cases same : other = array
    · subst other
      exact ⟨tail,rest,lookup_put_same ..,lookup_put_same ..,(List.nodup_cons.mp distinct).2,remaining⟩
    · obtain ⟨is,ws,hi,hw,hd,hc⟩ := corr.streams other isTracked
      exact ⟨is,ws,by simpa [lookup_put_other _ _ _ _ same] using hi,
        by simpa [lookup_put_other _ _ _ _ same] using hw,hd,hc⟩

theorem push_ordinary (corr : Corresponds ordinary arrays left right indices) (tracked : arrays array)
    (witness : indices.lookup array = some values) (fresh : index ∉ values)
    (originOrdinary : ordinary origin)
    (value : left.regs.lookup origin = some v) :
    ∃ out, StreamStep (.write array origin) right out ∧
      Corresponds ordinary arrays {left with memory := put left.memory (array,index) v} out
        (put indices array (values ++ [index])) := by
  have stored : Corresponds ordinary arrays {left with memory := put left.memory (array,index) v} right indices := by
    constructor
    · exact corr.registers
    · intro other isTracked
      obtain ⟨js,vs,hj,hv,distinct,contents⟩ := corr.streams other isTracked
      refine ⟨js,vs,hj,hv,distinct,contents.congr ?_⟩
      intro i member
      have different : (other,i) ≠ (array,index) := by
        intro same
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj same
        have equal := Option.some.inj (hj.symm.trans witness)
        subst js
        exact fresh member
      exact lookup_put_other _ _ _ _ different
  obtain ⟨out,step,_,after⟩ := stored.write_buffer tracked witness fresh (lookup_put_same ..)
    ((corr.registers origin originOrdinary).symm.trans value)
  exact ⟨out,step,after⟩


end PaperCore.DirectBody
