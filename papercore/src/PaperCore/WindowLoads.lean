import PaperCore.BufferView
import PaperCore.IndexSequence

namespace PaperCore.WindowLoads

/-- The contiguous window represented by scalar buffer registers. -/
def Held (heap : Heap) (regs : Registers) (array : Array) (first : Int) : List Var → Prop
  | [] => True
  | buffer :: rest => ∃ value, heap.lookup (array,first) = some value ∧
      regs.lookup buffer = some value ∧ Held heap regs array (first+1) rest

/-- An observation of the generated sequence of ordinary FIFO commands. -/
inductive Reads (array : Array) : List Var → State Streams → State Streams → Prop where
  | nil : Reads array [] s s
  | cons : StreamStep (.read buffer array) s mid → Reads array rest mid out →
      Reads array (buffer :: rest) s out

def prepend (array : Array) (buffers : List Var) (body : Target Op) : Target Op :=
  buffers.foldr (fun buffer rest => .seq (.action (.read buffer array)) rest) body

theorem prepend_exec : TargetExec meaning (prepend array buffers body) state out ↔
    ∃ mid, Reads array buffers state mid ∧ TargetExec meaning body mid out := by
  induction buffers generalizing state with
  | nil =>
    constructor
    · intro run; exact ⟨state,.nil,run⟩
    · rintro ⟨mid,reads,run⟩; cases reads; exact run
  | cons buffer rest ih =>
    constructor
    · intro run
      cases run with
      | seq first last =>
        cases first with
        | action step =>
          obtain ⟨mid,reads,bodyRun⟩ := ih.mp last
          exact ⟨mid,.cons step reads,bodyRun⟩
    · rintro ⟨mid,reads,bodyRun⟩
      cases reads with
      | cons step later => exact .seq (.action step) (ih.mpr ⟨mid,later,bodyRun⟩)

theorem Reads.frame (run : Reads array buffers state out) (other : x ∉ buffers) :
    out.regs.lookup x = state.regs.lookup x := by
  induction run with
  | nil => rfl
  | @cons buffer s mid rest out step later ih =>
    have facts : x ≠ buffer ∧ x ∉ rest := by simpa using other
    have after := ih facts.2
    cases step
    exact after.trans (lookup_put_other _ _ _ _ facts.1)

theorem load_exists_framed (buffers : List Var)
    (corr : Corresponds ordinary arrays source target indices)
    (tracked : arrays array)
    (fresh : ∀ b ∈ buffers, ¬ ordinary b)
    (distinct : buffers.Nodup)
    (witness : indices.lookup array = some (IndexSequence.entries first 1 buffers.length ++ tail)) :
    ∃ out afterIndices, Reads array buffers target out ∧
      Corresponds ordinary arrays source out afterIndices ∧
      afterIndices.lookup array = some tail ∧ Held source.memory out.regs array first buffers ∧
      (∀ other, other ≠ array → afterIndices.lookup other = indices.lookup other) := by
  induction buffers generalizing first target indices with
  | nil => exact ⟨target,indices,.nil,corr,witness,True.intro,by intros; rfl⟩
  | cons buffer rest ih =>
    have front : indices.lookup array = some (first :: (IndexSequence.entries (first+1) 1 rest.length ++ tail)) := by
      simpa [IndexSequence.entries] using witness
    obtain ⟨value,mid,cell,step,regs,after⟩ := corr.read_buffer tracked (fresh buffer (by simp)) front
    obtain ⟨out,afterIndices,later,finished,endQueue,heldRest,frameRest⟩ :=
      ih after (fun b hb => fresh b (List.mem_cons_of_mem _ hb)) (List.nodup_cons.mp distinct).2
        (first := first+1) (lookup_put_same ..)
    have headValue : out.regs.lookup buffer = some value := by
      rw [later.frame (List.nodup_cons.mp distinct).1,regs]
      exact lookup_put_same ..
    refine ⟨out,afterIndices,.cons step later,finished,endQueue,⟨value,cell,headValue,heldRest⟩,?_⟩
    intro other different
    simpa only [lookup_put_other _ _ _ _ different] using frameRest other different

theorem load_exists (buffers : List Var)
    (corr : Corresponds ordinary arrays source target indices)
    (tracked : arrays array) (fresh : ∀ b ∈ buffers, ¬ ordinary b)
    (distinct : buffers.Nodup)
    (witness : indices.lookup array = some (IndexSequence.entries first 1 buffers.length ++ tail)) :
    ∃ out afterIndices, Reads array buffers target out ∧
      Corresponds ordinary arrays source out afterIndices ∧
      afterIndices.lookup array = some tail ∧ Held source.memory out.regs array first buffers := by
  obtain ⟨out,after,reads,corrAfter,queue,held,_⟩ := load_exists_framed buffers corr tracked fresh distinct witness
  exact ⟨out,after,reads,corrAfter,queue,held⟩

theorem Reads.deterministic (first : Reads array buffers state left)
    (second : Reads array buffers state right) : left = right := by
  induction first generalizing right with
  | nil => cases second; rfl
  | cons head tail ih =>
    cases second with
    | cons otherHead otherTail =>
      have same := streamStep_deterministic head otherHead
      subst_vars
      exact ih otherTail

theorem entries_split (first : Int) (left right : Nat) :
    IndexSequence.entries first 1 (left+right) =
      IndexSequence.entries first 1 left ++ IndexSequence.entries (first+(left:Int)) 1 right := by
  induction left generalizing first with
  | zero => simp [IndexSequence.entries]
  | succ n ih =>
    simp only [Nat.succ_add,IndexSequence.entries,List.cons_append]
    rw [ih]
    congr 2
    congr 1
    omega

#print axioms prepend_exec
#print axioms load_exists
end PaperCore.WindowLoads
