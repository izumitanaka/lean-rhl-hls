import IRComparison.Circuit.Pipelining.Reuse
import IRComparison.Circuit.Pipelining.Word

namespace IRComparison.Circuit.Pipelining

abbrev Batches (α : Type := Expr) := List (List (Action α))

section Generic
variable {α : Type} [ExpressionEvaluation α] [ExpressionDependencies α]
variable {code : Array (Action α)}

def batches (code : Array (Action α)) (cycles : Cycles) : Batches α := cycles.map (List.map (actionAt code))

def runBatches (cap : Nat → Nat) : Batches α → Payload → Option Payload
  | [],p => some p
  | as :: rest,p => (clock cap as p).bind (runBatches cap rest)

theorem runBatches_eq (cycles : Cycles) :
    runBatches cap (batches code cycles) = runCycles cap code cycles := by
  induction cycles with
  | nil => rfl
  | cons ids rest ih =>
    simp only [batches] at ih
    funext p; simp only [batches,List.map_cons,runBatches,runCycles,ih]

end Generic

def liveIn : Batches → List Nat
  | [] => []
  | as :: rest => (liveBefore as (liveIn rest)).eraseDups

def reuseSafe (m : Nat → Nat) : Batches → Bool
  | [] => true
  | as :: rest => allocationSafe m as (liveIn rest) && reuseSafe m rest

def renamed (m : Nat → Nat) (bs : Batches) : Batches := bs.map (List.map (renameAction m))

theorem reuse_correct (bs : Batches) (hs : reuseSafe m bs = true)
    (h : LiveRel m (liveIn bs) p q) :
    Option.Rel (LiveRel m []) (runBatches cap bs p) (runBatches cap (renamed m bs) q) := by
  induction bs generalizing p q with
  | nil => exact .some h
  | cons as rest ih =>
    have hh : allocationSafe m as (liveIn rest) = true ∧ reuseSafe m rest = true := by simpa [reuseSafe] using hs
    have hb : LiveRel m (liveBefore as (liveIn rest)) p q :=
      ⟨h.1,h.2.1,fun k hk => h.2.2 k (by simpa [liveIn] using hk)⟩
    have step := clock_rename as hb hh.1 (cap := cap)
    simp only [runBatches,renamed,List.map_cons]
    cases hp : clock cap as p <;> cases hq : clock cap (as.map (renameAction m)) q <;>
      simp only [hp,hq] at step
    · exact .none
    · cases step
    · cases step
    · cases step with | some rel => exact ih hh.2 rel

def initialCompatible (m : Nat → Nat) (bs : Batches) : Bool :=
  (liveIn bs).all (fun k => if k < 2 then m k == k else 2 ≤ m k)

theorem initial_related (h : initialCompatible m bs = true) (s : HybridWord.State)
    (x y : HybridWord.Word) : LiveRel m (liveIn bs) (wordPayload s x y) (wordPayload s x y) := by
  refine ⟨rfl,rfl,?_⟩
  intro k hk
  have hm := List.all_eq_true.mp h k hk
  by_cases small : k < 2
  · have eq : m k = k := by simpa [small] using hm
    simp [eq]
  · have large : 2 ≤ m k := by simpa [small] using hm
    simp [wordPayload,show k ≠ 0 by omega,show k ≠ 1 by omega,
      show m k ≠ 0 by omega,show m k ≠ 1 by omega]

theorem identity_safe (bs : Batches) : reuseSafe id bs = true := by
  induction bs with
  | nil => rfl
  | cons as rest ih =>
    simp only [reuseSafe,allocationSafe,ih,Bool.and_true,List.all_eq_true,Bool.or_eq_true,bne_iff_ne,beq_iff_eq,id_eq]
    intro k hk j hj; exact Classical.em (k = j) |>.symm

theorem identity_initial (bs : Batches) : initialCompatible id bs = true := by
  simp only [initialCompatible,List.all_eq_true]
  intro k hk
  by_cases small : k < 2
  · simp [small]
  · simp [small,show 2 ≤ k from by omega]

/-- Interference is between each write and every other value live after its
edge. A register read for the last time on an edge can be reused at that edge. -/
def interference : Batches → List (Nat × Nat)
  | [] => []
  | as :: rest =>
      ((batchWrites as).flatMap (fun k => (liveIn rest).filterMap
        (fun j => if k = j then none else some (k,j)))) ++ interference rest

def conflicts (es : List (Nat × Nat)) (a b : Nat) : Bool := es.contains (a,b) || es.contains (b,a)

def mapped (table : Array Nat) (k : Nat) := table[k]?.getD k

/-- Greedy proposal only. The general live-state checker below validates the
actual mapping, including any future replacement for this heuristic. -/
def color (bs : Batches) (wireCount : Nat) : Array Nat := Id.run do
  let edges := interference bs
  let mut table : Array Nat := #[]
  for k in List.range wireCount do
    if k < 2 then table := table.push k
    else
      let used := ((List.range k).filter (conflicts edges k)).map (mapped table)
      let slot := ((List.range (wireCount+1)).map (·+2)).find? (fun slot => !used.contains slot)
      table := table.push (slot.getD k)
  return table

structure Allocation where
  table : Array Nat
  accepted : Bool
  deriving Repr

def Allocation.mapping (a : Allocation) : Nat → Nat := if a.accepted then mapped a.table else id

def chooseAllocation (bs : Batches) (candidate : Array Nat) : Allocation :=
  ⟨candidate, reuseSafe (mapped candidate) bs && initialCompatible (mapped candidate) bs⟩

theorem chosen_safe (bs : Batches) (candidate : Array Nat) :
    reuseSafe (chooseAllocation bs candidate).mapping bs = true ∧
      initialCompatible (chooseAllocation bs candidate).mapping bs = true := by
  unfold chooseAllocation Allocation.mapping
  split
  · rename_i h
    simpa only [Bool.and_eq_true] using h
  · exact ⟨identity_safe bs,identity_initial bs⟩

theorem allocated_word_correct (bs : Batches) (candidate : Array Nat)
    (s : HybridWord.State) (x y : HybridWord.Word) :
    (runBatches cap (renamed (chooseAllocation bs candidate).mapping bs) (wordPayload s x y)).map Payload.data =
      (runBatches cap bs (wordPayload s x y)).map Payload.data := by
  have checks := chosen_safe bs candidate
  have h := reuse_correct bs checks.1 (initial_related checks.2 s x y) (cap := cap)
  generalize hb : runBatches cap bs (wordPayload s x y) = before at *
  generalize ha : runBatches cap (renamed (chooseAllocation bs candidate).mapping bs) (wordPayload s x y) = after at *
  cases h with
  | none => rfl
  | some rel => exact congrArg some rel.1.symm

end IRComparison.Circuit.Pipelining
