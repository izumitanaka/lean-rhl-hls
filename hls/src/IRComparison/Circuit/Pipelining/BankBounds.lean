import IRComparison.Circuit.Pipelining.StorageSound

namespace IRComparison.Circuit.Pipelining

def BankFits (shape : StorageShape) (p : Payload) : Prop :=
  MemoriesFit shape (p.at 0) ∧ QueuesBound shape.queueSize (p.at 0)

def ContentFits (shape : StorageShape) : Cell → Content → Prop
  | .array k,.array xs => shape.hasMemory k → xs.size ≤ shape.memorySize k
  | .queue k,.queue xs => xs.length ≤ shape.queueSize k
  | _,_ => True

theorem get_fits (h : BankFits shape p) (c : Cell) : ContentFits shape c (get p c) := by
  cases c with
  | reg | wire => trivial
  | array k => exact h.1 k
  | queue k => exact h.2 k

theorem put_fits (h : BankFits shape p) (hv : ContentFits shape c v) : BankFits shape (put p c v) := by
  cases c <;> cases v <;> try exact h
  case array.array k v =>
    refine ⟨?_,h.2⟩
    intro n hn
    change (if n = k then v else p.data.arrays n).size ≤ _
    split
    · rename_i eq; subst n; exact hv hn
    · exact h.1 n hn
  case queue.queue k v =>
    refine ⟨h.1,?_⟩
    intro n
    change (if n = k then v else p.queues n).length ≤ _
    split
    · rename_i eq; subst n; exact hv
    · exact h.2 n

section Generic
variable {α : Type} [ExpressionEvaluation α] [ExpressionDependencies α] [ExpressionStorage α]
variable {a : Action α}

theorem prepare_fits (hc : (a.node 0).inStorage shape) (hb : BankFits shape p)
    (hp : prepare shape.queueSize a p = some us) : ∀ u ∈ us, ContentFits shape u.1 u.2 := by
  have eval : a.eval shape.queueSize p = some (commit us p) := by rw [← prepare_correct,hp]; rfl
  have ex : execute shape.queueSize (a.node 0) (p.at 0) = some ((commit us p).at 0) := by
    rw [Action.execute_eq,eval]; rfl
  have fits : BankFits shape (commit us p) :=
    ⟨execute_memory_fit _ hc hb.1 ex,execute_queue_bound _ hb.2 ex⟩
  have shape' := prepare_shape hp
  have unique : (us.map Prod.fst).Nodup := by rw [shape'.1]; cases a <;> simp [actionWrites]
  intro u hu
  have hg := get_fits fits u.1
  rwa [get_commit_member us p unique shape'.2 hu] at hg

theorem commit_fits (us : List Update) (h : ∀ u ∈ us, ContentFits shape u.1 u.2)
    (hb : BankFits shape p) : BankFits shape (commit us p) := by
  induction us generalizing p with
  | nil => exact hb
  | cons u us ih => exact ih (fun v hv => h v (by simp [hv])) (put_fits hb (h u (by simp)))

theorem allPrepared_fits (as : List (Action α)) (hc : ∀ a ∈ as, (a.node 0).inStorage shape)
    (hb : BankFits shape p) (hp : allPrepared shape.queueSize p as = some us) :
    ∀ u ∈ us, ContentFits shape u.1 u.2 := by
  induction as generalizing us with
  | nil => simp [allPrepared] at hp; subst us; simp
  | cons a as ih =>
    cases ha : prepare shape.queueSize a p <;> cases hs : allPrepared shape.queueSize p as <;>
      simp [allPrepared,ha,hs] at hp
    subst us
    intro u hu
    rcases List.mem_append.mp hu with hu | hu
    · exact prepare_fits (hc a (by simp)) hb ha u hu
    · exact ih (fun b hm => hc b (by simp [hm])) hs u hu

theorem batch_fits (as : List (Action α)) (hc : ∀ a ∈ as, (a.node 0).inStorage shape)
    (hb : BankFits shape p) (he : clock shape.queueSize as p = some q) : BankFits shape q := by
  simp only [clock,clockFrom_prepared] at he
  cases hp : allPrepared shape.queueSize p as <;> simp [hp] at he
  subst q
  exact commit_fits _ (allPrepared_fits as hc hb hp) hb

end Generic

theorem batchStatements_length (bs : Batches) (base : Nat) : (batchStatements base bs).length = bs.length+1 := by
  induction bs generalizing base <;> simp_all [batchStatements]

theorem batchStatements_last (bs : Batches) (base : Nat) : (batchStatements base bs)[bs.length]? = some RTL.halt := by
  induction bs generalizing base <;> simp_all [batchStatements]

theorem batchStatements_at (bs : Batches) (base k : Nat) (h : k < bs.length) :
    (batchStatements base bs)[k]? = some (lowerClock (base+k+1) bs[k]) := by
  induction bs generalizing base k with
  | nil => simp at h
  | cons as rest ih =>
    cases k with
    | zero => rfl
    | succ k => simpa [batchStatements,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (base+1) k (by simpa using h)

structure BatchBound (a : Artifact) (bs : Batches) (r : Circuit.Runtime) : Prop where
  numeric : RuntimeBound a.wires.toList r
  banks : BankFits a.storageShape r.payload
  pc : r.pc ≤ bs.length

theorem shape_frame (a : Artifact) : a.storageShape.wireRange = Frame.get a.wires.toList := by
  funext n; simp [Artifact.storageShape,StorageShape.wireRange,Frame.get]

theorem batchTick_bound (a : Artifact) (bs : Batches) (hc : BatchesClosed a.storageShape bs)
    (hw : batchWidthsSafe a.wires.toList bs = true) (h : BatchBound a bs r) :
    BatchBound a bs ((batchProgram bs a.machine.capacities).tick a.storageShape.wireRange r) := by
  by_cases stopped : r.done = true
  · simpa [RTL.Program.tick,stopped] using h
  have live : r.done = false := by cases hd : r.done <;> simp_all
  by_cases atEnd : r.pc = bs.length
  · simp only [batchProgram,RTL.Program.tick,live,Bool.false_eq_true,ite_false,List.getElem?_toArray,
      atEnd,batchStatements_last,Option.getD_some]
    exact ⟨⟨h.numeric.data,h.numeric.wires,h.numeric.queues⟩,h.banks,h.pc⟩
  · have inside : r.pc < bs.length := by have := h.pc; omega
    have member : bs[r.pc] ∈ bs := List.getElem_mem _
    have wc : ∀ act ∈ bs[r.pc], actionWidthSafe a.wires.toList act = true :=
      List.all_eq_true.mp (List.all_eq_true.mp hw _ member)
    have bound : InputsBound r.data r.wires a.storageShape.wireRange := by rw [shape_frame]; exact h.numeric.inputs
    simp only [batchProgram,RTL.Program.tick,live,Bool.false_eq_true,ite_false,List.getElem?_toArray,
      batchStatements_at bs 0 r.pc inside,Nat.zero_add,Option.getD_some,lowerClock_bit_correct _ _ r bound]
    change BatchBound a bs (match clock a.machine.capacity bs[r.pc] r.payload with
      | none => {r with done := true,error := true}
      | some p => {withPayload r p with pc := r.pc+1})
    cases he : clock a.machine.capacity bs[r.pc] r.payload with
    | none => exact ⟨⟨h.numeric.data,h.numeric.wires,h.numeric.queues⟩,h.banks,h.pc⟩
    | some q =>
      have w := batch_width_preserved _ wc
        (show WidthBound a.wires.toList r.payload from ⟨h.numeric.data,h.numeric.wires,h.numeric.queues⟩) he
      have b := batch_fits _ (hc _ member) h.banks he
      exact ⟨⟨w.data,w.wires,w.queues⟩,b,by simp only; omega⟩

theorem batchRun_bound (a : Artifact) (bs : Batches) (hc : BatchesClosed a.storageShape bs)
    (hw : batchWidthsSafe a.wires.toList bs = true) (h : BatchBound a bs r) (n : Nat) :
    BatchBound a bs ((batchProgram bs a.machine.capacities).run a.storageShape.wireRange n r) := by
  induction n generalizing r with
  | zero => exact h
  | succ n ih => exact ih (batchTick_bound a bs hc hw h)

theorem BatchBound.storage (h : BatchBound a bs r) (size : bs.length+1 ≤ a.storageShape.states) :
    StorageBound a.storageShape r := by
  refine ⟨by have := h.pc; omega,h.numeric.data,h.banks.1,?_,fun q _ => h.banks.2 q,h.numeric.queues⟩
  intro n hn
  rw [shape_frame]
  exact h.numeric.wires n

end IRComparison.Circuit.Pipelining
