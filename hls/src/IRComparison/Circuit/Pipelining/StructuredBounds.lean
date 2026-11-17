import IRComparison.Circuit.Pipelining.StructuredInvariant

namespace IRComparison.Circuit.Pipelining

variable {α : Type} [ExpressionEvaluation α] [ExpressionDependencies α] [ExpressionRange α]
  [ExpressionStorage α]
variable {g : ClockGraph α}

def ClockNode.closed (shape : StorageShape) : ClockNode α → Prop
  | .batch as _ => ∀ a ∈ as, (a.node 0).inStorage shape
  | .branch e yes no => (Node.branch e yes no).inStorage shape
  | .jump next => (Node.jump next).inStorage shape
  | .halt => True

instance [∀ e : α, Decidable (ExpressionStorage.closed shape e)] (n : ClockNode α) : Decidable (n.closed shape) := by
  cases n <;> unfold ClockNode.closed <;> infer_instance

def ClockNode.distinct : ClockNode α → Prop
  | .batch as _ => BanksDistinct as
  | _ => True

instance (n : ClockNode α) : Decidable n.distinct := by
  cases n <;> unfold ClockNode.distinct <;> infer_instance

def ClockNode.targets (limit : Nat) : ClockNode α → Prop
  | .batch _ next | .jump next => next < limit
  | .branch _ yes no => yes < limit ∧ no < limit
  | .halt => True

instance (n : ClockNode α) : Decidable (n.targets limit) := by
  cases n <;> unfold ClockNode.targets <;> infer_instance

structure ClockBound (a : Artifact) (g : ClockGraph α) (table : InvariantTable) (r : Circuit.Runtime) : Prop where
  numeric : RuntimeBound a.wires.toList r
  banks : BankFits a.storageShape r.payload
  pc : r.pc < g.nodes.size
  invariant : TableBound table r

structure GraphChecks (a : Artifact) (g : ClockGraph α) (table : InvariantTable) : Prop where
  capacity : g.capacities = a.machine.capacities
  size : g.nodes.size ≤ a.storageShape.states
  entry : 1 < g.nodes.size
  initial : initialWidthsSafe a.wires.toList = true
  invariant : validClockInvariant a g table = true
  closed : ∀ n ∈ g.nodes.toList, n.closed a.storageShape
  distinct : ∀ n ∈ g.nodes.toList, n.distinct
  targets : ∀ n ∈ g.nodes.toList, n.targets g.nodes.size

theorem ClockNode.stopped_payload (n : ClockNode α) (live : r.done = false)
    (stopped : (n.eval cap r).done = true) : (n.eval cap r).payload = r.payload := by
  cases n with
  | batch as next =>
    cases he : clock cap as r.payload with
    | none => simp only [ClockNode.eval,he]; rfl
    | some q => simp [ClockNode.eval,he,withPayload,live] at stopped
  | branch e yes no =>
    cases he : ExpressionEvaluation.eval e r.data r.wires with
    | none => simp only [ClockNode.eval,he]; rfl
    | some v => simp [ClockNode.eval,he,withPayload,live] at stopped
  | jump next => simp [ClockNode.eval,live] at stopped
  | halt => rfl

theorem clockNode_storage (n : ClockNode α) (caps : g.capacities = a.machine.capacities)
    (hc : n.closed a.storageShape) (ht : n.targets g.nodes.size)
    (h : ClockBound a g table r) :
    BankFits a.storageShape (n.eval g.capacity r).payload ∧ (n.eval g.capacity r).pc < g.nodes.size := by
  cases n with
  | batch as next =>
    cases he : clock g.capacity as r.payload with
    | none => simpa [ClockNode.eval,he] using And.intro h.banks h.pc
    | some q =>
      have cp : g.capacity = a.storageShape.queueSize := by
        change capacityOf g.capacities = a.machine.capacity
        rw [caps]; rfl
      have banks := batch_fits as hc h.banks (by simpa only [cp] using he)
      exact ⟨by simpa [ClockNode.eval,he] using banks,by simpa [ClockNode.eval,he] using ht⟩
  | branch e yes no =>
    cases he : ExpressionEvaluation.eval e r.data r.wires with
    | none => exact ⟨by simpa [ClockNode.eval,he] using h.banks,by simpa [ClockNode.eval,he] using h.pc⟩
    | some v =>
      refine ⟨by simpa [ClockNode.eval,he] using h.banks,?_⟩
      simp only [ClockNode.eval,he]
      change (if v != 0 then yes else no) < _
      split
      · exact ht.1
      · exact ht.2
  | jump next => exact ⟨h.banks,ht⟩
  | halt => exact ⟨h.banks,h.pc⟩

theorem clockGraph_tick_bound (checks : GraphChecks a g table) (h : ClockBound a g table r) :
    ClockBound a g table (g.tick r) := by
  by_cases done : r.done = true
  · simpa [ClockGraph.tick,done] using h
  have hn : g.nodes[r.pc]? = some (g.nodes[r.pc]'h.pc) := Array.getElem?_eq_getElem h.pc
  have hm : g.nodes[r.pc]'h.pc ∈ g.nodes.toList := by simp
  have he : g.tick r = (g.nodes[r.pc]'h.pc).eval g.capacity r := by simp [ClockGraph.tick,done,hn]
  have inv := clock_tick_table checks.invariant h.invariant
  have num : RuntimeBound a.wires.toList (g.tick r) := by
    by_cases stopped : (g.tick r).done = true
    · have eq := ClockNode.stopped_payload (g.nodes[r.pc]'h.pc) (Bool.eq_false_iff.mpr done) (by simpa [he] using stopped)
      have payload : (g.tick r).payload = r.payload := by simpa [he] using eq
      have bound : WidthBound a.wires.toList (g.tick r).payload := by
        rw [payload]; exact ⟨h.numeric.data,h.numeric.wires,h.numeric.queues⟩
      exact ⟨bound.data,bound.wires,bound.queues⟩
    · exact clock_table_global checks.invariant inv (Bool.eq_false_iff.mpr stopped)
  have storage := clockNode_storage _ checks.capacity (checks.closed _ hm) (checks.targets _ hm) h
  exact ⟨num,by simpa [he] using storage.1,by simpa [he] using storage.2,inv⟩

theorem clockGraph_run_bound (checks : GraphChecks a g table) (h : ClockBound a g table r) (n : Nat) :
    ClockBound a g table (g.run n r) := by
  induction n generalizing r with
  | zero => exact h
  | succ n ih => exact ih (clockGraph_tick_bound checks h)

theorem ClockBound.storage (h : ClockBound a g table r) (size : g.nodes.size ≤ a.storageShape.states) :
    StorageBound a.storageShape r := by
  refine ⟨Nat.lt_of_lt_of_le h.pc size,h.numeric.data,h.banks.1,?_,fun q _ => h.banks.2 q,h.numeric.queues⟩
  intro n hn
  rw [shape_frame]
  exact h.numeric.wires n

theorem clockGraph_rtl_tick {g : ClockGraph} {r : Circuit.Runtime} (h : InputsBound r.data r.wires wr) : g.rtl.tick wr r = g.tick r := by
  simp only [ClockGraph.rtl,RTL.Program.tick,ClockGraph.tick,Array.getElem?_map]
  split
  · rfl
  · cases hn : g.nodes[r.pc]? with
    | none => rfl
    | some n => exact n.statement_correct h

theorem clockGraph_rtl_run {g : ClockGraph} (checks : GraphChecks a g table) (h : ClockBound a g table r) (n : Nat) :
    g.rtl.run a.storageShape.wireRange n r = g.run n r := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    rw [RTL.Program.run,ClockGraph.run,clockGraph_rtl_tick (by rw [shape_frame]; exact h.numeric.inputs)]
    exact ih (clockGraph_tick_bound checks h)

/-- Full finite execution of arbitrary nested control, including guards that
fail. This theorem introduces no assumption that a while loop terminates. -/
theorem structured_rtl_finishes (he : s.Eval (capacityOf capacities) p result)
    (checks : GraphChecks a ((scheduleStructure strategy s).assemble capacities) table)
    (bound : ClockBound a ((scheduleStructure strategy s).assemble capacities) table (p.at 1)) :
    ∃ n, (((scheduleStructure strategy s).assemble capacities).rtl.run a.storageShape.wireRange n (p.at 1)).result =
      some (result.map Payload.data) := by
  obtain ⟨n,hn⟩ := scheduleStructure_finishes (strategy := strategy) he
  exact ⟨n,by rw [clockGraph_rtl_run checks bound]; exact hn⟩

end IRComparison.Circuit.Pipelining
