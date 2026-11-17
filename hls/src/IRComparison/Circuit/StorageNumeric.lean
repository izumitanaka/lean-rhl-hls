import IRComparison.Circuit.StorageGeometry

namespace IRComparison.Circuit

theorem execute_done_payload (node : Node) (he : execute cap node r = some t)
    (live : r.done = false) (stopped : t.done = true) :
    t.data = r.data ∧ t.wires = r.wires ∧ t.queues = r.queues := by
  cases node <;> simp only [execute] at he
  case halt => cases he; exact ⟨rfl,rfl,rfl⟩
  case jump | snapshot | erase | clear => cases he; simp [Runtime.setWire,Runtime.setArray,Runtime.setQueue,live] at stopped
  case wire slot e n | assign slot e n =>
    cases hv : e.eval r.data r.wires <;> simp [hv] at he
    cases he; simp [Runtime.setWire,Runtime.setArray,Runtime.setQueue,live] at stopped
  case store a j e n =>
    cases hj : j.eval r.data r.wires <;> simp [hj] at he
    next index =>
      cases hv : e.eval r.data r.wires <;> simp [hv] at he
      next value =>
        cases hs : r.data.write a index value <;> simp [hs] at he
        cases he; simp [Runtime.setWire,Runtime.setArray,Runtime.setQueue,live] at stopped
  case branch e yes no =>
    cases hv : e.eval r.data r.wires <;> simp [hv] at he
    cases he; simp [Runtime.setWire,Runtime.setArray,Runtime.setQueue,live] at stopped
  case send q e n =>
    cases hv : e.eval r.data r.wires <;> simp [hv] at he
    next value => obtain ⟨_,rfl⟩ := he; simp [Runtime.setWire,Runtime.setArray,Runtime.setQueue,live] at stopped
  case receive q slot n =>
    cases hq : r.queues q <;> simp [hq] at he
    cases he; simp [Runtime.setWire,Runtime.setArray,Runtime.setQueue,live] at stopped

theorem tick_stops_payload {m : Machine} (live : r.done = false) (stopped : (m.tick r).done = true) :
    (m.tick r).data = r.data ∧ (m.tick r).wires = r.wires ∧ (m.tick r).queues = r.queues := by
  cases hn : m.nodes[r.pc]? with
  | none => simp [Machine.tick,live,hn]
  | some node =>
    cases he : execute m.capacity node r with
    | none => simp [Machine.tick,live,hn,he]
    | some t =>
      have ht : m.tick r = t := by simp [Machine.tick,live,hn,he]
      rw [ht] at stopped ⊢
      exact execute_done_payload node he live stopped

theorem table_runtime_global (h : validInvariant a table = true) (hr : TableBound table r)
    (live : r.done = false) : RuntimeBound a.wires.toList r := by
  have inputs := table_global_bound h hr live
  rcases hr with done | ⟨f,hf,hb⟩
  · simp [live] at done
  refine ⟨hb.data,?_,hb.queues⟩
  simpa only [Frame.contains,Frame.get,Array.getElem?_toList] using inputs.wires

/-- Retain bounds even at the final halt/error state; the control-flow table
alone deliberately does not constrain stopped states. -/
theorem tick_runtime_global (h : validInvariant a table = true) (hr : TableBound table r)
    (bound : RuntimeBound a.wires.toList r) : RuntimeBound a.wires.toList (a.machine.tick r) := by
  by_cases old : r.done = true
  · rw [halt_stable _ _ old]; exact bound
  · have live : r.done = false := Bool.eq_false_iff.mpr old
    by_cases stopped : (a.machine.tick r).done = true
    · obtain ⟨hd,hw,hq⟩ := tick_stops_payload live stopped
      exact ⟨by rw [hd]; exact bound.data,by rw [hw]; exact bound.wires,by rw [hq]; exact bound.queues⟩
    · exact table_runtime_global h (tick_table_bound h hr) (Bool.eq_false_iff.mpr stopped)

theorem run_runtime_global (h : validInvariant a table = true) (hr : TableBound table r)
    (bound : RuntimeBound a.wires.toList r) (cycles : Nat) : RuntimeBound a.wires.toList (a.machine.run cycles r) := by
  induction cycles generalizing r with
  | zero => exact bound
  | succ n ih => exact ih (tick_table_bound h hr) (tick_runtime_global h hr bound)

theorem initial_runtime_global (h : validInvariant a table = true) (inputs : 2 ≤ a.wires.size)
    (s : HybridWord.State) (x y : HybridWord.Word) :
    RuntimeBound a.wires.toList (a.machine.start s.encode (HybridWord.encode x) (HybridWord.encode y)) :=
  table_runtime_global h (initial_table_bound h inputs s x y) rfl

end IRComparison.Circuit
