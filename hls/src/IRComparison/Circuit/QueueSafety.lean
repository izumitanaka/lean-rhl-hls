import IRComparison.Circuit.Machine

namespace IRComparison.Circuit

def QueuesBound (cap : Nat → Nat) (r : Runtime) : Prop := ∀ q, (r.queues q).length ≤ cap q

theorem QueuesBound.setQueue (h : QueuesBound cap r) (hv : vs.length ≤ cap q) :
    QueuesBound cap (r.setQueue q vs) := by
  intro k
  by_cases hk : k = q
  · simpa [Runtime.setQueue,hk] using hv
  · simpa [Runtime.setQueue,hk] using h k

theorem execute_queue_bound (instruction : Node) (h : QueuesBound cap r)
    (he : execute cap instruction r = some t) : QueuesBound cap t := by
  cases instruction <;> simp only [execute] at he
  case halt | jump | snapshot | erase => cases he; exact h
  case wire slot e next | assign slot e next =>
    cases hv : e.eval r.data r.wires <;> simp [hv] at he
    cases he; exact h
  case store a j e next =>
    cases hj : j.eval r.data r.wires <;> simp [hj] at he
    next index =>
      cases hv : e.eval r.data r.wires <;> simp [hv] at he
      next value =>
        cases hs : r.data.write a index value <;> simp [hs] at he
        cases he; exact h
  case branch e yes no =>
    cases hv : e.eval r.data r.wires <;> simp [hv] at he
    cases he; exact h
  case clear q next =>
    cases he
    exact h.setQueue (vs:=[]) (by simp)
  case send q e next =>
    cases hv : e.eval r.data r.wires <;> simp [hv] at he
    next value =>
      obtain ⟨space,rfl⟩ := he
      exact h.setQueue (vs:=r.queues q ++ [value]) (by simp; omega)
  case receive q slot next =>
    cases hq : r.queues q with
    | nil => simp [hq] at he
    | cons v vs =>
      simp only [hq,Option.some.injEq] at he
      cases he
      apply h.setQueue
      have hh := h q
      simp only [hq,List.length_cons] at hh
      omega

theorem tick_queue_bound {m : Machine} (h : QueuesBound m.capacity r) : QueuesBound m.capacity (m.tick r) := by
  by_cases hd : r.done = true
  · simpa [Machine.tick,hd] using h
  · cases hn : m.nodes[r.pc]? with
    | none => simpa [Machine.tick,hd,hn] using h
    | some instruction =>
      cases he : execute m.capacity instruction r with
      | none => simpa [Machine.tick,hd,hn,he] using h
      | some t => simpa [Machine.tick,hd,hn,he] using execute_queue_bound instruction h he

theorem run_queue_bound {m : Machine} (h : QueuesBound m.capacity r) (cycles : Nat) :
    QueuesBound m.capacity (m.run cycles r) := by
  induction cycles generalizing r with
  | zero => exact h
  | succ n ih => exact ih (tick_queue_bound h)

/-- All reachable FIFO occupancies fit the physical capacities. This proves
memory safety of the queue implementation; source preservation additionally
requires showing that its overflow error cannot be newly introduced. -/
theorem initialized_queue_bound (m : Machine) (s : State) (x y : Int) (cycles : Nat) :
    QueuesBound m.capacity (m.run cycles (m.start s x y)) :=
  run_queue_bound (by intro q; simp [Machine.start]) cycles

end IRComparison.Circuit
