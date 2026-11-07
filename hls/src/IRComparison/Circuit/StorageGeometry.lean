import IRComparison.Circuit.FiniteSimulation
import IRComparison.Circuit.QueueSafety

namespace IRComparison.Circuit

def MemoriesFit (s : StorageShape) (r : Runtime) : Prop :=
  ∀ a, s.hasMemory a → (r.data.arrays a).size ≤ s.memorySize a

theorem MemoriesFit.setArray (h : MemoriesFit s r) (fits : values.size ≤ s.memorySize a) :
    MemoriesFit s (r.setArray a values) := by
  intro k hk
  simp only [Runtime.setArray]
  split
  · subst k; exact fits
  · exact h k hk

theorem execute_memory_fit (node : Node) (closed : node.inStorage s) (h : MemoriesFit s r)
    (he : execute cap node r = some t) : MemoriesFit s t := by
  cases node <;> simp only [execute] at he
  case halt | jump | clear => cases he; exact h
  case wire slot e n | assign slot e n =>
    cases hv : e.eval r.data r.wires <;> simp [hv] at he
    cases he; exact h
  case store a j e n =>
    cases hj : j.eval r.data r.wires <;> simp [hj] at he
    next index =>
      cases hv : e.eval r.data r.wires <;> simp [hv] at he
      next value =>
        cases hs : r.data.write a index value <;> simp [hs] at he
        next data =>
          cases he
          intro k hk
          exact (PipelineShapes.write_same hs k).symm ▸ h k hk
  case branch e yes no =>
    cases hv : e.eval r.data r.wires <;> simp [hv] at he
    cases he; exact h
  case snapshot a b n =>
    cases he
    exact h.setArray (Nat.le_trans (h b closed.2.1) closed.2.2.1)
  case erase a n => cases he; exact h.setArray (by simp)
  case send q e n =>
    cases hv : e.eval r.data r.wires <;> simp [hv] at he
    next value => obtain ⟨_,rfl⟩ := he; exact h
  case receive q slot n =>
    cases hq : r.queues q <;> simp [hq] at he
    cases he; exact h

theorem execute_pc_bound (node : Node) (closed : node.inStorage s) (hp : r.pc < s.states)
    (he : execute cap node r = some t) : t.pc < s.states := by
  cases node <;> simp only [execute] at he
  case halt => cases he; exact hp
  case jump n => cases he; exact closed
  case snapshot a b n => cases he; exact closed.2.2.2
  case erase a n | clear a n => cases he; exact closed.2
  case wire slot e n | assign slot e n =>
    cases hv : e.eval r.data r.wires <;> simp [hv] at he
    cases he; exact closed.2.2
  case store a j e n =>
    cases hj : j.eval r.data r.wires <;> simp [hj] at he
    next index =>
      cases hv : e.eval r.data r.wires <;> simp [hv] at he
      next value =>
        cases hs : r.data.write a index value <;> simp [hs] at he
        cases he; exact closed.2.2.2
  case branch e yes no =>
    cases hv : e.eval r.data r.wires <;> simp [hv] at he
    next value =>
      cases he
      change (if value = 0 then no else yes) < s.states
      split
      · exact closed.2.2
      · exact closed.2.1
  case send q e n =>
    cases hv : e.eval r.data r.wires <;> simp [hv] at he
    next value => obtain ⟨_,rfl⟩ := he; exact closed.2.2
  case receive q slot n =>
    cases hq : r.queues q <;> simp [hq] at he
    cases he; exact closed.2.2

theorem tick_geometry {m : Machine} (closed : ∀ node ∈ m.nodes.toList, node.inStorage s)
    (hp : r.pc < s.states) (hm : MemoriesFit s r) :
    (m.tick r).pc < s.states ∧ MemoriesFit s (m.tick r) := by
  by_cases hd : r.done = true
  · simpa [Machine.tick,hd] using And.intro hp hm
  · cases hn : m.nodes[r.pc]? with
    | none => simpa [Machine.tick,hd,hn] using And.intro hp hm
    | some node =>
      have hc := closed node (by simpa using Array.mem_of_getElem? hn)
      cases he : execute m.capacity node r with
      | none => simpa [Machine.tick,hd,hn,he] using And.intro hp hm
      | some t => simpa [Machine.tick,hd,hn,he] using And.intro (execute_pc_bound node hc hp he) (execute_memory_fit node hc hm he)

theorem run_geometry {m : Machine} (closed : ∀ node ∈ m.nodes.toList, node.inStorage s)
    (hp : r.pc < s.states) (hm : MemoriesFit s r) (cycles : Nat) :
    (m.run cycles r).pc < s.states ∧ MemoriesFit s (m.run cycles r) := by
  induction cycles generalizing r with
  | zero => exact ⟨hp,hm⟩
  | succ n ih =>
    have hh := tick_geometry closed hp hm
    exact ih hh.1 hh.2

end IRComparison.Circuit
