import IRComparison.Circuit.InvariantSound
import IRComparison.Circuit.BitArithmetic

namespace IRComparison.Circuit

def bitExecute (wr : Nat → Interval) (capacities : Nat → Nat) (node : Node) (r : Runtime) : Option Runtime :=
  match node with
  | .halt => some { r with done := true }
  | .jump n => some { r with pc := n }
  | .wire slot v n => return { (r.setWire slot (← v.bitEval wr r.data r.wires)) with pc := n }
  | .assign slot v n => return { r with data := r.data.set slot (← v.bitEval wr r.data r.wires), pc := n }
  | .store a j v n => do
      let t ← r.data.write a (← j.bitEval wr r.data r.wires) (← v.bitEval wr r.data r.wires)
      return { r with data := t, pc := n }
  | .branch e yes no => return { r with pc := if (← e.bitEval wr r.data r.wires) != 0 then yes else no }
  | .snapshot a b n => some { (r.setArray a (r.data.arrays b)) with pc := n }
  | .erase a n => some { (r.setArray a #[]) with pc := n }
  | .clear q n => some { (r.setQueue q []) with pc := n }
  | .send q v n => do
      let x ← v.bitEval wr r.data r.wires
      if (r.queues q).length < capacities q then
        return { (r.setQueue q (r.queues q ++ [x])) with pc := n }
      else none
  | .receive q slot n => match r.queues q with
      | [] => none
      | x::xs => some { ((r.setQueue q xs).setWire slot x) with pc := n }


theorem bitExecute_correct (instruction : Node) (h : InputsBound r.data r.wires wr) :
    bitExecute wr capacities instruction r = execute capacities instruction r := by
  cases instruction <;> simp only [bitExecute,execute,Expr.bitEval_correct _ h] <;> rfl

def Machine.bitTick (m : Machine) (wr : Nat → Interval) (r : Runtime) : Runtime :=
  if r.done then r else
    match m.nodes[r.pc]?.bind (fun n => bitExecute wr m.capacity n r) with
    | none => { r with done := true, error := true }
    | some t => t

def Machine.bitRun (m : Machine) (wr : Nat → Interval) : Nat → Runtime → Runtime
  | 0,r => r
  | n+1,r => m.bitRun wr n (m.bitTick wr r)

theorem bitTick_correct {r : Runtime} {m : Machine} {wr : Nat → Interval} (h : r.done = false → InputsBound r.data r.wires wr) :
    m.bitTick wr r = m.tick r := by
  by_cases hd : r.done = true
  · simp [Machine.bitTick,Machine.tick,hd]
  · have hf : r.done = false := Bool.eq_false_iff.mpr hd
    simp only [Machine.bitTick,Machine.tick,hf]
    cases m.nodes[r.pc]? <;> simp only [bind,Option.bind,bitExecute_correct _ (h hf)] <;> rfl

/-- Once the finite invariant check succeeds, evaluating every arithmetic node
with its selected bit width preserves the complete clock-by-clock execution.
This theorem covers the arithmetic cycle model, not SystemVerilog parsing or
placement/routing. -/
theorem bitRun_correct (h : validInvariant a table = true) (hr : TableBound table r) (cycles : Nat) :
    a.machine.bitRun (fun n => a.wires[n]?.getD zeroRange) cycles r = a.machine.run cycles r := by
  induction cycles generalizing r with
  | zero => rfl
  | succ n ih =>
    simp only [Machine.bitRun,Machine.run]
    rw [bitTick_correct (fun hd => table_global_bound h hr hd)]
    exact ih (tick_table_bound h hr)

theorem bitRun_from_input (h : validInvariant a table = true) (hsize : 2 ≤ a.wires.size)
    (s : HybridWord.State) (x y : HybridWord.Word) (cycles : Nat) :
    a.machine.bitRun (fun n => a.wires[n]?.getD zeroRange) cycles
      (a.machine.start s.encode (HybridWord.encode x) (HybridWord.encode y)) =
    a.machine.run cycles
      (a.machine.start s.encode (HybridWord.encode x) (HybridWord.encode y)) :=
  bitRun_correct h (initial_table_bound h hsize s x y) cycles

end IRComparison.Circuit
