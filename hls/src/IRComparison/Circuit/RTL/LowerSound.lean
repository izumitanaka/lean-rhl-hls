import IRComparison.Circuit.RTL.Semantics

namespace IRComparison.Circuit.RTL

theorem fault_eval (wr cap) (old r : Runtime) :
    fault.eval wr cap old r = {r with done := true,error := true} := rfl

/-- The statement compiler makes every failure guard and every simultaneous
FIFO/register update explicit. It is proved for all nodes and states, not for
the generated examples alone. -/
theorem lowerNode_correct (node : Node) (r : Runtime) :
    (lowerNode node).eval wr cap r r =
      (bitExecute wr cap node r).getD {r with done := true,error := true} := by
  cases node with
  | halt => rfl
  | jump n => simp [lowerNode,advance,Statement.eval,Scalar.eval,Register.write,bitExecute]
  | wire k e n | assign k e n =>
    cases he : e.bitEval wr r.data r.wires <;>
      simp [lowerNode,guarded,Test.eval,Statement.eval,advance,fault,Scalar.eval,Register.write,bitExecute,he]
  | store a j e n =>
    cases hj : j.bitEval wr r.data r.wires with
    | none => simp [lowerNode,guarded,Test.eval,Statement.eval,fault,Scalar.eval,Register.write,bitExecute,hj]
    | some index =>
      cases he : e.bitEval wr r.data r.wires with
      | none => simp [lowerNode,guarded,Test.eval,Statement.eval,fault,Scalar.eval,Register.write,bitExecute,hj,he]
      | some value =>
        by_cases negative : index < 0
        · simp [lowerNode,guarded,Test.eval,Statement.eval,fault,Scalar.eval,Register.write,bitExecute,hj,he,State.write,negative,show ¬0 ≤ index from by omega]
        · by_cases inside : index.toNat < (r.data.arrays a).size
          · simp [lowerNode,guarded,Test.eval,Statement.eval,advance,Scalar.eval,Register.write,MemoryRhs.eval,bitExecute,hj,he,
              State.write,negative,inside,show 0 ≤ index from by omega,Array.set!,Array.setIfInBounds,Runtime.setArray]
          · simp [lowerNode,guarded,Test.eval,Statement.eval,fault,Scalar.eval,Register.write,bitExecute,hj,he,State.write,negative,inside]
  | branch e yes no =>
    cases he : e.bitEval wr r.data r.wires with
    | none => simp [lowerNode,guarded,Test.eval,Statement.eval,advance,fault,Scalar.eval,Register.write,bitExecute,he]
    | some v =>
      by_cases hv : v = 0 <;>
        simp [lowerNode,guarded,Test.eval,Statement.eval,advance,fault,Scalar.eval,Register.write,bitExecute,he,hv]
  | snapshot a b n | erase a n =>
    simp [lowerNode,Statement.eval,MemoryRhs.eval,advance,Scalar.eval,Register.write,bitExecute]
  | clear q n => simp [lowerNode,Statement.eval,QueueRhs.eval,advance,Scalar.eval,Register.write,bitExecute]
  | send q e n =>
    cases he : e.bitEval wr r.data r.wires with
    | none => simp [lowerNode,guarded,Test.eval,Statement.eval,fault,Scalar.eval,Register.write,bitExecute,he]
    | some value =>
      by_cases room : (r.queues q).length < cap q <;>
        simp [lowerNode,guarded,Test.eval,Statement.eval,fault,advance,Scalar.eval,Register.write,QueueRhs.eval,bitExecute,he,room]
  | receive q k n =>
    cases hq : r.queues q <;>
      simp [lowerNode,guarded,Test.eval,Statement.eval,fault,advance,Scalar.eval,Register.write,QueueRhs.eval,bitExecute,hq,Runtime.setQueue,Runtime.setWire]

theorem lower_tick (m : Machine) (wr : Nat → Interval) (r : Runtime) :
    (lower m).tick wr r = m.bitTick wr r := by
  simp only [Program.tick,lower,Machine.bitTick,Array.getElem?_map]
  split
  · rfl
  · cases hn : m.nodes[r.pc]? with
    | none => exact fault_eval wr _ r r
    | some node =>
      simp only [Option.map_some,Option.getD_some,Option.bind]
      have hh := lowerNode_correct (wr:=wr) (cap:=m.capacity) node r
      cases he : bitExecute wr m.capacity node r <;> simp only [he,Option.getD] at hh ⊢ <;> exact hh

theorem lower_run (m : Machine) (wr : Nat → Interval) (r : Runtime) (cycles : Nat) :
    (lower m).run wr cycles r = m.bitRun wr cycles r := by
  induction cycles generalizing r with
  | zero => rfl
  | succ n ih => simp only [Program.run,Machine.bitRun,lower_tick,ih]

end IRComparison.Circuit.RTL
