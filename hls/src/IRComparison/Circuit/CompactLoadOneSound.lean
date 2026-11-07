import IRComparison.Circuit.LoadsSound

namespace IRComparison.Circuit

def Load.at (index : Int) : Load → WindowFIFO.Load
  | .memory a => .memory (a.eval index)
  | .saved n => .saved n
  | .take n => .take (n.eval index).toNat

theorem linear_correct (a : AffineAddress.Linear) (h : i.eval s w = some v) :
    (linear i a).eval s w = some (a.eval v) := by
  simp [linear,Expr.eval,h,Bin.eval,AffineAddress.Linear.eval]

theorem compactLoadOne_frame (b : Build) (input qi slot : Nat) (i : Expr) (old : List Expr) (l : Load)
    (hb : low ≤ b.wires.size) (hs : low ≤ slot) :
    b.wires.size ≤ ((compactLoadOne i input qi old slot l).run b).2.wires.size ∧
    ((compactLoadOne i input qi old slot l).run b).1.above low := by
  cases l with
  | memory | saved => exact ⟨Nat.le_refl _,hs⟩
  | take n => exact take_frame b qi slot (linear i n) low hb hs

theorem compactLoadOne_correct (b : Build) (input qi slot : Nat) (i : Expr) (old : List Expr) (l : Load) (p : Payload)
    (hi : i.eval p.data p.wires = some index) (hm : Matches p.data p.wires old values) :
    ∃ result, ((compactLoadOne i input qi old slot l).run b).1.Eval cap p result ∧
      result.map (observeTake qi slot) =
        ((l.at index).eval (arrayInput (p.data.arrays input)) values (p.queues qi)).map (fun (v,qs) => (p.data,v,qs)) := by
  cases l with
  | take n =>
    obtain ⟨r,hr,ho⟩ := take_correct (cap:=cap) b qi slot (linear i n) p
    refine ⟨r,hr,?_⟩
    cases hn : (p.queues qi)[(n.eval index).toNat]? <;>
    simpa [Load.at,linear_correct n hi,WindowFIFO.Load.eval,hn] using ho
  | memory a =>
    refine ⟨_,Schedule.Eval.step,?_⟩
    simp only [Action.eval,Action.node,execute,Payload.at,Expr.eval,linear_correct a hi,bind,Option.bind,Load.at,WindowFIFO.Load.eval]
    cases arrayInput (p.data.arrays input) (a.eval index) <;> simp [observeTake,Runtime.payload,Runtime.setWire]
  | saved n =>
    refine ⟨_,Schedule.Eval.step,?_⟩
    simp only [Action.eval,Action.node,execute,Payload.at,hm n,Load.at,WindowFIFO.Load.eval]
    cases values[n]? <;> simp [observeTake,Runtime.payload,Runtime.setWire]

end IRComparison.Circuit
