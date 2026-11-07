import IRComparison.Circuit.LoadFrame

namespace IRComparison.Circuit

theorem loadOne_frame (b : Build) (input qi slot : Nat) (old : List Expr) (l : WindowFIFO.Load)
    (hb : low ≤ b.wires.size) (hs : low ≤ slot) :
    b.wires.size ≤ ((loadOne input qi old slot l).run b).2.wires.size ∧
    ((loadOne input qi old slot l).run b).1.above low := by
  cases l with
  | memory | saved => exact ⟨Nat.le_refl _,hs⟩
  | take n => exact take_frame b qi slot (.lit n) low hb hs

/-- Each inserted load, including buffer reuse and destructive FIFO reads,
returns the source value and leaves architectural memory unchanged. -/
theorem loadOne_correct (b : Build) (input qi slot : Nat) (old : List Expr) (l : WindowFIFO.Load) (p : Payload)
    (hm : Matches p.data p.wires old values) :
    ∃ result, ((loadOne input qi old slot l).run b).1.Eval cap p result ∧
      result.map (observeTake qi slot) =
        (l.eval (arrayInput (p.data.arrays input)) values (p.queues qi)).map (fun (v,qs) => (p.data,v,qs)) := by
  cases l with
  | take n =>
    obtain ⟨r,hr,ho⟩ := take_correct (cap:=cap) b qi slot (.lit n) p
    refine ⟨r,hr,?_⟩
    cases hn : (p.queues qi)[n]? <;>
    simpa [Expr.eval,WindowFIFO.Load.eval,hn] using ho
  | memory a =>
    refine ⟨_,Schedule.Eval.step,?_⟩
    simp only [loadOne,Action.eval,Action.node,execute,Payload.at,Expr.eval,bind,Option.bind,WindowFIFO.Load.eval]
    cases arrayInput (p.data.arrays input) a <;> simp [observeTake,Runtime.payload,Runtime.setWire]
  | saved n =>
    refine ⟨_,Schedule.Eval.step,?_⟩
    simp only [loadOne,Action.eval,Action.node,execute,Payload.at,hm n,WindowFIFO.Load.eval]
    cases values[n]? <;> simp [observeTake,Runtime.payload,Runtime.setWire]

end IRComparison.Circuit
