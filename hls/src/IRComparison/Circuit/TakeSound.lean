import IRComparison.Circuit.QueueDrop

namespace IRComparison.Circuit

def observeTake (qi slot : Nat) (p : Payload) : State × Int × List Int :=
  (p.data,p.wires slot,p.queues qi)

theorem observe_receive (p : Payload) :
    ((Action.receive qi slot).eval cap p).map (observeTake qi slot) =
      (receiveHead (p.queues qi)).map (fun (v,vs) => (p.data,v,vs)) := by
  cases he : p.queues qi with
  | nil => rw [receive_empty he]; rfl
  | cons v vs =>
    rw [receive_eval he]
    simp [observeTake,Payload.setWire,Payload.setQueue,he,receiveHead]

/-- The actual discard/take compiler is correct for any queue, including an
empty queue or an excessive discard count. This covers its extra controller
cycles, not just the abstract list operation. -/
theorem take_correct (b : Build) (qi slot : Nat) (e : Expr) (p : Payload) :
    ∃ result, ((take qi slot e).run b).1.Eval cap p result ∧
      result.map (observeTake qi slot) = (do
        let d ← e.eval p.data p.wires
        let v ← (p.queues qi)[d.toNat]?
        return (p.data,v,(p.queues qi).drop (d.toNat+1))) := by
  let expr := Expr.natIndex e
  let n := b.wires.size
  let b1 := b.addWire (b.exprRange expr)
  let k := b1.wires.size
  let b2 := b1.addWire (b1.exprRange expr)
  let unused := b2.wires.size
  have hk : k = n+1 := by simp [k,b1,n,Build.addWire]
  have hu : unused = k+1 := by simp [unused,b2,Build.addWire,k]
  change ∃ result, (Schedule.seq (.step (.wire n expr))
    (.seq (counterLoop k (.wire n) (.step (.receive qi unused))) (.step (.receive qi slot)))).Eval cap p result ∧ _
  cases he : e.eval p.data p.wires with
  | none =>
    have hfail : (Action.wire n expr).eval cap p = none := by
      simp [Action.eval,Action.node,execute,Payload.at,expr,Expr.eval,he]
    refine ⟨none,.seq_error ?_,by simp [he]⟩
    rw [← hfail]; exact .step
  | some d =>
    let p1 := p.setWire n (d.toNat : Int)
    let p2 := p1.setWire k 0
    have capture : (Schedule.step (.wire n expr)).Eval cap p (some p1) := by
      apply setWire_eval
      simp [expr,Expr.eval,he]
    have init : (Schedule.step (.wire k (.lit 0))).Eval cap p1 (some p2) := setWire_eval rfl
    obtain ⟨r,hr,ho⟩ := discard_loop (cap:=cap) qi n k unused (by omega) (by omega) (by omega)
      d.toNat p2 (by simp [p2,p1,Payload.setWire,show n ≠ k from by omega]) (by simp [p2,Payload.setWire])
    have hloop := Schedule.Eval.seq init hr
    have connection :
        (r.map (observe qi)).bind (fun (s,q) => (receiveHead q).map (fun (v,vs) => (s,v,vs))) =
        (do let v ← (p.queues qi)[d.toNat]?; return (p.data,v,(p.queues qi).drop (d.toNat+1))) := by
      rw [ho]
      change ((dropPrefix d.toNat (p.queues qi)).map (fun qs => (p.data,qs))).bind _ = _
      have h := drop_receive d.toNat (p.queues qi)
      cases hd : dropPrefix d.toNat (p.queues qi) with
      | none =>
        simp only [hd,Option.bind_none] at h
        cases hn : (p.queues qi)[d.toNat]? <;>
        simpa [hd,hn,bind,pure,Option.bind,Option.map] using
          congrArg (Option.map (fun (v,vs) => (p.data,v,vs))) h
      | some qs =>
        simp only [hd,Option.bind_some] at h
        cases hn : (p.queues qi)[d.toNat]? <;>
        simpa [hd,hn,bind,pure,Option.bind,Option.map] using
          congrArg (Option.map (fun (v,vs) => (p.data,v,vs))) h
    cases r with
    | none =>
      refine ⟨none,.seq capture (.seq_error hloop),?_⟩
      simpa [he] using connection
    | some q =>
      refine ⟨(Action.receive qi slot).eval cap q,.seq capture (.seq hloop .step),?_⟩
      rw [observe_receive]
      simpa [he,observe] using connection

end IRComparison.Circuit
