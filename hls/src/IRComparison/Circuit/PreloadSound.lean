import IRComparison.Circuit.BlocksSound
import IRComparison.Circuit.PayloadOperations

namespace IRComparison.Circuit

theorem Payload.setQueue_self (p : Payload) (q : Nat) : p.setQueue q (p.queues q) = p := by
  unfold setQueue
  congr 1
  funext n
  by_cases h : n = q <;> simp [h]

theorem Payload.setQueue_twice (p : Payload) (q : Nat) (first last : List Int) :
    (p.setQueue q first).setQueue q last = p.setQueue q last := by
  unfold setQueue
  congr 1
  funext n
  by_cases h : n = q <;> simp [h]

theorem preload_correct (input q : Nat) (indices : List Int) (p : Payload)
    (fits : (p.queues q).length + indices.length ≤ cap q) :
    (preload input q indices).Eval cap p
      ((CommunicationIR.emit (arrayInput (p.data.arrays input)) indices).map
        (fun values => p.setQueue q (p.queues q ++ values))) := by
  induction indices generalizing p with
  | nil => simpa [preload,CommunicationIR.emit,Payload.setQueue_self] using (Schedule.Eval.skip (cap:=cap) (p:=p))
  | cons i indices ih =>
    cases hv : arrayInput (p.data.arrays input) i with
    | none =>
      have fail : (Action.send q (.memory input (.lit i))).eval cap p = none := by
        simp [Action.eval,Action.node,execute,Payload.at,Expr.eval,hv]
      simpa only [preload,CommunicationIR.emit,hv,bind,Option.bind,Option.map_none] using
        (Schedule.Eval.seq_error (by rw [← fail]; exact Schedule.Eval.step) :
          (Schedule.seq (.step (.send q (.memory input (.lit i)))) (preload input q indices)).Eval cap p none)
    | some v =>
      have room : (p.queues q).length < cap q := by simp only [List.length_cons] at fits; omega
      let next := p.setQueue q (p.queues q ++ [v])
      have send : (Schedule.step (.send q (.memory input (.lit i)))).Eval cap p (some next) := by
        have hh : (Action.send q (.memory input (.lit i))).eval cap p = some next := by
          simp [Action.eval,Action.node,execute,Payload.at,Expr.eval,hv,room,next,Payload.setQueue,Runtime.setQueue,Runtime.payload]
        rw [← hh]; exact .step
      have tail := ih next (by simpa [next,Payload.setQueue,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using fits)
      have result := Schedule.Eval.seq send tail
      cases he : CommunicationIR.emit (arrayInput (p.data.arrays input)) indices with
      | none => simpa [preload,CommunicationIR.emit,hv,next,Payload.setQueue,he] using result
      | some values =>
        have nd : next.data = p.data := rfl
        have nq : next.queues q = p.queues q ++ [v] := by simp [next,Payload.setQueue]
        simp only [nd,he,Option.map_some,nq] at result
        dsimp only [next] at result
        rw [Payload.setQueue_twice] at result
        simpa [preload,CommunicationIR.emit,hv,he,List.append_assoc] using result

end IRComparison.Circuit
