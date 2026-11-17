import IRComparison.Circuit.CompactDuplexSound

namespace IRComparison.Circuit

def receiverDuplex (code : HybridCompactFIFO.Code) : HybridCompactDuplex.Code :=
  ⟨code.start,code.stride,code.count,code.initial,code.refill,code.body.target⟩

theorem receiver_loop_duplex (code : HybridCompactFIFO.Code) (n k : Nat)
    (old : List Int) (s : State) (qi qo : List Int) :
    (receiverDuplex code).loop x y n k old s qi qo =
      (code.loop x y n k old s qi).map (fun (t,rest) => (t,rest,qo)) := by
  induction n generalizing k old s qi with
  | zero => rfl
  | succ n ih =>
    rw [HybridCompactDuplex.Code.loop,HybridCompactFIFO.Code.loop]
    simp only [receiverDuplex,HybridIR.MemoryCmd.target_correct]
    cases hb : code.body.eval (HybridSymbolicLoop.index code.start code.stride k) x y s old with
    | none => rfl
    | some t =>
      simp only [Option.map_some,bind,Option.bind]
      cases n with
      | zero => rfl
      | succ m =>
        cases hl : WindowFIFO.execute (fun _ => none) old
          (CompactRouting.instantiate (HybridSymbolicLoop.index code.start code.stride (k+1)) code.refill) qi with
        | none => rfl
        | some pair => obtain ⟨vs,rest⟩ := pair; exact ih (k+1) vs t rest

theorem receiver_eval_duplex (code : HybridCompactFIFO.Code) (s : State) (qi : List Int) :
    HybridCompactDuplexControl.evalFull (receiverDuplex code) x y s qi =
      (code.eval x y s qi).map (fun (t,rest) => (t,rest,[])) := by
  cases hc : code.count with
  | zero => simp [HybridCompactDuplexControl.evalFull,HybridCompactFIFO.Code.eval,receiverDuplex,hc]
  | succ n =>
    unfold HybridCompactDuplexControl.evalFull HybridCompactFIFO.Code.eval
    change (match code.count with
      | 0 => some (s,qi,[])
      | n+1 => (WindowFIFO.execute (fun _ => none) [] (CompactRouting.instantiate code.start code.initial) qi).bind
          (fun (vs,rest) => (receiverDuplex code).loop x y (n+1) 0 vs s rest [])) = _
    rw [hc]

    cases WindowFIFO.execute (fun _ => none) [] (CompactRouting.instantiate code.start code.initial) qi with
    | none => rfl
    | some pair => obtain ⟨vs,rest⟩ := pair; exact receiver_loop_duplex code (n+1) 0 vs s rest []

/-- Receivers emit no tokens: their capacity condition is discharged for any
allocated output capacity, including the zero-capacity unused output bank. -/
theorem receiver_correct (code : HybridCompactFIFO.Code) (b : Build) (p : Payload)
    (inputs : 2 ≤ b.wires.size) (distinct : qi ≠ qo) (empty : p.queues qo = [])
    (hx : p.wires 0 = x) (hy : p.wires 1 = y) :
    ∃ r, ((counted code.start code.stride code.count (code.initial.map fromFIFOLoad)
      (code.refill.map fromFIFOLoad) code.body.target input qi qo).run b).1.Eval cap p r ∧
      r.map (observeBlock qi qo) = (code.eval x y p.data (p.queues qi)).map (fun (t,rest) => (t,rest,[])) := by
  obtain ⟨r,hr,ho⟩ := duplex_correct (input:=input) (cap:=cap) (receiverDuplex code) b p inputs distinct empty hx hy (by
    intro t rest out he
    rw [receiver_eval_duplex] at he
    cases hh : code.eval x y p.data (p.queues qi) with
    | none => rw [hh] at he; cases he
    | some pair => obtain ⟨u,remaining⟩ := pair; rw [hh] at he; cases he; exact Nat.zero_le _)
  exact ⟨r,hr,by simpa only [receiver_eval_duplex] using ho⟩

end IRComparison.Circuit
