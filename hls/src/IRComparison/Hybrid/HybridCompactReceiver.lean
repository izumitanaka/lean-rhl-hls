import IRComparison.Hybrid.HybridCompactFIFO
import IRComparison.Hybrid.HybridSafety

namespace IRComparison.HybridCompactReceiver
open StreamConsumer StreamState

theorem fifo_loop_erase (checked : HybridSafety.Checked array code.body) (n k : Nat) (old : List Int) (s : State) (q : List Int) :
    (HybridCompactFIFO.Code.loop code x y n k old s q).map (fun (t,qs) => (erase array t,qs)) =
      code.loop x y n k old (erase array s) q := by
  induction n generalizing k old s q with
  | zero => rfl
  | succ n ih =>
    rw [HybridCompactFIFO.Code.loop,HybridCompactFIFO.Code.loop,← checked.correct]
    cases hb : code.body.eval (HybridSymbolicLoop.index code.start code.stride k) x y s old with
    | none => rfl
    | some t =>
      cases n with
      | zero => rfl
      | succ m =>
        simp only [Option.map_some,bind,Option.bind]
        cases hl : WindowFIFO.execute (fun _ => none) old
            (CompactRouting.instantiate (HybridSymbolicLoop.index code.start code.stride (k+1)) code.refill) q with
        | none => rfl
        | some pair => obtain ⟨vs,qs⟩ := pair; exact ih (k+1) vs t qs

theorem fifo_erase (checked : HybridSafety.Checked array code.body) (s : State) (q : List Int) :
    (HybridCompactFIFO.Code.eval code x y s q).map (fun (t,qs) => (erase array t,qs)) =
      code.eval x y (erase array s) q := by
  cases hc : code.count with
  | zero => simp [HybridCompactFIFO.Code.eval,hc]
  | succ n =>
    simp only [HybridCompactFIFO.Code.eval,hc]
    cases WindowFIFO.execute (fun _ => none) [] (CompactRouting.instantiate code.start code.initial) q with
    | none => rfl
    | some pair => obtain ⟨vs,qs⟩ := pair; exact fifo_loop_erase checked (n+1) 0 vs s qs

structure Receiver (source : HybridSymbolicLoop.Code) (supplier : CompactSequence.Seq) where
  code : HybridCompactFIFO.Code
  body : code.body = source.body
  correct : ∀ input x y s q, CommunicationIR.Corresponds input supplier.entries q →
    (code.eval x y s q).map Prod.fst = source.eval input x y s

def receiver (p : HybridCompactFIFO.Plan source supplier) : Receiver source supplier :=
  ⟨p.code,rfl,fun input x y s q h => p.correct s q h⟩

def candidateReceiver (candidate : CompactSequence.Certified supplier)
    (p : HybridCompactFIFO.Plan source candidate.sequence) : Receiver source supplier :=
  ⟨p.code,rfl,by intro input x y s q h; apply p.correct s q; simpa only [candidate.correct] using h⟩

end IRComparison.HybridCompactReceiver
