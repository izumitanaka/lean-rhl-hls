import IRComparison.Hybrid.HybridSymbolicProducerLoop
import IRComparison.Hybrid.HybridCompactReceiver

namespace IRComparison.HybridCompactDuplex
open HybridSymbolicLoop CompactRouting

structure Code where
  start : Int
  stride : Int
  count : Nat
  initial : List CompactRouting.Load
  refill : List CompactRouting.Load
  body : HybridIR.Cmd

def Code.loop (c : Code) (x y : Int) : Nat → Nat → List Int → State → List Int → List Int → Option (State × List Int × List Int)
  | 0,_,_,s,qi,qo => some (s,qi,qo)
  | n+1,k,old,s,qi,qo => do
    let (t,out) ← c.body.eval (index c.start c.stride k) x y s qo old
    match n with
    | 0 => some (t,qi,out)
    | m+1 =>
      let (vs,rest) ← WindowFIFO.execute (fun _ => none) old (instantiate (index c.start c.stride (k+1)) c.refill) qi
      c.loop x y (m+1) (k+1) vs t rest out

def Code.eval (c : Code) (x y : Int) (s : State) (qi : List Int) : Option (State × List Int) :=
  match c.count with
  | 0 => some (s,[])
  | n+1 => do
    let (vs,rest) ← WindowFIFO.execute (fun _ => none) [] (instantiate c.start c.initial) qi
    (c.loop x y (n+1) 0 vs s rest []).map (fun (t,_,out) => (t,out))

structure Plan (array size : Nat) (memory : HybridSymbolicLoop.Code) (supplier : CompactSequence.Seq) where
  sender : HybridSymbolicProducerLoop.Plan array size memory
  routedSupply : CompactSequence.Seq
  supplySame : routedSupply.entries = supplier.entries
  routing : HybridCompactFIFO.Plan memory routedSupply

def compile (array size : Nat) (memory : HybridSymbolicLoop.Code) (supplier : CompactSequence.Seq) :
    Option (Plan array size memory supplier) := do
  return ⟨← HybridSymbolicProducerLoop.compile array size memory,supplier,rfl,← HybridCompactFIFO.compile memory supplier⟩

def Plan.code (p : Plan array size memory supplier) : Code :=
  ⟨memory.start,memory.stride,memory.count,p.routing.initial.code,p.routing.refill.code,p.sender.body.code⟩

theorem Plan.loop_routing (p : Plan array size memory supplier) (n k : Nat) (bound : k+n ≤ memory.count)
    (s : State) (old qi qo : List Int)
    (hq : CommunicationIR.Corresponds input (p.routing.initial.after.at (index memory.start memory.stride k)).entries qi) :
    (p.code.loop x y n k old s qi qo).map (fun (t,_,out) => (t,out)) =
      p.sender.code.loop input x y n k old s qo := by
  induction n generalizing k s old qi qo with
  | zero => rfl
  | succ n ih =>
    rw [Code.loop,HybridSymbolicProducerLoop.Code.loop]
    dsimp only [Plan.code,HybridSymbolicProducerLoop.Plan.code]
    cases hb : p.sender.body.code.eval (index memory.start memory.stride k) x y s qo old with
    | none => rfl
    | some pair =>
      obtain ⟨t,out⟩ := pair
      cases n with
      | zero => rfl
      | succ m =>
        have before : CommunicationIR.Corresponds input
            ((shift p.routing.initial.after (-memory.stride)).at (index memory.start memory.stride (k+1))).entries qi := by
          rw [shift_at,index_next]
          simpa only [Int.add_neg_cancel_right] using hq
        obtain ⟨eq,suffix⟩ := p.routing.refill.correct (index memory.start memory.stride (k+1))
          (p.routing.refillSafe (k+1) (by omega)) input old qi before
        rw [HybridCompactFIFO.execute_input (other:=fun _ => none)] at eq suffix
        cases hl : WindowFIFO.execute (fun _ => none) old
            (instantiate (index memory.start memory.stride (k+1)) p.routing.refill.code) qi with
        | none =>
          simp only [hl,Option.map_none] at eq
          simp only [hl,← eq,bind,Option.bind,Option.map_none]
        | some pair =>
          obtain ⟨vs,qs⟩ := pair
          have after := suffix vs qs hl
          rw [p.routing.closes] at after
          simp only [hl,Option.map_some] at eq
          simp only [hl,← eq,bind,Option.bind]
          exact ih (k+1) (by omega) t vs qs out after

theorem Plan.routing_correct (p : Plan array size memory supplier) (s : State) (qi : List Int)
    (hq : CommunicationIR.Corresponds input supplier.entries qi) :
    p.code.eval x y s qi = p.sender.code.eval input x y s := by
  cases hc : memory.count with
  | zero => simp [Code.eval,Plan.code,HybridSymbolicProducerLoop.Code.eval,HybridSymbolicProducerLoop.Plan.code,hc]
  | succ n =>
    have initialQ : CommunicationIR.Corresponds input
        ((Sequence.mk ⟨0,p.routedSupply.first⟩ p.routedSupply.step ⟨0,p.routedSupply.count⟩).at memory.start).entries qi := by
      have actual : CommunicationIR.Corresponds input p.routedSupply.entries qi := by
        simpa only [p.supplySame] using hq
      simpa [Sequence.at,literal_eval] using actual
    obtain ⟨eq,suffix⟩ := p.routing.initial.correct memory.start p.routing.initialSafe input [] qi initialQ
    rw [HybridCompactFIFO.execute_input (other:=fun _ => none)] at eq suffix
    simp only [Code.eval,Plan.code,hc,HybridSymbolicProducerLoop.Code.eval,HybridSymbolicProducerLoop.Plan.code]
    cases hl : WindowFIFO.execute (fun _ => none) [] (instantiate memory.start p.routing.initial.code) qi with
    | none =>
      simp only [hl,Option.map_none] at eq
      simp only [hl,← eq,bind,Option.bind,Option.map_none]
    | some pair =>
      obtain ⟨vs,qs⟩ := pair
      have after := suffix vs qs hl
      simp only [hl,Option.map_some] at eq
      simp only [hl,← eq,bind,Option.bind]
      have hq' : CommunicationIR.Corresponds input (p.routing.initial.after.at (index memory.start memory.stride 0)).entries qs := by
        simpa only [index,Int.natCast_zero,Int.zero_mul,Int.add_zero] using after
      simpa only [Plan.code,HybridSymbolicProducerLoop.Plan.code,hc] using
        p.loop_routing (x:=x) (y:=y) (n+1) 0 (by omega) s vs qs [] hq'

def compileWithSMT (array size : Nat) (memory : HybridSymbolicLoop.Code) (supplier : CompactSequence.Seq)
    (directory : System.FilePath) : IO (Option (Plan array size memory supplier)) := do
  let some sender := HybridSymbolicProducerLoop.compile array size memory | return none
  let (_,certificate) ← CompactSequence.solve supplier directory
  let some certificate := certificate | return none
  let some routing := HybridCompactFIFO.compile memory certificate.sequence | return none
  return some ⟨sender,certificate.sequence,certificate.correct,routing⟩

end IRComparison.HybridCompactDuplex
