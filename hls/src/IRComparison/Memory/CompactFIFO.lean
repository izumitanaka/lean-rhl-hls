import IRComparison.Memory.CompactRouting
import IRComparison.Memory.SymbolicWindowLoop

namespace IRComparison.CompactFIFO
open CompactRouting AffineAddress SymbolicWindowLoop

structure Code where
  start : Int
  stride : Int
  count : Nat
  initial : List CompactRouting.Load
  refill : List CompactRouting.Load
  body : Imperative.Cmd

def Code.loop (c : Code) (x y : Int) : Nat → Nat → List Int → State → List Int → Option (State × List Int)
  | 0,_,_,s,q => some (s,q)
  | n+1,k,old,s,q => do
    let t ← c.body.eval (index c.start c.stride k) x y s old
    match n with
    | 0 => some (t,q)
    | m+1 =>
      let (vs,qs) ← WindowFIFO.execute (fun _ => none) old
        (instantiate (index c.start c.stride (k+1)) c.refill) q
      c.loop x y (m+1) (k+1) vs t qs

def Code.eval (c : Code) (x y : Int) (s : State) (q : List Int) : Option (State × List Int) :=
  match c.count with
  | 0 => some (s,q)
  | n+1 => do
    let (vs,qs) ← WindowFIFO.execute (fun _ => none) [] (instantiate c.start c.initial) q
    c.loop x y (n+1) 0 vs s qs

/-- Queue indices are an affine invariant at the end of each iteration.
    The invariant and its shift disappear from executable code. -/
structure Plan (memory : SymbolicWindowLoop.Code) (producer : CompactSequence.Seq) where
  initial : Route memory.initial ⟨⟨0,producer.first⟩,producer.step,⟨0,producer.count⟩⟩
  refill : Route memory.refill (shift initial.after (-memory.stride))
  closes : refill.after = initial.after
  initialSafe : Valid initial.guards memory.start
  refillSafe : ∀ k, k < memory.count → Valid refill.guards (index memory.start memory.stride k)

def Plan.code (p : Plan memory producer) : Code :=
  ⟨memory.start,memory.stride,memory.count,p.initial.code,p.refill.code,memory.body⟩

/-- FIFO loads do not consult the memory callback. -/
theorem execute_input (ls : List CompactRouting.Load) :
    WindowFIFO.execute input old (instantiate i ls) q = WindowFIFO.execute other old (instantiate i ls) q := by
  induction ls generalizing q with
  | nil => rfl
  | cons l ls ih =>
    simp only [instantiate] at ih
    cases l with
    | saved n =>
      simp only [instantiate,List.map_cons,WindowFIFO.execute,WindowFIFO.Load.eval]
      cases old[n]? <;> simp_all [bind,Option.bind]
    | take n =>
      simp only [instantiate,List.map_cons,WindowFIFO.execute,WindowFIFO.Load.eval]
      cases q[(n.eval i).toNat]? <;> simp_all [bind,Option.bind]

theorem Plan.loop_correct (p : Plan memory producer) (n k : Nat) (bound : k+n ≤ memory.count)
    (s : State) (old q : List Int)
    (hq : CommunicationIR.Corresponds input (p.initial.after.at (index memory.start memory.stride k)).entries q) :
    (p.code.loop x y n k old s q).map Prod.fst = memory.loop input x y n k old s := by
  induction n generalizing k s old q with
  | zero => rfl
  | succ n ih =>
    rw [Code.loop,SymbolicWindowLoop.Code.loop]
    dsimp only [Plan.code]
    cases hb : memory.body.eval (index memory.start memory.stride k) x y s old with
    | none => rfl
    | some t =>
      cases n with
      | zero => rfl
      | succ m =>
        have before : CommunicationIR.Corresponds input
            ((shift p.initial.after (-memory.stride)).at (index memory.start memory.stride (k+1))).entries q := by
          rw [shift_at,index_next]
          simpa only [Int.add_neg_cancel_right] using hq
        obtain ⟨eq,suffix⟩ := p.refill.correct (index memory.start memory.stride (k+1))
          (p.refillSafe (k+1) (by omega)) input old q before
        rw [execute_input (other:=fun _ => none)] at eq suffix
        cases hl : WindowFIFO.execute (fun _ => none) old
            (instantiate (index memory.start memory.stride (k+1)) p.refill.code) q with
        | none =>
          simp only [hl,Option.map_none] at eq
          simp only [hl,← eq,bind,Option.bind,Option.map_none]
        | some pair =>
          obtain ⟨vs,qs⟩ := pair
          have after := suffix vs qs hl
          rw [p.closes] at after
          simp only [hl,Option.map_some] at eq
          simp only [hl,← eq,bind,Option.bind]
          exact ih (k+1) (by omega) t vs qs after

theorem Plan.correct (p : Plan memory producer) (s : State) (q : List Int)
    (hq : CommunicationIR.Corresponds input producer.entries q) :
    (p.code.eval x y s q).map Prod.fst = memory.eval input x y s := by
  cases hc : memory.count with
  | zero => simp [Code.eval,Plan.code,SymbolicWindowLoop.Code.eval,hc]
  | succ n =>
    have initialQ : CommunicationIR.Corresponds input
        ((Sequence.mk ⟨0,producer.first⟩ producer.step ⟨0,producer.count⟩).at memory.start).entries q := by
      simpa [Sequence.at,literal_eval] using hq
    obtain ⟨eq,suffix⟩ := p.initial.correct memory.start p.initialSafe input [] q initialQ
    rw [execute_input (other:=fun _ => none)] at eq suffix
    simp only [Code.eval,Plan.code,hc,SymbolicWindowLoop.Code.eval]
    cases hl : WindowFIFO.execute (fun _ => none) [] (instantiate memory.start p.initial.code) q with
    | none =>
      simp only [hl,Option.map_none] at eq
      simp only [hl,← eq,bind,Option.bind,Option.map_none]
    | some pair =>
      obtain ⟨vs,qs⟩ := pair
      have after := suffix vs qs hl
      simp only [hl,Option.map_some] at eq
      simp only [hl,← eq,bind,Option.bind]
      have hq' : CommunicationIR.Corresponds input (p.initial.after.at (index memory.start memory.stride 0)).entries qs := by
        simpa only [index,Int.natCast_zero,Int.zero_mul,Int.add_zero] using after
      simpa only [Plan.code,hc] using p.loop_correct (x:=x) (y:=y) (n+1) 0 (by omega) s vs qs hq' 

/-- The generated program has two fixed load lists and one body, regardless
    of trip count. Endpoint checks discharge all iterations' route guards. -/
def compile (memory : SymbolicWindowLoop.Code) (producer : CompactSequence.Seq) : Option (Plan memory producer) := do
  let initial ← CompactRouting.compile memory.initial ⟨⟨0,producer.first⟩,producer.step,⟨0,producer.count⟩⟩
  let refill ← CompactRouting.compile memory.refill (shift initial.after (-memory.stride))
  if closes : refill.after = initial.after then
    if firstSafe : checkGuards initial.guards memory.start 0 1 = true then
      if restSafe : checkGuards refill.guards memory.start memory.stride memory.count = true then
        return ⟨initial,refill,closes,by
          simpa only [Int.natCast_zero,Int.zero_mul,Int.add_zero] using checkGuards_sound (k:=0) firstSafe (by omega),
          by intro k hk; exact checkGuards_sound restSafe hk⟩
      else none
    else none
  else none

end IRComparison.CompactFIFO
