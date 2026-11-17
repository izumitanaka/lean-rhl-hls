import IRComparison.Hybrid.HybridCompactStage

namespace IRComparison.HybridRegions

/-- One region keeps its loop, initial window, refill and body. Its input is
frozen at entry; the body still operates on the current source state. -/
structure Region where
  array : Nat
  code : HybridSymbolicLoop.Code

def Region.eval (r : Region) (x y : Int) (s : State) : Option State :=
  r.code.eval (arrayInput (s.arrays r.array)) x y s

def eval (x y : Int) : List Region → State → Option State
  | [],s => some s
  | r::rs,s => (r.eval x y s).bind (eval x y rs)

def ofStages (ps : List HybridCompactStage.Stage) : List Region :=
  ps.map (fun p => ⟨p.array,p.code⟩)

/-- Loop preservation is inherited from the symbolic loop invariant, never
from enumerating the iterations or checking individual input vectors. -/
theorem ofStages_correct (ps : List HybridCompactStage.Stage)
    (sized : ∀ p ∈ ps, (s.arrays p.array).size = p.size) :
    eval x y (ofStages ps) s = HybridCompactStage.source x y ps s := by
  induction ps generalizing s with
  | nil => rfl
  | cons p ps ih =>
    have hp := p.correct s (sized p (by simp)) x y
    simp only [ofStages,List.map_cons,eval,Region.eval,HybridCompactStage.source,hp]
    cases hr : p.source x y s with
    | none => rfl
    | some t =>
      apply ih
      intro q hq
      exact (p.same (sized p (by simp)) hr q.array).symm.trans (sized q (by simp [hq]))

/-- Reuse the existing counted producer lowering with no sends. No dummy
source kernel or private source array is introduced. -/
def Region.producer (r : Region) : HybridSymbolicProducerLoop.Code :=
  ⟨r.code.start,r.code.stride,r.code.count,r.code.initial,r.code.refill,r.code.body.target⟩

theorem producer_loop (r : Region) (n k : Nat) (vs : List Int) (s : State) (q : List Int) :
    r.producer.loop input x y n k vs s q =
      (r.code.loop input x y n k vs s).map (fun t => (t,q)) := by
  induction n generalizing k vs s q with
  | zero => rfl
  | succ n ih =>
    rw [HybridSymbolicProducerLoop.Code.loop,HybridSymbolicLoop.Code.loop]
    simp only [Region.producer,HybridIR.MemoryCmd.target_correct]
    cases hb : r.code.body.eval (HybridSymbolicLoop.index r.code.start r.code.stride k) x y s vs with
    | none => rfl
    | some t =>
      cases n with
      | zero => rfl
      | succ m =>
        simp only [Option.map_some,bind,Option.bind]
        cases hl : SymbolicWindowSchedule.execute input (HybridSymbolicLoop.index r.code.start r.code.stride (k+1)) vs r.code.refill with
        | none => rfl
        | some ws => exact ih (k+1) ws t q

theorem producer_eval (r : Region) :
    r.producer.eval input x y s = (r.code.eval input x y s).map (fun t => (t,[])) := by
  cases hn : r.code.count with
  | zero => simp [Region.producer,HybridSymbolicProducerLoop.Code.eval,HybridSymbolicLoop.Code.eval,hn]
  | succ n =>
    simp only [HybridSymbolicProducerLoop.Code.eval,Region.producer,HybridSymbolicLoop.Code.eval,hn]
    cases hl : SymbolicWindowSchedule.execute input r.code.start [] r.code.initial with
    | none => rfl
    | some vs => simpa only [Region.producer,hn,bind,Option.bind] using (producer_loop (input:=input) (x:=x) (y:=y) r (n+1) 0 vs s [])

end IRComparison.HybridRegions
