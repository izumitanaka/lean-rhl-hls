import PaperCore.MemoryWindowIteration
import PaperCore.LoopSimulation

namespace PaperCore.MemoryWindowPlan
open AccessAnalysis OrientedWindow SourcePass MemoryWindowSchedule
variable {Op : Type} {classify : Op → Option Arithmetic} {source : Source Op}

/-- Remaining iterations are a logical witness, not a generated counter. -/
def Candidate.Invariant (p : Candidate classify source) (left right : State Heap) : Prop :=
  Agrees p.ordinary left right ∧ ∃ k : Int, ∃ n : Nat,
    left.regs.lookup p.counter = some k ∧ p.stop = k+(n:Int)*p.counterDelta ∧
    MemoryCoverage.Covers left.memory p.input (p.base k) (direction p.reverse) (p.overlap+n*p.reload) ∧
    Held (direction p.reverse) right.memory right.regs p.input (p.base k) p.initialBuffers

theorem Candidate.advance (p : Candidate classify source)
    (endpoint : p.stop = k+((n+1:Nat):Int)*p.counterDelta)
    (coverage : MemoryCoverage.Covers left.memory p.input (p.base k) (direction p.reverse)
      (p.overlap+(n+1)*p.reload))
    (run : SourceExec meaning p.body left leftOut)
    (agrees : Agrees p.ordinary leftOut rightOut)
    (held : Held (direction p.reverse) rightOut.memory rightOut.regs p.input
      (p.base (k+p.counterDelta)) p.initialBuffers) :
    p.Invariant (leftOut.setReg p.counter (k+p.counterDelta)) (rightOut.setReg p.counter (k+p.counterDelta)) := by
  refine ⟨agrees.setReg _ _,k+p.counterDelta,n,lookup_put_same ..,?_,?_,?_⟩
  · simp only [Int.natCast_add,Int.natCast_one,Int.add_mul,Int.one_mul] at endpoint
    omega
  · have after := MemoryCoverage.covers_preserved run coverage
    have fits : p.reload+(p.overlap+n*p.reload) ≤ p.overlap+(n+1)*p.reload := by
      simp only [Nat.add_mul,Nat.one_mul]; omega
    have tail := after.subrange fits
    simpa only [p.next_base k,State.setReg] using tail
  · apply OrientedWindow.Held.set_other held
    intro member
    exact p.buffers_fresh p.counter (List.mem_append_left p.refill member) p.counterMember

theorem Candidate.loop_forward (p : Candidate classify source) (ops : ArithmeticSound classify meaning)
    (run : SourceExec meaning (.loop p.counter e p.stop p.step p.body) left leftOut)
    (equal : e.eval meaning left.regs = e.eval meaning right.regs)
    (initial : ∀ k, e.eval meaning left.regs = some k →
      p.Invariant (left.setReg p.counter k) (right.setReg p.counter k)) :
    ∃ rightOut, SourceExec meaning (.loop p.counter e p.stop p.step p.iteration) right rightOut ∧
      p.Invariant leftOut rightOut ∧ leftOut.regs.lookup p.counter = some p.stop ∧
      rightOut.regs.lookup p.counter = some p.stop := by
  apply loop_simulation meaning (MemoryStep meaning) (MemoryStep meaning) p.Invariant ?_ run equal initial
  intro left right invariant k counter notEnd leftOut bodyRun
  obtain ⟨agrees,j,n,atCounter,endpoint,coverage,held⟩ := invariant
  have same := Option.some.inj (counter.symm.trans atCounter)
  subst j
  cases n with
  | zero => simp at endpoint; exact (notEnd endpoint.symm).elim
  | succ n =>
    have fits : p.overlap+p.reload ≤ p.overlap+(n+1)*p.reload := by
      simp only [Nat.add_mul,Nat.one_mul]; omega
    have refill := coverage.subrange fits
    obtain ⟨rightOut,executed,after,bodyCounter,nextHeld⟩ := p.iteration_forward ops counter agrees held refill bodyRun
    refine ⟨rightOut,executed,?_⟩
    intro next actual
    have nextEq : next = k+p.counterDelta-p.step := Option.some.inj (actual.symm.trans bodyCounter)
    have advanceEq : next+p.step = k+p.counterDelta := by omega
    refine ⟨(after.registers _ p.counterMember).symm.trans actual,?_⟩
    rw [advanceEq]
    exact p.advance endpoint coverage bodyRun after nextHeld

theorem Candidate.loop_backward (p : Candidate classify source) (ops : ArithmeticSound classify meaning)
    (run : SourceExec meaning (.loop p.counter e p.stop p.step p.iteration) right rightOut)
    (equal : e.eval meaning left.regs = e.eval meaning right.regs)
    (initial : ∀ k, e.eval meaning left.regs = some k →
      p.Invariant (left.setReg p.counter k) (right.setReg p.counter k)) :
    ∃ leftOut, SourceExec meaning (.loop p.counter e p.stop p.step p.body) left leftOut ∧
      p.Invariant leftOut rightOut ∧ rightOut.regs.lookup p.counter = some p.stop ∧
      leftOut.regs.lookup p.counter = some p.stop := by
  apply loop_simulation meaning (MemoryStep meaning) (MemoryStep meaning)
    (fun right left => p.Invariant left right) ?_ run equal.symm ?_
  · intro right left invariant k counter notEnd rightOut bodyRun
    obtain ⟨agrees,j,n,atCounter,endpoint,coverage,held⟩ := invariant
    have sourceCounter := (agrees.registers _ p.counterMember).trans counter
    have same := Option.some.inj (sourceCounter.symm.trans atCounter)
    subst j
    cases n with
    | zero => simp at endpoint; exact (notEnd endpoint.symm).elim
    | succ n =>
      have fits : p.overlap+p.reload ≤ p.overlap+(n+1)*p.reload := by
        simp only [Nat.add_mul,Nat.one_mul]; omega
      have refill := coverage.subrange fits
      obtain ⟨leftOut,executed,after,bodyCounter,nextHeld⟩ := p.iteration_backward ops sourceCounter agrees held refill bodyRun
      refine ⟨leftOut,executed,?_⟩
      intro next actual
      have actualSource := (after.registers _ p.counterMember).trans actual
      have nextEq : next = k+p.counterDelta-p.step := Option.some.inj (actualSource.symm.trans bodyCounter)
      have advanceEq : next+p.step = k+p.counterDelta := by omega
      refine ⟨actualSource,?_⟩
      rw [advanceEq]
      exact p.advance endpoint coverage executed after nextHeld
  · intro k hk
    exact initial k (equal.trans hk)

#print axioms Candidate.loop_forward
#print axioms Candidate.loop_backward
end PaperCore.MemoryWindowPlan
