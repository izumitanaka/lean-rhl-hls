import PaperCore.MemoryWindowFacts

namespace PaperCore.MemoryWindowPlan
open AccessAnalysis OrientedWindow SourcePass MemoryWindowSchedule
variable {Op : Type} {classify : Op → Option Arithmetic} {source : Source Op}

/-- Post-body shifts preserve ordinary state and establish the next window's
retained prefix. The actual emitted suffix is checked, in either direction. -/
theorem Candidate.finish (p : Candidate classify source)
    (held : Held (direction p.reverse) initial.memory initial.regs p.input (p.base k) p.buffers)
    (run : Runs meaning (shifts p.reload p.buffers) initial final) :
    Agrees p.ordinary initial final ∧
    Held (direction p.reverse) final.memory final.regs p.input (p.base (k+p.counterDelta)) p.initialBuffers := by
  obtain ⟨expected,executed,mem,nextHeld⟩ := shifts_exists p.reload p.buffers p.distinct held (meaning := meaning)
  have same := run.deterministic executed shifts_flat
  subst expected
  refine ⟨⟨fun x hx => (shifts_frame run (fun member => p.buffers_fresh x member hx)).symm,mem.symm⟩,?_⟩
  have trimmed : WindowStrideShifts.trim p.reload p.buffers = p.initialBuffers := by
    rw [← p.refill_length]
    exact WindowStrideShifts.trim_suffix
  simpa only [mem,trimmed,← p.next_base k] using nextHeld

theorem Candidate.iteration_forward (p : Candidate classify source) (ops : ArithmeticSound classify meaning)
    (atCounter : left.regs.lookup p.counter = some k)
    (agrees : Agrees p.ordinary left right)
    (held : Held (direction p.reverse) right.memory right.regs p.input (p.base k) p.initialBuffers)
    (coverage : MemoryCoverage.Covers left.memory p.input
      (p.base k+(p.overlap:Int)*direction p.reverse) (direction p.reverse) p.reload)
    (run : SourceExec meaning p.body left leftOut) :
    ∃ rightOut, SourceExec meaning p.iteration right rightOut ∧ Agrees p.ordinary leftOut rightOut ∧
      leftOut.regs.lookup p.counter = some (k+p.counterDelta-p.step) ∧
      Held (direction p.reverse) rightOut.memory rightOut.regs p.input
        (p.base (k+p.counterDelta)) p.initialBuffers := by
  have rightCounter := (agrees.registers _ p.counterMember).symm.trans atCounter
  obtain ⟨loaded,preRun,preAgrees,fullHeld⟩ := p.readPrefix_exists ops rightCounter held
    (by simpa only [← agrees.memory] using coverage)
  have view := p.layout.view fullHeld
  obtain ⟨bodyOut,bodyRun,bodyAgrees,env,bodyView⟩ := p.substitution.forward_framed ops
    (p.layout.fresh p.buffers_fresh) p.typed p.counterMember p.layout.slots_for atCounter
    (agrees.trans preAgrees) view run
  have bodyHeld := p.layout.held bodyView
  obtain ⟨final,shiftRun,_,_⟩ := shifts_exists p.reload p.buffers p.distinct bodyHeld (meaning := meaning)
  obtain ⟨shiftAgrees,nextHeld⟩ := p.finish bodyHeld shiftRun
  refine ⟨final,prepend_exec.mpr ⟨loaded,preRun,appendTo_exec.mpr ⟨bodyOut,bodyRun,shiftRun⟩⟩,
    bodyAgrees.trans shiftAgrees,?_,nextHeld⟩
  exact (bodyAgrees.registers _ p.counterMember).trans (p.counter_after env)

theorem Candidate.iteration_backward (p : Candidate classify source) (ops : ArithmeticSound classify meaning)
    (atCounter : left.regs.lookup p.counter = some k)
    (agrees : Agrees p.ordinary left right)
    (held : Held (direction p.reverse) right.memory right.regs p.input (p.base k) p.initialBuffers)
    (coverage : MemoryCoverage.Covers left.memory p.input
      (p.base k+(p.overlap:Int)*direction p.reverse) (direction p.reverse) p.reload)
    (run : SourceExec meaning p.iteration right rightOut) :
    ∃ leftOut, SourceExec meaning p.body left leftOut ∧ Agrees p.ordinary leftOut rightOut ∧
      leftOut.regs.lookup p.counter = some (k+p.counterDelta-p.step) ∧
      Held (direction p.reverse) rightOut.memory rightOut.regs p.input
        (p.base (k+p.counterDelta)) p.initialBuffers := by
  obtain ⟨loaded,preRun,remaining⟩ := prepend_exec.mp run
  obtain ⟨bodyOut,bodyRun,shiftRun⟩ := appendTo_exec.mp remaining
  have rightCounter := (agrees.registers _ p.counterMember).symm.trans atCounter
  obtain ⟨expected,expectedRun,preAgrees,fullHeld⟩ := p.readPrefix_exists ops rightCounter held
    (by simpa only [← agrees.memory] using coverage)
  have same := preRun.deterministic expectedRun p.readPrefix_flat
  subst expected
  have view := p.layout.view fullHeld
  obtain ⟨leftOut,original,bodyAgrees,env,bodyView⟩ := p.substitution.backward_framed ops
    (p.layout.fresh p.buffers_fresh) p.typed p.counterMember p.layout.slots_for atCounter
    (agrees.trans preAgrees) view bodyRun
  obtain ⟨shiftAgrees,nextHeld⟩ := p.finish (p.layout.held bodyView) shiftRun
  exact ⟨leftOut,original,bodyAgrees.trans shiftAgrees,
    (bodyAgrees.registers _ p.counterMember).trans (p.counter_after env),nextHeld⟩

#print axioms Candidate.iteration_forward
#print axioms Candidate.iteration_backward
end PaperCore.MemoryWindowPlan
