import PaperCore.MemoryWindowLoop

namespace PaperCore.MemoryWindowPlan
open AccessAnalysis OrientedWindow SourcePass MemoryWindowSchedule
variable {Op : Type} {classify : Op → Option Arithmetic} {source : Source Op}

def Candidate.startPrefix (p : Candidate classify source) : List (Source Op) :=
  literalLoads p.input (p.base p.start) (direction p.reverse) p.initialBuffers

theorem Candidate.startPrefix_flat (p : Candidate classify source) : ∀ c ∈ p.startPrefix, Flat c :=
  literalLoads_flat

theorem Candidate.startPrefix_exists (p : Candidate classify source)
    (nonempty : p.start ≠ p.stop) (coverage : p.covered initial.memory) :
    ∃ final, Runs meaning p.startPrefix initial final ∧ Agrees p.ordinary initial final ∧
      Held (direction p.reverse) final.memory final.regs p.input (p.base p.start) p.initialBuffers := by
  have all : MemoryCoverage.Covers initial.memory p.input (p.base p.start) (direction p.reverse)
      (p.overlap+p.trips*p.reload) := by
    simpa [Candidate.covered,nonempty,Candidate.base] using coverage
  have part := all.subrange (offset := 0) (length := p.overlap) (by omega)
  have initialCoverage : MemoryCoverage.Covers initial.memory p.input (p.base p.start) (direction p.reverse) p.initialBuffers.length := by
    simpa [p.initial_length] using part
  obtain ⟨final,loaded,mem,held⟩ := literalLoads_exists p.initialBuffers
    (List.nodup_append.mp p.distinct).1 initialCoverage (meaning := meaning)
  refine ⟨final,loaded,⟨?_,mem.symm⟩,held⟩
  intro x hx
  exact ((literalLoads_frame loaded (fun h => p.buffers_fresh x (List.mem_append_left _ h) hx)).1).symm

theorem Candidate.startInvariant (p : Candidate classify source) (nonempty : p.start ≠ p.stop)
    (coverage : p.covered initial.memory) (agrees : Agrees p.ordinary initial loaded)
    (held : Held (direction p.reverse) loaded.memory loaded.regs p.input (p.base p.start) p.initialBuffers) :
    p.Invariant (initial.setReg p.counter p.start) (loaded.setReg p.counter p.start) := by
  refine ⟨agrees.setReg _ _,p.start,p.trips,lookup_put_same ..,p.endpoint,?_,?_⟩
  · simpa [Candidate.covered,nonempty,Candidate.base,State.setReg] using coverage
  · apply OrientedWindow.Held.set_other held
    intro member
    exact p.buffers_fresh _ (List.mem_append_left _ member) p.counterMember

/-- The actual generated memory program, including initialization. Coverage
is an explicit precondition to be established by preceding program analysis. -/
theorem Candidate.program_forward (p : Candidate classify source) (ops : ArithmeticSound classify meaning)
    (coverage : p.covered initial.memory) (run : SourceExec meaning source initial final) :
    ∃ transformed, SourceExec meaning p.code initial transformed ∧ Agrees p.ordinary final transformed := by
  by_cases empty : p.start = p.stop
  · exact ⟨final,by simpa [Candidate.code,empty] using run,Agrees.refl final⟩
  · obtain ⟨loaded,prefixRun,agrees,held⟩ := p.startPrefix_exists empty coverage (meaning := meaning)
    have loopRun := p.original ▸ run
    obtain ⟨transformed,executed,inv,_,_⟩ := p.loop_forward ops loopRun (right := loaded) rfl
      (by intro k hk; simp [Expr.eval] at hk; subst k; exact p.startInvariant empty coverage agrees held)
    refine ⟨transformed,?_,inv.1⟩
    simp only [Candidate.code,if_neg empty]
    exact prepend_exec.mpr ⟨loaded,prefixRun,executed⟩

theorem Candidate.program_backward (p : Candidate classify source) (ops : ArithmeticSound classify meaning)
    (coverage : p.covered initial.memory) (run : SourceExec meaning p.code initial transformed) :
    ∃ final, SourceExec meaning source initial final ∧ Agrees p.ordinary final transformed := by
  by_cases empty : p.start = p.stop
  · exact ⟨transformed,by simpa [Candidate.code,empty] using run,Agrees.refl transformed⟩
  · simp only [Candidate.code,if_neg empty] at run
    obtain ⟨loaded,prefixRun,loopRun⟩ := prepend_exec.mp run
    obtain ⟨expected,expectedRun,agrees,held⟩ := p.startPrefix_exists empty coverage (meaning := meaning)
    have same := prefixRun.deterministic expectedRun p.startPrefix_flat
    subst expected
    obtain ⟨final,executed,inv,_,_⟩ := p.loop_backward ops loopRun (left := initial) rfl
      (by intro k hk; simp [Expr.eval] at hk; subst k; exact p.startInvariant empty coverage agrees held)
    exact ⟨final,p.original.symm ▸ executed,inv.1⟩

#print axioms Candidate.program_forward
#print axioms Candidate.program_backward
end PaperCore.MemoryWindowPlan
