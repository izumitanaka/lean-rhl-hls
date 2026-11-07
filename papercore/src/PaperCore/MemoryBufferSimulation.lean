import PaperCore.MemoryBufferBody
import PaperCore.SourceFrame
import PaperCore.LoopAnalysis

namespace PaperCore.MemoryBufferBody
open AccessAnalysis BufferView SourcePass

/-- Connect a real original state (without generated registers) to the state
whose buffer has been loaded. The body may write arbitrary other arrays. -/
theorem Prepared.forward_framed
    (p : Prepared classify slots input (Env.initial counter) source)
    (ops : ArithmeticSound classify meaning) (fresh : Fresh slots ordinary)
    (typed : Typed ordinary source) (counterTyped : ordinary counter)
    (only : BufferMemory.SlotsFor slots input)
    (atCounter : left.regs.lookup counter = some k)
    (agrees : Agrees ordinary left right) (view : View slots k right.memory right.regs)
    (run : SourceExec meaning source left leftOut) :
    ∃ rightOut, SourceExec meaning p.code right rightOut ∧ Agrees ordinary leftOut rightOut ∧
      p.after.Matches rightOut.regs k ∧ View slots k rightOut.memory rightOut.regs := by
  have rightCounter := (agrees.registers counter counterTyped).symm.trans atCounter
  obtain ⟨rightOut,original,after⟩ := execute_frame run typed agrees
  obtain ⟨equivalent,post⟩ := p.correct meaning ops ordinary fresh typed only k right rightOut
    (LoopAnalysis.Env.initial_matches rightCounter) view
  obtain ⟨env,held⟩ := post original
  exact ⟨rightOut,equivalent.mp original,after,env,held⟩

theorem Prepared.backward_framed
    (p : Prepared classify slots input (Env.initial counter) source)
    (ops : ArithmeticSound classify meaning) (fresh : Fresh slots ordinary)
    (typed : Typed ordinary source) (counterTyped : ordinary counter)
    (only : BufferMemory.SlotsFor slots input)
    (atCounter : left.regs.lookup counter = some k)
    (agrees : Agrees ordinary left right) (view : View slots k right.memory right.regs)
    (run : SourceExec meaning p.code right rightOut) :
    ∃ leftOut, SourceExec meaning source left leftOut ∧ Agrees ordinary leftOut rightOut ∧
      p.after.Matches rightOut.regs k ∧ View slots k rightOut.memory rightOut.regs := by
  have rightCounter := (agrees.registers counter counterTyped).symm.trans atCounter
  obtain ⟨equivalent,post⟩ := p.correct meaning ops ordinary fresh typed only k right rightOut
    (LoopAnalysis.Env.initial_matches rightCounter) view
  have original := equivalent.mpr run
  obtain ⟨env,held⟩ := post original
  obtain ⟨leftOut,executed,after⟩ := execute_frame original typed agrees.symm
  exact ⟨leftOut,executed,after.symm,env,held⟩

#print axioms Prepared.forward_framed
#print axioms Prepared.backward_framed
end PaperCore.MemoryBufferBody
