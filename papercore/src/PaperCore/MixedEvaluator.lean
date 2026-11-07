import PaperCore.MixedTarget
import PaperCore.Evaluator

namespace PaperCore.MixedTarget

def actionRun (meaning : Op → Int → Int → Int) : Action Op → State Storage → Option (State Storage)
  | .memory command, state => do
    let out ← memoryRun meaning command ⟨state.regs,state.memory.1⟩
    return memoryState out state.memory.2
  | .stream command, state => do
    let out ← streamRun command ⟨state.regs,state.memory.2⟩
    return streamState out state.memory.1

theorem actionRun_sound (success : actionRun meaning command s = some t) : Step meaning command s t := by
  cases command with
  | memory command =>
    cases h : memoryRun meaning command ⟨s.regs,s.memory.1⟩ with
    | none => simp [actionRun,h] at success
    | some out =>
      simp [actionRun,h] at success; subst t
      exact .memory (memoryRun_sound meaning h)
  | stream command =>
    cases h : streamRun command ⟨s.regs,s.memory.2⟩ with
    | none => simp [actionRun,h] at success
    | some out =>
      simp [actionRun,h] at success; subst t
      exact .stream (streamRun_sound h)

#print axioms actionRun_sound
end PaperCore.MixedTarget
