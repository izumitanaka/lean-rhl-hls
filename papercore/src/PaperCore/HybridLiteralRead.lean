import PaperCore.HybridRules
import PaperCore.QueueInterface

namespace PaperCore.Hybrid.LiteralRead
open QueueInterface

def Ready (queues : Queues) (array : Array) (index : Int) : Prop :=
  0 < (queues array).count.toNat ∧ (queues array).first = index
instance : Decidable (Ready queues array index) := inferInstanceAs (Decidable (_ ∧ _))

def output (queues : Queues) (array : Array) : Queues :=
  fun a => if a = array then drop (queues array) 1 else queues a

theorem correct (selected : array ∈ arrays) (ready : Ready queues array index) :
    Translation meaning ordinary (fun a => a ∈ arrays) (Holds arrays queues)
      (.action (.read dest array (.num index))) (.action (.stream (.read dest array)))
      (Holds arrays (output queues array)) := by
  intro left right indices initial
  obtain ⟨positive,firstEq⟩ := ready
  cases countEq : (queues array).count.toNat with
  | zero => omega
  | succ n =>
    let tail := IndexSequence.entries ((queues array).first+(queues array).step) (queues array).step n
    have sequence : (queues array).sequence = index :: tail := by
      simp only [IndexSequence.Values.sequence,countEq,IndexSequence.entries,tail,firstEq]
    have head : indices.lookup array = some (index :: tail) := (initial.2 array selected).trans (congrArg some sequence)
    obtain ⟨value,rest,cell,queue,after⟩ := initial.1.pop selected head dest
    let target : State MixedTarget.Storage := ⟨put right.regs dest value,(right.memory.1,put right.memory.2 array rest)⟩
    have sourceStep : SourceExec meaning (.action (.read dest array (.num index))) left (left.setReg dest value) :=
      .action (.read rfl cell)
    have targetStep : MixedTarget.Step meaning (.stream (.read dest array)) right target :=
      stream_step_iff.mpr ⟨StreamStep.read queue,rfl⟩
    have post : Holds arrays (output queues array) target.regs left.memory (put indices array tail) := by
      intro a member
      by_cases same : a = array
      · subst a
        rw [lookup_put_same]
        simp [output,drop_sequence,sequence]
      · rw [lookup_put_other _ _ _ _ same]
        simpa only [output,if_neg same] using initial.2 a member
    constructor
    · intro out run
      have same := memoryAction_unique run sourceStep
      subst out
      exact ⟨target,put indices array tail,.action targetStep,after,post⟩
    · intro out run
      cases run with
      | action step =>
        have same := step_deterministic step targetStep
        subst out
        exact ⟨left.setReg dest value,put indices array tail,sourceStep,after,post⟩

#print axioms correct
end PaperCore.Hybrid.LiteralRead
