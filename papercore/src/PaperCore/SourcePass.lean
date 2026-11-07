import PaperCore.AccessAnalysis
import PaperCore.BufferNames
import PaperCore.Correspondence

namespace PaperCore.SourcePass
open AccessAnalysis

/-- Memory-to-memory passes may introduce fresh registers, but preserve every
original variable and the entire heap, including arrays later kept in memory. -/
structure Agrees (ordinary : Var → Prop) (before after : State Heap) : Prop where
  registers : ∀ x, ordinary x → before.regs.lookup x = after.regs.lookup x
  memory : before.memory = after.memory

theorem Agrees.refl (state : State Heap) : Agrees ordinary state state :=
  ⟨fun _ _ => rfl,rfl⟩

/-- Both terminating-execution directions, with no solver or FIFO assumption.
The input state is shared; the output may contain fresh buffer registers. -/
structure Correct (meaning : Op → Int → Int → Int) (ordinary : Var → Prop)
    (source transformed : Source Op) : Prop where
  forward : ∀ initial final, SourceExec meaning source initial final →
    ∃ result, SourceExec meaning transformed initial result ∧ Agrees ordinary final result
  backward : ∀ initial result, SourceExec meaning transformed initial result →
    ∃ final, SourceExec meaning source initial final ∧ Agrees ordinary final result

structure Prepared (classify : Op → Option Arithmetic) (source : Source Op) where
  code : Source Op
  names : ∀ x ∈ BufferNames.sourceVars source, x ∈ BufferNames.sourceVars code
  correct : ∀ meaning, ArithmeticSound classify meaning →
    Correct meaning (fun x => x ∈ BufferNames.sourceVars source) source code

def identity (classify : Op → Option Arithmetic) (source : Source Op) : Prepared classify source :=
  ⟨source,fun _ h => h,fun _ _ =>
    ⟨fun _ out run => ⟨out,run,Agrees.refl out⟩,
     fun _ out run => ⟨out,run,Agrees.refl out⟩⟩⟩

/-- Compose independently proved source passes before deciding any storage
policy. Neither pass is re-run when the FIFO policy changes. -/
def Prepared.then (first : Prepared classify source) (second : Prepared classify first.code) :
    Prepared classify source where
  code := second.code
  names := fun x hx => second.names x (first.names x hx)
  correct := by
    intro meaning ops
    constructor
    · intro initial final run
      obtain ⟨middle,runMiddle,agreeMiddle⟩ := (first.correct meaning ops).forward _ _ run
      obtain ⟨result,runResult,agreeResult⟩ := (second.correct meaning ops).forward _ _ runMiddle
      exact ⟨result,runResult,⟨fun x hx => (agreeMiddle.registers x hx).trans
        (agreeResult.registers x (first.names x hx)),agreeMiddle.memory.trans agreeResult.memory⟩⟩
    · intro initial result run
      obtain ⟨middle,runMiddle,agreeResult⟩ := (second.correct meaning ops).backward _ _ run
      obtain ⟨final,runFinal,agreeMiddle⟩ := (first.correct meaning ops).backward _ _ runMiddle
      exact ⟨final,runFinal,⟨fun x hx => (agreeMiddle.registers x hx).trans
        (agreeResult.registers x (first.names x hx)),agreeMiddle.memory.trans agreeResult.memory⟩⟩

end PaperCore.SourcePass
