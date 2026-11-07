import PaperCore.HybridPipeline

namespace PaperCore.Hybrid.Alternatives
open AccessAnalysis QueueInterface SolverReply
open Pipeline (Plan empty_related)
open ProgramState (emptyStreams)

/-- Logical disjunction of queue interfaces. It does not store or reread the
    runtime branch condition, which either branch is allowed to overwrite. -/
def HoldsAny (arrays : List Array) (alternatives : List Queues) : Assertion :=
  fun regs heap indices => ∃ queues ∈ alternatives, Holds arrays queues regs heap indices

theorem lift (valid : ∀ queues ∈ before, ∃ afterQueues ∈ after,
    Translation meaning ordinary (fun a => a ∈ arrays) (Holds arrays queues) source target (Holds arrays afterQueues)) :
    Translation meaning ordinary (fun a => a ∈ arrays) (HoldsAny arrays before) source target (HoldsAny arrays after) := by
  intro left right indices initial
  obtain ⟨queues,member,holds⟩ := initial.2
  obtain ⟨output,outputMember,certified⟩ := valid queues member
  have both := certified left right indices ⟨initial.1,holds⟩
  constructor
  · intro out run
    obtain ⟨out',afterIndices,executed,related⟩ := both.1 out run
    exact ⟨out',afterIndices,executed,related.1,output,outputMember,related.2⟩
  · intro out run
    obtain ⟨out',afterIndices,executed,related⟩ := both.2 out run
    exact ⟨out',afterIndices,executed,related.1,output,outputMember,related.2⟩

variable {Op : Type} {classify : Op → Option Arithmetic} {source : Source Op}

def acceptMany (stage : Stage.Prepared classify variables arrays source) : List Queues → List Reply → Option (List Queues)
  | [],[] => some []
  | queues :: rest,reply :: replies => do
    let after ← stage.accept queues reply
    let remaining ← acceptMany stage rest replies
    return after :: remaining
  | _,_ => none

theorem acceptMany_witness (stage : Stage.Prepared classify variables arrays source)
    (success : acceptMany stage before replies = some after)
    (member : queues ∈ before) :
    ∃ output ∈ after, ∃ reply ∈ replies, stage.accept queues reply = some output := by
  induction before generalizing replies after with
  | nil => simp at member
  | cons head rest ih =>
    cases replies with
    | nil => simp [acceptMany] at success
    | cons reply replies =>
      cases ha : stage.accept head reply with
      | none => simp [acceptMany,ha] at success
      | some output =>
        cases hr : acceptMany stage rest replies with
        | none => simp [acceptMany,ha,hr] at success
        | some tail =>
          simp [acceptMany,ha,hr] at success; subst after
          rcases List.mem_cons.mp member with same | later
          · subst queues; exact ⟨output,by simp,reply,by simp,ha⟩
          · obtain ⟨out,hm,r,hrm,accepted⟩ := ih hr later
            exact ⟨out,List.mem_cons_of_mem _ hm,r,List.mem_cons_of_mem _ hrm,accepted⟩

def Replies {source : Source Op} : Plan classify variables arrays source → Type
  | .assign .. => Unit
  | .kernel body => Replies body
  | .leaf _ => List Reply
  | .seq a b => Replies a × Replies b
  | .branch _ _ a b => Replies a × Replies b

def SoundReplies {source : Source Op} (plan : Plan classify variables arrays source) (replies : Replies plan) : Prop :=
  match plan with
  | .assign .. => True
  | .kernel body => SoundReplies body replies
  | .leaf stage => ∀ (reply : Reply), reply ∈ (show List Reply from replies) → PaperCore.SMTConnection.SolverReplySound reply.request reply.response
  | .seq a b => SoundReplies a replies.1 ∧ SoundReplies b replies.2
  | .branch _ _ a b => SoundReplies a replies.1 ∧ SoundReplies b replies.2

/-- Each subsequent region is checked against every possible incoming queue.
    Its generated code stays the same for every interface and every model. -/
def accept {source : Source Op} (plan : Plan classify variables arrays source) (before : List Queues) (replies : Replies plan) : Option (List Queues) :=
  match plan with
  | .assign .. => some before
  | .kernel body => accept body before replies
  | .leaf stage => acceptMany stage before replies
  | .seq a b => do
    let middle ← accept a before replies.1
    accept b middle replies.2
  | .branch _ _ a b => do
    let yes ← accept a before replies.1
    let no ← accept b before replies.2
    return yes ++ no

theorem accept_correct (plan : Plan classify variables arrays source) (ops : ArithmeticSound classify meaning)
    {replies : Replies plan}
    (success : accept plan before replies = some after) (solver : SoundReplies plan replies) :
    Translation meaning (fun x => x ∈ variables) (fun a => a ∈ arrays) (HoldsAny arrays before)
      source plan.code (HoldsAny arrays after) := by
  induction plan generalizing before after with
  | assign dest expr typed =>
    simp [accept] at success; subst after
    apply lift
    intro queues member
    exact ⟨queues,member,Pipeline.Plan.accept_correct (.assign dest expr typed) ops (replies := ()) rfl True.intro⟩
  | kernel body ih => exact Translation.kernel (ih success solver)
  | leaf stage =>
    apply lift
    intro queues member
    obtain ⟨output,hm,reply,hr,accepted⟩ := acceptMany_witness stage success member
    exact ⟨output,hm,stage.accept_correct ops accepted (solver reply hr)⟩
  | seq a b ia ib =>
    cases ha : accept a before replies.1 with
    | none => simp [accept,ha] at success
    | some middle =>
      have hb : accept b middle replies.2 = some after := by simpa [accept,ha] using success
      exact Translation.seq (ia ha solver.1) (ib hb solver.2)
  | branch condition typed a b ia ib =>
    cases ha : accept a before replies.1 with
    | none => simp [accept,ha] at success
    | some yes =>
      cases hb : accept b before replies.2 with
      | none => simp [accept,ha,hb] at success
      | some no =>
        simp [accept,ha,hb] at success; subst after
        apply Translation.branch typed
        · apply Translation.consequence (ia ha solver.1)
          · intro regs heap indices guarded; exact guarded.1
          · rintro regs heap indices ⟨queues,member,holds⟩
            exact ⟨queues,List.mem_append_left _ member,holds⟩
        · apply Translation.consequence (ib hb solver.2)
          · intro regs heap indices guarded; exact guarded.1
          · rintro regs heap indices ⟨queues,member,holds⟩
            exact ⟨queues,List.mem_append_right _ member,holds⟩

def build (plan : Plan classify variables arrays source) (before : List Queues) (replies : Replies plan) : Option (MixedTarget.Code Op × List Queues) := do
  let after ← accept plan before replies
  return (plan.code,after)

theorem build_correct (plan : Plan classify variables arrays source) (ops : ArithmeticSound classify meaning)
    {replies : Replies plan}
    (success : build plan before replies = some (targetCode,after)) (solver : SoundReplies plan replies) :
    Translation meaning (fun x => x ∈ variables) (fun a => a ∈ arrays) (HoldsAny arrays before)
      source targetCode (HoldsAny arrays after) := by
  cases accepted : accept plan before replies with
  | none => simp [build,accepted] at success
  | some outputs =>
    have same : plan.code = targetCode ∧ outputs = after := by simpa [build,accepted] using success
    obtain ⟨rfl,rfl⟩ := same
    exact accept_correct plan ops accepted solver

theorem build_closed_forward
    (plan : Plan classify (BufferNames.sourceVars source) arrays source)
    (ops : ArithmeticSound classify meaning) {replies : Replies plan}
    (success : build plan [QueueInterface.empty] replies = some (targetCode,after)) (solver : SoundReplies plan replies)
    (run : SourceExec meaning source ⟨regs,[]⟩ out) :
    ∃ targetOut indices, MixedTarget.Execution meaning targetCode ⟨regs,([],emptyStreams arrays)⟩ targetOut ∧
      Related (fun x => x ∈ BufferNames.sourceVars source) (fun a => a ∈ arrays)
        (HoldsAny arrays after) out targetOut indices := by
  have initial := empty_related (BufferNames.sourceVars source) arrays regs
  exact (build_correct plan ops success solver _ _ _ ⟨initial.1,QueueInterface.empty,by simp,initial.2⟩).1 out run

theorem build_closed_backward
    (plan : Plan classify (BufferNames.sourceVars source) arrays source)
    (ops : ArithmeticSound classify meaning) {replies : Replies plan}
    (success : build plan [QueueInterface.empty] replies = some (targetCode,after)) (solver : SoundReplies plan replies)
    (run : MixedTarget.Execution meaning targetCode ⟨regs,([],emptyStreams arrays)⟩ targetOut) :
    ∃ out indices, SourceExec meaning source ⟨regs,[]⟩ out ∧
      Related (fun x => x ∈ BufferNames.sourceVars source) (fun a => a ∈ arrays)
        (HoldsAny arrays after) out targetOut indices := by
  have initial := empty_related (BufferNames.sourceVars source) arrays regs
  exact (build_correct plan ops success solver _ _ _ ⟨initial.1,QueueInterface.empty,by simp,initial.2⟩).2 targetOut run

#print axioms accept_correct
#print axioms build_closed_forward
#print axioms build_closed_backward
end PaperCore.Hybrid.Alternatives
