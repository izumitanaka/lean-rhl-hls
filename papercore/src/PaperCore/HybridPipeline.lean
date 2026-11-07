import PaperCore.HybridStage
import PaperCore.ProgramState

namespace PaperCore.Hybrid.Pipeline
open AccessAnalysis QueueInterface SolverReply

open ProgramState (sourceArrays emptyStreams lookup_empty)

/-- Composition follows the actual sequence tree, with no stage-count limit
    or producer/filter/consumer position tags. -/
inductive Plan (classify : Op → Option Arithmetic) (variables arrays : List String) : Source Op → Type where
  | assign (dest : Var) (expr : Expr Op) (typed : expr.ordinary (fun x => x ∈ variables)) :
      Plan classify variables arrays (.assign dest expr)
  | branch (condition : Var) (typed : condition ∈ variables)
      (yes : Plan classify variables arrays a) (no : Plan classify variables arrays b) :
      Plan classify variables arrays (.branch condition a b)
  | kernel (body : Plan classify variables arrays bodySource) :
      Plan classify variables arrays (.kernel bodySource)
  | leaf (stage : Stage.Prepared classify variables arrays source) : Plan classify variables arrays source
  | seq (left : Plan classify variables arrays a) (right : Plan classify variables arrays b) :
      Plan classify variables arrays (.seq a b)

variable {Op : Type} {classify : Op → Option Arithmetic} {source : Source Op}

def prepare (classify : Op → Option Arithmetic) (variables arrays : List String) (source : Source Op) :
    Except String (Plan classify variables arrays source) :=
  match source with
  | .seq a b => do
    let left ← prepare classify variables arrays a
    let right ← prepare classify variables arrays b
    return .seq left right
  | .branch condition a b => do
    if typed : condition ∈ variables then
      return .branch condition typed (← prepare classify variables arrays a) (← prepare classify variables arrays b)
    else .error "branch-condition-not-in-program"
  | .kernel body => do return .kernel (← prepare classify variables arrays body)
  | .assign dest expr =>
    if names : (BufferNames.exprVars expr).all (fun x => decide (x ∈ variables)) = true then
      .ok (.assign dest expr (BufferNames.expr_typed (fun x hx => by simpa using List.all_eq_true.mp names x hx)))
    else .error "scalar-variable-not-in-program"
  | other => do return .leaf (← Stage.prepareFifoOnly classify variables arrays other)

def prepareClosed (classify : Op → Option Arithmetic) (source : Source Op) (arrays : List Array) :
    Except String (Plan classify (BufferNames.sourceVars source) arrays source) :=
  prepare classify (BufferNames.sourceVars source) arrays source

def Plan.code {source : Source Op} : Plan classify variables arrays source → MixedTarget.Code Op
  | .assign dest expr _ => .assign dest expr
  | .branch condition _ yes no => .branch condition yes.code no.code
  | .kernel body => .kernel body.code
  | .leaf stage => stage.code
  | .seq left right => .seq left.code right.code

def Replies {source : Source Op} : Plan classify variables arrays source → Type
  | .assign .. => Unit
  | .branch _ _ yes no => Replies yes × Replies no
  | .kernel body => Replies body
  | .leaf _ => Reply
  | .seq left right => Replies left × Replies right

def SoundReplies {source : Source Op} : (plan : Plan classify variables arrays source) → Replies plan → Prop
  | .assign ..,_ => True
  | .branch _ _ yes no,replies => SoundReplies yes replies.1 ∧ SoundReplies no replies.2
  | .kernel body,replies => SoundReplies body replies
  | .leaf _,reply => PaperCore.SMTConnection.SolverReplySound reply.request reply.response
  | .seq left right,replies => SoundReplies left replies.1 ∧ SoundReplies right replies.2

def Plan.accept {source : Source Op} (plan : Plan classify variables arrays source) (queues : Queues) (replies : Replies plan) : Option Queues :=
  match plan with
  | .assign .. => some queues
  | .branch _ _ yes no => do
    let yesQueues ← yes.accept queues replies.1
    let noQueues ← no.accept queues replies.2
    if QueueInterface.equal arrays yesQueues noQueues then some yesQueues else none
  | .kernel body => body.accept queues replies
  | .leaf stage => stage.accept queues replies
  | .seq left right => do
    let middle ← left.accept queues replies.1
    right.accept middle replies.2

def Plan.build (plan : Plan classify variables arrays source) (queues : Queues) (replies : Replies plan) : Option (MixedTarget.Code Op × Queues) := do
  let after ← plan.accept queues replies
  return (plan.code,after)

theorem Plan.accept_correct (plan : Plan classify variables arrays source) (ops : ArithmeticSound classify meaning)
    {replies : Replies plan}
    (success : plan.accept queues replies = some after) (solver : SoundReplies plan replies) :
    Translation meaning (fun x => x ∈ variables) (fun a => a ∈ arrays) (Holds arrays queues)
      source plan.code (Holds arrays after) := by
  induction plan generalizing queues after with
  | assign dest expr typed =>
    simp [Plan.accept] at success; subst after
    intro left right indices initial
    constructor
    · intro out run
      cases run with
      | assign value =>
        exact ⟨right.setReg dest _,indices,.assign ((initial.1.eval_eq meaning expr typed).symm.trans value),initial.1.setReg dest _,initial.2⟩
    · intro out run
      cases run with
      | assign value =>
        exact ⟨left.setReg dest _,indices,.assign ((initial.1.eval_eq meaning expr typed).trans value),initial.1.setReg dest _,initial.2⟩
  | branch condition typed yes no ihYes ihNo =>
    cases hy : yes.accept queues replies.1 with
    | none => simp [Plan.accept,hy] at success
    | some yesQueues =>
      cases hn : no.accept queues replies.2 with
      | none => simp [Plan.accept,hy,hn] at success
      | some noQueues =>
        by_cases same : QueueInterface.equal arrays yesQueues noQueues = true
        · simp [Plan.accept,hy,hn,same] at success; subst after
          apply Translation.branch typed
          · apply Translation.consequence (ihYes hy solver.1)
            · intro regs heap indices guarded; exact guarded.1
            · intro regs heap indices holds; exact holds
          · apply Translation.consequence (ihNo hn solver.2)
            · intro regs heap indices guarded; exact guarded.1
            · intro regs heap indices holds a member
              exact (holds a member).trans (congrArg some (QueueInterface.equal_correct.mp same a member).symm)
        · simp [Plan.accept,hy,hn,same] at success
  | kernel body ih => exact Translation.kernel (ih success solver)
  | leaf stage => exact stage.accept_correct ops success solver
  | seq left right ihLeft ihRight =>
    cases ha : left.accept queues replies.1 with
    | none => simp [Plan.accept,ha] at success
    | some middle =>
      have hb : right.accept middle replies.2 = some after := by simpa [Plan.accept,ha] using success
      exact Translation.seq (ihLeft ha solver.1) (ihRight hb solver.2)

theorem Plan.build_correct (plan : Plan classify variables arrays source) (ops : ArithmeticSound classify meaning)
    {replies : Replies plan}
    (success : plan.build queues replies = some (targetCode,after)) (solver : SoundReplies plan replies) :
    Translation meaning (fun x => x ∈ variables) (fun a => a ∈ arrays) (Holds arrays queues)
      source targetCode (Holds arrays after) := by
  cases accepted : plan.accept queues replies with
  | none => simp [Plan.build,accepted] at success
  | some output =>
    have same : plan.code = targetCode ∧ output = after := by simpa [Plan.build,accepted] using success
    obtain ⟨rfl,rfl⟩ := same
    exact plan.accept_correct ops accepted solver

theorem empty_related (variables arrays : List String) (regs : Registers) :
    Related (fun x => x ∈ variables) (fun a => a ∈ arrays) (Holds arrays empty)
      ⟨regs,[]⟩ ⟨regs,([],emptyStreams arrays)⟩ (emptyStreams arrays) := by
  refine ⟨⟨⟨fun _ _ => rfl,?_⟩,by intros; rfl⟩,?_⟩
  · intro a member
    exact ⟨[],[],lookup_empty arrays member,lookup_empty arrays member,by simp,.nil⟩
  · intro a member; exact lookup_empty arrays member

theorem Plan.build_closed_forward
    (plan : Plan classify (BufferNames.sourceVars source) arrays source)
    (ops : ArithmeticSound classify meaning)
    {replies : Replies plan}
    (success : plan.build empty replies = some (targetCode,after)) (solver : SoundReplies plan replies)
    (run : SourceExec meaning source ⟨regs,[]⟩ out) :
    ∃ targetOut indices, MixedTarget.Execution meaning targetCode ⟨regs,([],emptyStreams arrays)⟩ targetOut ∧
      Related (fun x => x ∈ BufferNames.sourceVars source) (fun a => a ∈ arrays)
        (Holds arrays after) out targetOut indices := by
  exact (plan.build_correct ops success solver _ _ _ (empty_related _ _ regs)).1 out run

theorem Plan.build_closed_backward
    (plan : Plan classify (BufferNames.sourceVars source) arrays source)
    (ops : ArithmeticSound classify meaning)
    {replies : Replies plan}
    (success : plan.build empty replies = some (targetCode,after)) (solver : SoundReplies plan replies)
    (run : MixedTarget.Execution meaning targetCode ⟨regs,([],emptyStreams arrays)⟩ targetOut) :
    ∃ out indices, SourceExec meaning source ⟨regs,[]⟩ out ∧
      Related (fun x => x ∈ BufferNames.sourceVars source) (fun a => a ∈ arrays)
        (Holds arrays after) out targetOut indices := by
  exact (plan.build_correct ops success solver _ _ _ (empty_related _ _ regs)).2 targetOut run

#print axioms Plan.build_correct
#print axioms Plan.build_closed_forward
#print axioms Plan.build_closed_backward
end PaperCore.Hybrid.Pipeline
