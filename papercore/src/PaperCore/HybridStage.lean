import PaperCore.HybridLiteralRead
import PaperCore.HybridPreparedLoop
import PaperCore.HybridRetain
import PaperCore.ProgramState
import PaperCore.SolverReply

namespace PaperCore.Hybrid.Stage
open AccessAnalysis QueueInterface

/-- Each source array has one storage decision across every stage. -/
def policy (arrays : List Array) : Array → Bool := fun a => decide (a ∈ arrays)

structure Prepared (classify : Op → Option Arithmetic) (variables arrays : List String) (source : Source Op) where
  code : MixedTarget.Code Op
  query : Queues → PaperCore.SMT
  output : Queues → (String → Int) → Queues
  correct : ∀ (meaning : Op → Int → Int → Int), ArithmeticSound classify meaning →
    ∀ {zero params vars queues}, PaperCore.SMTMeaning.eval zero params vars (query queues) = .boolean true →
      Translation meaning (fun x => x ∈ variables) (fun a => a ∈ arrays) (Holds arrays queues)
        source code (Holds arrays (output queues params))

variable {Op : Type} {classify : Op → Option Arithmetic} {source : Source Op}

def directInput (p : PreparedLoop.Prepared (policy arrays) classify source) (queues : Queues) : PreparedLoop.Interface :=
  ⟨queues,min p.start p.stop,max p.start p.stop⟩

def directOutput (p : PreparedLoop.Prepared (policy arrays) classify source) (queues : Queues) (params : String → Int) : Queues :=
  fun a => if a ∈ p.arrays then BodyCursorSMT.values params (PreparedLoop.layout a) p.exitCoordinate else queues a

theorem direct_tracked (p : PreparedLoop.Prepared (policy arrays) classify source) (member : a ∈ p.arrays) : a ∈ arrays := by
  simp only [PreparedLoop.Prepared.arrays,List.mem_eraseDups,List.mem_map] at member
  obtain ⟨event,he,rfl⟩ := member
  have h := (List.mem_filter.mp he).2
  simpa [policy] using h

theorem direct_correct (p : PreparedLoop.Prepared (policy arrays) classify source) (ops : ArithmeticSound classify meaning)
    (typed : BufferView.Typed ordinary p.body) (counterTyped : ordinary p.counter)
    (model : PaperCore.SMTMeaning.eval zero params vars (PreparedLoop.query p (directInput p queues)) = .boolean true) :
    Translation meaning ordinary (fun a => a ∈ arrays) (Holds arrays queues) source p.code
      (Holds arrays (directOutput p queues params)) := by
  have certified := PreparedLoop.model_correct_framed p ops typed counterTyped model
    (fun indices => ∀ a ∈ arrays, a ∉ p.arrays → indices.lookup a = some (queues a).sequence)
    (by intro before after frame initial a member untouched; exact (frame a untouched).trans (initial a member untouched))
  simp only [policy,decide_eq_true_eq] at certified
  apply Translation.consequence certified
  · intro regs heap indices initial
    exact ⟨fun a ha => initial a (direct_tracked p ha),fun a ha _ => initial a ha⟩
  · intro regs heap indices final a member
    obtain ⟨⟨k,value,shape,untouched⟩,finished⟩ := final
    have same : k = p.stop := Option.some.inj (value.symm.trans finished)
    subst k
    by_cases touched : a ∈ p.arrays
    · simpa [directOutput,touched] using PreparedLoop.shape_at_end p shape a touched
    · simpa [directOutput,touched] using untouched a member touched

def prepareDirect (classify : Op → Option Arithmetic) (variables arrays : List String) (source : Source Op) :
    Except String (Prepared classify variables arrays source) := do
  let p ← PreparedLoop.prepare (policy arrays) classify source
  if names : (p.counter :: BufferNames.sourceVars p.body).all (fun x => decide (x ∈ variables)) = true then
    let typed : ∀ x ∈ p.counter :: BufferNames.sourceVars p.body, x ∈ variables :=
      fun x hx => by simpa using List.all_eq_true.mp names x hx
    return ⟨p.code,fun q => PreparedLoop.query p (directInput p q),directOutput p,
      fun meaning ops {zero params vars queues} model => direct_correct p ops
        (BufferNames.source_typed _ (fun x hx => typed x (List.mem_cons_of_mem _ hx)))
        (typed p.counter (by simp)) model⟩
  else .error "hybrid-stage-variables-not-in-program"

/-- A retained region needs no access-pattern approximation. It may contain
arbitrary existing branches and loops; only its storage/frame condition is checked. -/
def prepareRetained (classify : Op → Option Arithmetic) (variables arrays : List String) (source : Source Op) :
    Except String (Prepared classify variables arrays source) :=
  if retained : (ProgramState.sourceArrays source).all (fun a => decide (a ∉ arrays)) = true then
    if names : (BufferNames.sourceVars source).all (fun x => decide (x ∈ variables)) = true then
      .ok ⟨MixedTarget.retain source,fun _ => PaperCore.SMT.conj [],fun q _ => q,
        fun meaning _ {_ _ _ queues} _ => retain_correct source
          (BufferNames.source_typed _ (fun x hx => by simpa using List.all_eq_true.mp names x hx))
          (fun a ha => by simpa using List.all_eq_true.mp retained a ha)
          (fun indices => ∀ a ∈ arrays, indices.lookup a = some (queues a).sequence)⟩
    else .error "hybrid-retained-variables-not-in-program"
  else .error "hybrid-retained-region-touches-fifo"

/-- A statically addressed preload is a normal source memory read. -/
def prepareLiteralRead (classify : Op → Option Arithmetic) (variables arrays : List String)
    (dest : Var) (array : Array) (index : Int) (selected : array ∈ arrays) :
    Prepared classify variables arrays (.action (.read dest array (.num index))) where
  code := .action (.stream (.read dest array))
  query := fun queues => if LiteralRead.Ready queues array index then .truth else .disj []
  output := fun queues _ => LiteralRead.output queues array
  correct := by
    intro meaning ops zero params vars queues model
    by_cases ready : LiteralRead.Ready queues array index
    · exact LiteralRead.correct selected ready
    · simp [ready,PaperCore.SMT.disj,PaperCore.SMTMeaning.eval,
        PaperCore.SMTMeaning.operation,PaperCore.SMTMeaning.booleans] at model

/-- FIFO selection after an independent source-to-source buffer pass. This
entry point never inserts or removes buffers: unselected regions remain exactly
as supplied, selected actions use the direct mixed lowering. -/
def prepareFifoOnly (classify : Op → Option Arithmetic) (variables arrays : List String)
    (source : Source Op) : Except String (Prepared classify variables arrays source) :=
  if (ProgramState.sourceArrays source).all (fun a => decide (a ∉ arrays)) then
    prepareRetained classify variables arrays source
  else match source with
    | .action (.read dest array (.num index)) =>
      if selected : array ∈ arrays then .ok (prepareLiteralRead classify variables arrays dest array index selected)
      else prepareRetained classify variables arrays (.action (.read dest array (.num index)))
    | other => prepareDirect classify variables arrays other

def Prepared.accept (p : Prepared classify variables arrays source) (queues : Queues) (reply : SolverReply.Reply) : Option Queues := do
  let bindings ← PaperCore.SMTConnection.acceptResponse (p.query queues) reply.request reply.response
  return p.output queues (SolverReply.parameters bindings)

theorem Prepared.accept_correct (p : Prepared classify variables arrays source) (ops : ArithmeticSound classify meaning)
    (success : p.accept queues reply = some after)
    (solver : PaperCore.SMTConnection.SolverReplySound reply.request reply.response) :
    Translation meaning (fun x => x ∈ variables) (fun a => a ∈ arrays) (Holds arrays queues)
      source p.code (Holds arrays after) := by
  unfold Prepared.accept at success
  cases accepted : PaperCore.SMTConnection.acceptResponse (p.query queues) reply.request reply.response with
  | none => simp [accepted] at success
  | some bindings =>
    simp [accepted] at success; subst after
    obtain ⟨zero,model⟩ := PaperCore.SMTConnection.acceptResponse_sound accepted solver
    exact p.correct meaning ops model

#print axioms direct_correct
end PaperCore.Hybrid.Stage
