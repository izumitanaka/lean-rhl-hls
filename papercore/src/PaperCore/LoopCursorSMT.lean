import PaperCore.BodyCursorSMT
import PaperCore.CursorObligation

namespace PaperCore.LoopCursorSMT
open AccessAnalysis IndexSequence BodyCursorSMT
open PaperCore (SMT)
open PaperCore.SMTMeaning (eval conj_member)

def sameSequence (left right : Template) : SMT :=
  equality left.first left.step left.count right.first right.step right.count

def frames (arrays : List Array) (before after : Layout) (counter next : SMT) : SMT :=
  SMT.conj (arrays.map (fun a => sameSequence (template (before a) counter) (template (after a) next)))

theorem frames_sound
    (hc : eval zero params vars counter = .integer k)
    (hn : eval zero params vars next = .integer n)
    (model : eval zero params vars (frames arrays before after counter next) = .boolean true)
    (agrees : MatchesOn (fun a => a ∈ arrays) params k before indices) :
    MatchesOn (fun a => a ∈ arrays) params n after indices := by
  intro a tracked
  have part := conj_member _ _ zero params vars model (List.mem_map.mpr ⟨a,tracked,rfl⟩)
  have left := evaluates (name := before a) hc
  have right := evaluates (name := after a) hn
  have same := (equality_correct left.first left.step left.count right.first right.step right.count).mp part
  exact (agrees a tracked).trans (congrArg some same.2.2)

def domain (low high : Int) (counter : SMT) : SMT :=
  SMT.conj [SMT.le (.num low) counter,SMT.le counter (.num high)]

theorem domain_correct (hc : eval zero params vars counter = .integer k) :
    eval zero params vars (domain low high counter) = .boolean true ↔ low ≤ k ∧ k ≤ high := by
  simp [domain,SMT.conj,SMT.le,SMT.op,eval,hc,PaperCore.SMTMeaning.operation,PaperCore.SMTMeaning.booleans]

def nextCounter (counterAfter : Affine) (step : Int) (counter : SMT) : SMT :=
  SMT.add (address counterAfter counter) (.num step)

theorem next_evaluates (hc : eval zero params vars counter = .integer k) :
    eval zero params vars (nextCounter counterAfter step counter) = .integer (counterAfter.eval k + step) := by
  simp [nextCounter,SMT.add,SMT.op,eval,address_evaluates hc,PaperCore.SMTMeaning.operation]

/-- This interval is an invariant candidate, not a source-language bound.
    Preservation is checked using the actual post-body counter expression. -/
def bodyCondition (summary : Summary) (counterAfter : Affine) (arrays : List Array)
    (layout : Layout) (low high stop step : Int) : SMT :=
  let counter : SMT := .var "loop.counter"
  let next := nextCounter counterAfter step counter
  SMT.implies (SMT.conj [domain low high counter,SMT.neg (SMT.eq counter (.num stop))])
    (SMT.conj [BodyCursorSMT.query counter 0 layout summary.accesses,
      frames arrays (finalLayout 0 layout summary.accesses) layout counter next,
      domain low high next])

def query (summary : Summary) (counterAfter : Affine) (arrays : List Array)
    (layout : Layout) (low high stop step : Int) : SMT :=
  let body := bodyCondition summary counterAfter arrays layout low high stop step
  SMT.quantify body.freeVars body

def shape (params : String → Int) (arrays : List Array) (layout : Layout) (low high k : Int)
    (indices : IndexMap) : Prop :=
  low ≤ k ∧ k ≤ high ∧ MatchesOn (fun a => a ∈ arrays) params k layout indices

theorem query_sound
    (tracked : ∀ event ∈ summary.accesses, event.array ∈ arrays)
    (model : eval zero params vars (query summary counterAfter arrays layout low high stop step) = .boolean true) :
    CursorObligation.Obligation summary counterAfter (shape params arrays layout low high) stop step := by
  intro k indices atHead nonzero
  let runtime := fun (_ : String) => k
  have instantiated := PaperCore.SMTMeaning.close_instantiate _ zero params vars runtime model
  have hc : eval zero params runtime (.var "loop.counter") = .integer k := by simp [eval,runtime]
  have inDomain := (domain_correct hc).mpr ⟨atHead.1,atHead.2.1⟩
  have guard : eval zero params runtime (SMT.conj
      [domain low high (.var "loop.counter"),SMT.neg (SMT.eq (.var "loop.counter") (.num stop))]) = .boolean true := by
    simp [SMT.conj,SMT.neg,SMT.eq,SMT.op,eval,inDomain,runtime,nonzero,
      PaperCore.SMTMeaning.operation,PaperCore.SMTMeaning.booleans]
  have body := PaperCore.SMTMeaning.implies_elim _ _ zero params runtime instantiated guard
  have cursor := conj_member _ _ zero params runtime body (by simp :
    BodyCursorSMT.query (.var "loop.counter") 0 layout summary.accesses ∈ _)
  have frame := conj_member _ _ zero params runtime body (by simp :
    frames arrays (finalLayout 0 layout summary.accesses) layout (.var "loop.counter")
      (nextCounter counterAfter step (.var "loop.counter")) ∈ _)
  have range := conj_member _ _ zero params runtime body (by simp :
    domain low high (nextCounter counterAfter step (.var "loop.counter")) ∈ _)
  obtain ⟨afterIndices,consumed,after⟩ := BodyCursorSMT.query_sound summary.accesses hc tracked atHead.2.2 cursor
  have next := next_evaluates (counterAfter := counterAfter) (step := step) hc
  have bounds := (domain_correct next).mp range
  exact ⟨afterIndices,consumed,bounds.1,bounds.2,frames_sound hc next frame after⟩

theorem accepted_obligation
    (tracked : ∀ event ∈ summary.accesses, event.array ∈ arrays)
    (accepted : PaperCore.SMTConnection.acceptResponse
      (query summary counterAfter arrays layout low high stop step) request response = some bindings)
    (solver : PaperCore.SMTConnection.SolverReplySound request response) :
    CursorObligation.Obligation summary counterAfter
      (shape (fun name => (bindings.lookup name).getD 0) arrays layout low high) stop step := by
  obtain ⟨zero,model⟩ := PaperCore.SMTConnection.acceptResponse_sound accepted solver
  exact query_sound tracked model

#print axioms accepted_obligation
end PaperCore.LoopCursorSMT
