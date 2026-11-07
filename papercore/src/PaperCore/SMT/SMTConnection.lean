import PaperCore.SMT.SMTRequest
namespace PaperCore.SMTConnection
open SMTMeaning

/-- Exactly the external trust assumption: the solver's reply is a model of the
    actual, well-formed SMT-LIB request. No VC or transformation soundness is assumed.
    Zero-division interpretations are existential, as required by SMT-LIB. -/
def SolverReplySound (request response : String) : Prop :=
  ∀ count term values, SMTRequest.Syntax request count term →
    SMTReply.ResponseSyntax (SMTReply.lex response) values → values.length=count →
    ∃ zero : ZeroDivision,
      evalIndexed zero (fun i => (values[i]?).getD 0) (fun _ => 0) term = .boolean true

/-- A parser may propose values, but both directions of the actual transcript are checked. -/
def accept (formula : SMT) (request response : String) (proposal : List Int) :
    Option (List (String × Int)) :=
  if SMTRequest.check formula request then SMTReply.accept formula.params response proposal else none

/-- End-to-end wire boundary: accepted bindings satisfy the original named VC,
    assuming only correctness of the solver's reply for these actual request bytes. -/
theorem accept_sound {formula : SMT} {request response : String} {proposal : List Int}
    {bindings : List (String × Int)}
    (h : accept formula request response proposal = some bindings)
    (solver : SolverReplySound request response) :
    ∃ zero : ZeroDivision,
      eval zero (fun x => (bindings.lookup x).getD 0) (fun _ => 0) formula = .boolean true := by
  unfold accept at h
  split at h
  next hc =>
    have hs := SMTRequest.check_sound hc
    obtain ⟨hr,hd⟩ := SMTReply.accept_sound h
    obtain ⟨_,hl,_⟩ := Model.decode_shape hd
    obtain ⟨zero,hv⟩ := solver formula.params.length (encode formula.params formula) proposal hs hr hl.symm
    refine ⟨zero,?_⟩
    rw [Model.decode_assignment hd]
    exact (encode_correct formula formula.params zero (fun i => (proposal[i]?).getD 0) (fun _ => 0)) ▸ hv
  next => contradiction

/-- The oracle is parameterized, not supplied by an axiom asserting arbitrary VCs. -/
structure Oracle where
  reply : String → String
  sound : ∀ request, SolverReplySound request (reply request)

def choose (oracle : Oracle) (formula : SMT) (propose : String → List Int) : Option (List (String × Int)) :=
  let request := SMT.script formula
  let response := oracle.reply request
  accept formula request response (propose response)

theorem choose_sound (oracle : Oracle) (formula : SMT) (propose : String → List Int)
    (bindings : List (String × Int)) (h : choose oracle formula propose = some bindings) :
    ∃ zero : ZeroDivision,
      eval zero (fun x => (bindings.lookup x).getD 0) (fun _ => 0) formula = .boolean true :=
  accept_sound h (oracle.sound (SMT.script formula))

#print axioms accept_sound
#print axioms choose_sound

def acceptResponse (formula : SMT) (request response : String) : Option (List (String × Int)) := do
  let proposal ← SMTReply.propose response
  accept formula request response proposal

theorem acceptResponse_sound {formula : SMT} {request response : String}
    {bindings : List (String × Int)}
    (h : acceptResponse formula request response = some bindings)
    (solver : SolverReplySound request response) :
    ∃ zero : ZeroDivision,
      eval zero (fun x => (bindings.lookup x).getD 0) (fun _ => 0) formula = .boolean true := by
  unfold acceptResponse at h
  cases hp : SMTReply.propose response with
  | none => simp [hp] at h
  | some proposal =>
    simp only [hp] at h
    exact accept_sound h solver

#print axioms acceptResponse_sound
end PaperCore.SMTConnection
