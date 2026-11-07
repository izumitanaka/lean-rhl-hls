import PaperCore.IndexSequenceSMT
import IRComparison.Core.CommunicationIR

namespace IRComparison.CompactSequence

/-- Counted signed arithmetic sequence. It occupies constant space even for
    large trip counts. Empty/singleton sequences have no forced canonical form. -/
structure Seq where
  first : Int
  step : Int
  count : Nat
  deriving Repr, DecidableEq

def Seq.entries (s : Seq) : List Int := PaperCore.IndexSequence.entries s.first s.step s.count

def equivalent (a b : Seq) : Bool :=
  a.count == b.count && (a.count == 0 || a.first == b.first) && (a.count ≤ 1 || a.step == b.step)

theorem equivalent_correct (a b : Seq) : equivalent a b = true ↔ a.entries = b.entries := by
  simp only [equivalent,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq,Seq.entries]
  simpa only [and_assoc] using (PaperCore.IndexSequence.eq_entries_iff a.first a.step b.first b.step a.count b.count).symm

structure Certified (wanted : Seq) where
  sequence : Seq
  correct : sequence.entries = wanted.entries

def query (wanted : Seq) : PaperCore.SMT :=
  PaperCore.IndexSequence.candidateQuery wanted.first wanted.step wanted.count

/-- General solver-trust boundary: request and response are both checked by
    PaperCore's verified wire parser, not accepted on the word `sat` alone. -/
theorem response_sound (wanted : Seq)
    (accepted : PaperCore.SMTConnection.acceptResponse (query wanted) request response = some bindings)
    (solver : PaperCore.SMTConnection.SolverReplySound request response) :
    let value := fun name => (bindings.lookup name).getD 0
    (Seq.mk (value "first") (value "step") (value "count").toNat).entries = wanted.entries := by
  have h := PaperCore.IndexSequence.candidateResponse_sound wanted.first wanted.step wanted.count accepted solver
  exact h.2.symm

/-- For this arithmetic fragment the model can also be rechecked without an
    oracle assumption. This check is independent of the sequence length. -/
def accept (wanted : Seq) (request response : String) : Option (Certified wanted) := do
  let bindings ← PaperCore.SMTConnection.acceptResponse (query wanted) request response
  let value := fun name => (bindings.lookup name).getD 0
  if value "count" < 0 then none else
  let candidate : Seq := ⟨value "first",value "step",(value "count").toNat⟩
  if h : equivalent candidate wanted = true then return ⟨candidate,(equivalent_correct _ _).mp h⟩ else none

structure Transcript where
  request : String
  response : String
  stderr : String
  deriving Repr

/-- SAT proposes parameters; UNSAT, unknown, timeout and malformed replies do
    not authorize a transformation. No counterexample/UNSAT query is used. -/
def solve (wanted : Seq) (directory : System.FilePath) : IO (Transcript × Option (Certified wanted)) := do
  IO.FS.createDirAll directory
  let request := PaperCore.SMT.script (query wanted)
  let path := directory / "request.smt2"
  IO.FS.writeFile path request
  let result ← IO.Process.output {cmd := "z3",args := #["-T:15",path.toString]}
  IO.FS.writeFile (directory / "response.txt") result.stdout
  IO.FS.writeFile (directory / "stderr.txt") result.stderr
  let transcript := Transcript.mk request result.stdout result.stderr
  return (transcript,if result.exitCode == 0 then accept wanted request result.stdout else none)

example : equivalent ⟨0,1,1000000000⟩ ⟨0,1,1000000000⟩ = true := by decide +kernel
example : equivalent ⟨0,1,0⟩ ⟨99,-7,0⟩ = true := by decide +kernel
example : equivalent ⟨4,1,1⟩ ⟨4,-100,1⟩ = true := by decide +kernel
example : equivalent ⟨0,1,3⟩ ⟨2,-1,3⟩ = false := by decide +kernel

end IRComparison.CompactSequence
