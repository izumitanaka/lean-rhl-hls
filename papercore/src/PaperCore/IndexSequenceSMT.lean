import PaperCore.IndexSequence
import PaperCore.SMT.SMTConnection

namespace PaperCore.IndexSequence
open PaperCore (SMT)

/-- Equality of finite arithmetic sequences, including the representation
    freedom of empty and singleton sequences. Counts are checked nonnegative.
    This is integer arithmetic only; no SMT sequence theory is required. -/
def equality (first step count otherFirst otherStep otherCount : SMT) : SMT :=
  SMT.conj [SMT.le (.num 0) count, SMT.le (.num 0) otherCount,
    SMT.eq count otherCount,
    SMT.disj [SMT.eq count (.num 0), SMT.eq first otherFirst],
    SMT.disj [SMT.le count (.num 1), SMT.eq step otherStep]]

theorem equality_correct
    (hf : PaperCore.SMTMeaning.eval zero params vars first = .integer f)
    (hs : PaperCore.SMTMeaning.eval zero params vars step = .integer s)
    (hn : PaperCore.SMTMeaning.eval zero params vars count = .integer n)
    (hg : PaperCore.SMTMeaning.eval zero params vars otherFirst = .integer g)
    (ht : PaperCore.SMTMeaning.eval zero params vars otherStep = .integer t)
    (hm : PaperCore.SMTMeaning.eval zero params vars otherCount = .integer m) :
    PaperCore.SMTMeaning.eval zero params vars (equality first step count otherFirst otherStep otherCount) = .boolean true ↔
      0 ≤ n ∧ 0 ≤ m ∧ entries f s n.toNat = entries g t m.toNat := by
  simp only [equality, SMT.conj, SMT.disj, SMT.le, SMT.eq, SMT.op,
    PaperCore.SMTMeaning.eval, List.map_cons, List.map_nil, hf, hs, hn, hg, ht, hm]
  simp [PaperCore.SMTMeaning.operation, PaperCore.SMTMeaning.booleans] 
  rw [eq_entries_iff]
  omega

def candidateQuery (first step : Int) (count : Nat) : SMT :=
  equality (.num first) (.num step) (.num count)
    (.param "first") (.param "step") (.param "count")

/-- Concrete SAT-to-sequence theorem: the response is checked against the
    actual query bytes, and its decoded parameters denote the requested
    sequence. No atom-encoding assumption or UNSAT assumption remains. -/
theorem candidateResponse_sound (first step : Int) (count : Nat)
    (accepted : PaperCore.SMTConnection.acceptResponse (candidateQuery first step count)
      request response = some bindings)
    (solver : PaperCore.SMTConnection.SolverReplySound request response) :
    let value := fun name => (bindings.lookup name).getD 0
    0 ≤ value "count" ∧
      entries first step count = entries (value "first") (value "step") (value "count").toNat := by
  obtain ⟨zero,model⟩ := PaperCore.SMTConnection.acceptResponse_sound accepted solver
  let params := fun name => (bindings.lookup name).getD 0
  have hf : PaperCore.SMTMeaning.eval zero params (fun _ => 0) (.num first) = .integer first := by
    simp [PaperCore.SMTMeaning.eval]
  have hs : PaperCore.SMTMeaning.eval zero params (fun _ => 0) (.num step) = .integer step := by
    simp [PaperCore.SMTMeaning.eval]
  have hn : PaperCore.SMTMeaning.eval zero params (fun _ => 0) (.num count) = .integer count := by
    simp [PaperCore.SMTMeaning.eval]
  have hg : PaperCore.SMTMeaning.eval zero params (fun _ => 0) (.param "first") = .integer (params "first") := by
    simp [PaperCore.SMTMeaning.eval]
  have ht : PaperCore.SMTMeaning.eval zero params (fun _ => 0) (.param "step") = .integer (params "step") := by
    simp [PaperCore.SMTMeaning.eval]
  have hm : PaperCore.SMTMeaning.eval zero params (fun _ => 0) (.param "count") = .integer (params "count") := by
    simp [PaperCore.SMTMeaning.eval]
  have result := (equality_correct hf hs hn hg ht hm).mp model
  simpa using result.2

#print axioms equality_correct
#print axioms candidateResponse_sound
end PaperCore.IndexSequence
