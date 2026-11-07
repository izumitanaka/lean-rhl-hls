import PaperCore.BodyCursorSMT
import PaperCore.SMT.SMTConnection

namespace PaperCore.QueueStepSMT
open AccessAnalysis IndexSequence

/-- Shared wire boundary for an individual queue transition. No source AST,
Lean.Expr or source-state representation is part of this interface. -/
def concrete (v : Values) : Template := ⟨.num v.first,.num v.step,.num v.count⟩
def afterTemplate : Template := ⟨.param "first",.param "step",.param "count"⟩
def decode (values : List (String × Int)) : Values :=
  ⟨(values.lookup "first").getD 0,(values.lookup "step").getD 0,(values.lookup "count").getD 0⟩

def query (direction : Direction) (index : Affine) (counter : Int) (before : Values) : SMT :=
  let address := BodyCursorSMT.address index (.num counter)
  match direction with
  | .read => popConstraint (concrete before) afterTemplate address
  | .write => safePushConstraint (concrete before) afterTemplate address

def accept (direction : Direction) (index : Affine) (counter : Int) (before : Values)
    (request response : String) : Option Values := do
  return decode (← SMTConnection.acceptResponse (query direction index counter before) request response)

def Transition (direction : Direction) (index : Int) (before after : Values) : Prop :=
  match direction with
  | .read => 0 < before.count ∧ 0 ≤ after.count ∧ before.sequence = index :: after.sequence
  | .write => 0 ≤ before.count ∧ 0 ≤ after.count ∧
      before.sequence ++ [index] = after.sequence ∧ index ∉ before.sequence

/-- Success refers to the actual query and reply bytes, for either direction.
The solver contract is the only external semantic assumption. -/
theorem accept_sound (direction : Direction) (index : Affine) (counter : Int) (before : Values)
    (accepted : accept direction index counter before request response = some after)
    (solver : SMTConnection.SolverReplySound request response) :
    Transition direction (index.eval counter) before after := by
  unfold accept at accepted
  cases checked : SMTConnection.acceptResponse (query direction index counter before) request response with
  | none => simp [checked] at accepted
  | some values =>
    simp [checked] at accepted
    subst after
    obtain ⟨zero,model⟩ := SMTConnection.acceptResponse_sound checked solver
    have hb : (concrete before).Evaluates before zero (fun name => (values.lookup name).getD 0) (fun _ => 0) := by
      constructor <;> simp [concrete,SMTMeaning.eval]
    have ha : afterTemplate.Evaluates (decode values) zero (fun name => (values.lookup name).getD 0) (fun _ => 0) := by
      constructor <;> simp [afterTemplate,decode,SMTMeaning.eval]
    have hx := BodyCursorSMT.address_evaluates (index := index)
      (zero := zero) (params := fun name => (values.lookup name).getD 0) (vars := fun _ => 0)
      (k := counter) (counter := SMT.num counter) (by simp [SMTMeaning.eval])
    cases direction with
    | read => exact popConstraint_sound hb ha hx model
    | write => exact safePushConstraint_sound hb ha hx model

#print axioms accept_sound
end PaperCore.QueueStepSMT
