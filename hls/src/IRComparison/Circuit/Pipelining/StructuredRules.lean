import IRComparison.Circuit.Pipelining.Allocation
import IRComparison.Circuit.Structured

namespace IRComparison.Circuit.Pipelining

/-- Scheduling metadata on the existing control structure. Expressions,
actions, payloads and failure behavior are unchanged; leaves hold clocks. -/
inductive ClockTree (α : Type := Expr) where
  | block (batches : Batches α)
  | seq (first second : ClockTree α)
  | branch (condition : α) (yes no : ClockTree α)
  | loop (condition : α) (body : ClockTree α)
  deriving Repr

variable {α : Type} [ExpressionEvaluation α] [ExpressionDependencies α]

inductive ClockTree.Eval (cap : Nat → Nat) : ClockTree α → Payload → Option Payload → Prop where
  | block : Eval cap (.block bs) p (runBatches cap bs p)
  | seq_error : Eval cap a p none → Eval cap (.seq a b) p none
  | seq : Eval cap a p (some q) → Eval cap b q r → Eval cap (.seq a b) p r
  | branch_error : ExpressionEvaluation.eval e p.data p.wires = none → Eval cap (.branch e a b) p none
  | branch_yes {v : Int} {a : ClockTree α} {p : Payload} {r : Option Payload} {e : α} {b : ClockTree α} : ExpressionEvaluation.eval e p.data p.wires = some v → v ≠ 0 → Eval cap a p r → Eval cap (.branch e a b) p r
  | branch_no {b : ClockTree α} {p : Payload} {r : Option Payload} {e : α} {a : ClockTree α} : ExpressionEvaluation.eval e p.data p.wires = some 0 → Eval cap b p r → Eval cap (.branch e a b) p r
  | loop_error : ExpressionEvaluation.eval e p.data p.wires = none → Eval cap (.loop e body) p none
  | loop_stop : ExpressionEvaluation.eval e p.data p.wires = some 0 → Eval cap (.loop e body) p (some p)
  | loop_body_error {v : Int} {body : ClockTree α} {p : Payload} {e : α} : ExpressionEvaluation.eval e p.data p.wires = some v → v ≠ 0 → Eval cap body p none → Eval cap (.loop e body) p none
  | loop_next {v : Int} {body : ClockTree α} {p q : Payload} {e : α} {r : Option Payload} : ExpressionEvaluation.eval e p.data p.wires = some v → v ≠ 0 → Eval cap body p (some q) →
      Eval cap (.loop e body) q r → Eval cap (.loop e body) p r

/-- Finite-execution RHL for structured control. The relation is arbitrary;
source termination is a premise, not an assumed bound or a divergence proof. -/
def ControlTranslation (cap : Nat → Nat) (P : Payload → Payload → Prop)
    (source : Circuit.Schedule α) (target : ClockTree α) (Q : Payload → Payload → Prop) : Prop :=
  ∀ s t, P s t → ∀ result, source.Eval cap s result →
    ∃ out, target.Eval cap t out ∧ Option.Rel Q result out

namespace ControlTranslation

variable {s a b : Circuit.Schedule α} {t ta tb : ClockTree α} {e f : α}

theorem consequence (body : ControlTranslation cap P s t Q)
    (pre : ∀ a b, P' a b → P a b) (post : ∀ a b, Q a b → Q' a b) :
    ControlTranslation cap P' s t Q' := by
  intro a b hp r run
  obtain ⟨out,hr,hq⟩ := body a b (pre a b hp) r run
  refine ⟨out,hr,?_⟩
  cases hq with
  | none => exact .none
  | some h => exact .some (post _ _ h)

theorem seq (first : ControlTranslation cap P a ta R)
    (second : ControlTranslation cap R b tb Q) :
    ControlTranslation cap P (.seq a b) (.seq ta tb) Q := by
  intro s t hp r run
  cases run with
  | seq_error ha =>
    obtain ⟨out,ht,rel⟩ := first s t hp none ha
    cases rel
    exact ⟨none,.seq_error ht,.none⟩
  | seq ha hb =>
    obtain ⟨out,ht,rel⟩ := first s t hp _ ha
    cases rel with
    | some hm =>
      obtain ⟨out,hu,hq⟩ := second _ _ hm _ hb
      exact ⟨out,.seq ht hu,hq⟩

theorem branch
    (guards : ∀ s t, P s t → ExpressionEvaluation.eval e s.data s.wires = ExpressionEvaluation.eval f t.data t.wires)
    (yes : ControlTranslation cap
      (fun s t => P s t ∧ ∃ v, ExpressionEvaluation.eval e s.data s.wires = some v ∧ v ≠ 0) a ta Q)
    (no : ControlTranslation cap (fun s t => P s t ∧ ExpressionEvaluation.eval e s.data s.wires = some 0) b tb Q) :
    ControlTranslation cap P (.branch e a b) (.branch f ta tb) Q := by
  intro s t hp r run
  have guards := guards s t hp
  cases run with
  | branch_error he => exact ⟨none,.branch_error (guards ▸ he),.none⟩
  | branch_yes he ne ha =>
    obtain ⟨out,ht,hq⟩ := yes s t ⟨hp,_,he,ne⟩ r ha
    exact ⟨out,.branch_yes (guards ▸ he) ne ht,hq⟩
  | branch_no he hb =>
    obtain ⟨out,ht,hq⟩ := no s t ⟨hp,he⟩ r hb
    exact ⟨out,.branch_no (guards ▸ he) ht,hq⟩

/-- Tr-While with an arbitrary relational invariant and synchronized guards.
It permits different internal body executions, but not speculation across a
branch or overlapped dynamic iterations without a stronger relation/rule. -/
theorem loop
    (guards : ∀ s t, P s t → ExpressionEvaluation.eval e s.data s.wires = ExpressionEvaluation.eval f t.data t.wires)
    (body : ControlTranslation cap
      (fun s t => P s t ∧ ∃ v, ExpressionEvaluation.eval e s.data s.wires = some v ∧ v ≠ 0) a ta P) :
    ControlTranslation cap P (.loop e a) (.loop f ta) P := by
  intro s t hp r run
  generalize eq : Circuit.Schedule.loop e a = c at run
  induction run generalizing t with
  | skip | step | seq_error | seq | branch_error | branch_yes | branch_no => cases eq
  | loop_error he =>
    cases eq
    exact ⟨none,.loop_error ((guards _ _ hp) ▸ he),.none⟩
  | loop_stop he =>
    cases eq
    exact ⟨some t,.loop_stop ((guards _ _ hp) ▸ he),.some hp⟩
  | loop_body_error he ne ha ih =>
    cases eq
    obtain ⟨out,ht,rel⟩ := body _ t ⟨hp,_,he,ne⟩ none ha
    cases rel
    exact ⟨none,.loop_body_error ((guards _ _ hp) ▸ he) ne ht,.none⟩
  | loop_next he ne ha hl ia il =>
    cases eq
    obtain ⟨mid,ht,rel⟩ := body _ t ⟨hp,_,he,ne⟩ _ ha
    cases rel with
    | some hm =>
      obtain ⟨out,hu,hq⟩ := il _ hm rfl
      exact ⟨out,.loop_next ((guards _ _ hp) ▸ he) ne ht hu,hq⟩

theorem of_preserves
    (h : ∀ p r, s.Eval cap p r → t.Eval cap p r) : ControlTranslation cap Eq s t Eq := by
  intro p q hp r run
  subst q
  refine ⟨r,h p r run,?_⟩
  cases r with
  | none => exact .none
  | some v => exact .some rfl

theorem preserves (h : ControlTranslation cap Eq s t Eq) (run : s.Eval cap p r) :
    t.Eval cap p r := by
  obtain ⟨out,ht,rel⟩ := h p p rfl r run
  cases rel with
  | none => exact ht
  | some eq => simpa [eq] using ht

end ControlTranslation
end IRComparison.Circuit.Pipelining
