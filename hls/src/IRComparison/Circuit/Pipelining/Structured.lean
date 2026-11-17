import IRComparison.Circuit.Pipelining.StructuredRules
import IRComparison.Circuit.Pipelining.Optimized

namespace IRComparison.Circuit.Pipelining

variable {α : Type} [ExpressionEvaluation α] [ExpressionDependencies α]
variable {s : Circuit.Schedule α} {strategy : Array (Action α) → Cycles}

def blockSchedule (strategy : Array (Action α) → Cycles) (actions : List (Action α)) : ClockTree α :=
  .block (batches actions.toArray (compile actions.toArray (strategy actions.toArray)).cycles)

def scheduleStructure (strategy : Array (Action α) → Cycles) : Circuit.Schedule α → ClockTree α
  | .skip => blockSchedule strategy []
  | .step a => blockSchedule strategy [a]
  | .seq a b => match flatten (.seq a b) with
      | some actions => blockSchedule strategy actions
      | none => .seq (scheduleStructure strategy a) (scheduleStructure strategy b)
  | .branch e a b => .branch e (scheduleStructure strategy a) (scheduleStructure strategy b)
  | .loop e body => .loop e (scheduleStructure strategy body)

theorem blockSchedule_correct (actions : List (Action α)) (p : Payload) :
    (blockSchedule strategy actions).Eval cap p (evalList (Action.eval cap) actions p) := by
  have h := ClockTree.Eval.block (cap := cap) (p := p)
    (bs := batches actions.toArray (compile actions.toArray (strategy actions.toArray)).cycles)
  simpa only [blockSchedule,runBatches_eq,compile_correct,sourceEval_eq,List.toList_toArray] using h

/-- The compiler is composed from the basic relational rules. Scheduling
strategy only supplies block candidates; it does not supply new axioms. -/
theorem scheduleStructure_rule (s : Circuit.Schedule α) (strategy : Array (Action α) → Cycles) :
    ControlTranslation cap Eq s (scheduleStructure strategy s) Eq := by
  induction s with
  | skip =>
    apply ControlTranslation.of_preserves
    intro p r run
    cases run
    exact blockSchedule_correct [] p
  | step a =>
    apply ControlTranslation.of_preserves
    intro p r run
    cases run
    simpa [evalList] using (blockSchedule_correct [a] p (strategy := strategy) (cap := cap))
  | seq a b ia ib =>
    cases hf : flatten (.seq a b) with
    | none => simpa [scheduleStructure,hf] using ControlTranslation.seq ia ib
    | some actions =>
      apply ControlTranslation.of_preserves
      intro p r run
      have eq := flatten_correct run hf
      simpa [scheduleStructure,hf,eq] using (blockSchedule_correct actions p (strategy := strategy) (cap := cap))
  | branch e a b ia ib =>
    apply ControlTranslation.branch (fun _ _ h => h ▸ rfl)
    · exact ControlTranslation.consequence ia (fun _ _ h => h.1) (fun _ _ h => h)
    · exact ControlTranslation.consequence ib (fun _ _ h => h.1) (fun _ _ h => h)
  | loop e body ih =>
    apply ControlTranslation.loop (fun _ _ h => h ▸ rfl)
    exact ControlTranslation.consequence ih (fun _ _ h => h.1) (fun _ _ h => h)

/-- Arbitrary nested branches/loops and failure are covered. This follows
from the relational rule derivation, not a second independent proof. -/
theorem scheduleStructure_correct (h : s.Eval cap p result) (strategy : Array (Action α) → Cycles) :
    (scheduleStructure strategy s).Eval cap p result :=
  (scheduleStructure_rule s strategy).preserves h

end IRComparison.Circuit.Pipelining
