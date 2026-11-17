import IRComparison.Circuit.Structured

namespace IRComparison.Circuit

/-- Change only the expression representation; destinations, control edges,
queue identities, and clock count are retained. -/
def Node.mapExpressions (f : α → β) : Node α → Node β
  | .halt => .halt
  | .jump k => .jump k
  | .wire n e k => .wire n (f e) k
  | .assign n e k => .assign n (f e) k
  | .store a j e k => .store a (f j) (f e) k
  | .branch e y n => .branch (f e) y n
  | .snapshot a b k => .snapshot a b k
  | .erase a k => .erase a k
  | .clear q k => .clear q k
  | .send q e k => .send q (f e) k
  | .receive q n k => .receive q n k

def Action.mapExpressions (f : α → β) : Action α → Action β
  | .wire n e => .wire n (f e)
  | .assign n e => .assign n (f e)
  | .store a j e => .store a (f j) (f e)
  | .snapshot a b => .snapshot a b
  | .erase a => .erase a
  | .clear q => .clear q
  | .send q e => .send q (f e)
  | .receive q n => .receive q n

def Schedule.mapExpressions (f : α → β) : Schedule α → Schedule β
  | .skip => .skip
  | .step a => .step (a.mapExpressions f)
  | .seq a b => .seq (a.mapExpressions f) (b.mapExpressions f)
  | .branch e a b => .branch (f e) (a.mapExpressions f) (b.mapExpressions f)
  | .loop e b => .loop (f e) (b.mapExpressions f)

def Machine.mapExpressions (f : α → β) (m : Machine α) : Machine β :=
  ⟨m.entry,m.nodes.map (Node.mapExpressions f),m.capacities⟩

@[simp] theorem Action.map_node (f : α → β) (a : Action α) (next : Nat) :
    (a.mapExpressions f).node next = (a.node next).mapExpressions f := by cases a <;> rfl

@[simp] theorem Schedule.map_size (f : α → β) (s : Schedule α) :
    (s.mapExpressions f).size = s.size := by induction s <;> simp_all [mapExpressions,size]

@[simp] theorem Schedule.map_layout (f : α → β) (s : Schedule α) (base next : Nat) :
    (s.mapExpressions f).layout base next = (s.layout base next).map (Node.mapExpressions f) := by
  induction s generalizing base next <;> simp_all [mapExpressions,layout,Node.mapExpressions]

@[simp] theorem Schedule.map_assemble (f : α → β) (s : Schedule α) (caps : Array (Nat × Nat)) :
    (s.mapExpressions f).assemble caps = (s.assemble caps).mapExpressions f := by
  simp [assemble,Machine.mapExpressions,Node.mapExpressions]

/-- Simulation changes expression representation only. Every finite source
execution, including failure, has the same payload outcome in the target. -/
def Schedule.Simulates [ExpressionEvaluation α] [ExpressionEvaluation β]
    (source : Schedule α) (target : Schedule β) : Prop :=
  ∀ cap p result, source.Eval cap p result → target.Eval cap p result

namespace Schedule.Simulates
variable [ExpressionEvaluation α] [ExpressionEvaluation β]

theorem skip : (Schedule.skip : Schedule α).Simulates (Schedule.skip : Schedule β) := by
  intro cap p result h; cases h; exact .skip

theorem step {a : Action α} {b : Action β}
    (same : ∀ cap p, a.eval cap p = b.eval cap p) :
    (Schedule.step a).Simulates (.step b) := by
  intro cap p result h; cases h
  rw [same]; exact .step

theorem seq {a b : Schedule α} {x y : Schedule β}
    (left : a.Simulates x) (right : b.Simulates y) :
    (Schedule.seq a b).Simulates (.seq x y) := by
  intro cap p result h
  cases h with
  | seq_error h => exact .seq_error (left _ _ _ h)
  | seq ha hb => exact .seq (left _ _ _ ha) (right _ _ _ hb)

theorem branch {e : α} {f : β} {a b : Schedule α} {x y : Schedule β}
    (same : ∀ s w, ExpressionEvaluation.eval e s w = ExpressionEvaluation.eval f s w)
    (yes : a.Simulates x) (no : b.Simulates y) :
    (Schedule.branch e a b).Simulates (.branch f x y) := by
  intro cap p result h
  cases h with
  | branch_error he => exact .branch_error ((same _ _).symm.trans he)
  | branch_yes he ne ha => exact .branch_yes ((same _ _).symm.trans he) ne (yes _ _ _ ha)
  | branch_no he hb => exact .branch_no ((same _ _).symm.trans he) (no _ _ _ hb)

theorem loop {e : α} {f : β} {a : Schedule α} {b : Schedule β}
    (same : ∀ s w, ExpressionEvaluation.eval e s w = ExpressionEvaluation.eval f s w)
    (body : a.Simulates b) : (Schedule.loop e a).Simulates (.loop f b) := by
  intro cap p result h
  generalize equation : Schedule.loop e a = whole at h
  induction h with
  | loop_error he => cases equation; exact .loop_error ((same _ _).symm.trans he)
  | loop_stop he => cases equation; exact .loop_stop ((same _ _).symm.trans he)
  | loop_body_error he ne hb _ =>
    cases equation
    exact .loop_body_error ((same _ _).symm.trans he) ne (body _ _ _ hb)
  | loop_next he ne hb hl _ ih =>
    cases equation
    exact .loop_next ((same _ _).symm.trans he) ne (body _ _ _ hb) (ih rfl)
  | _ => cases equation

end Schedule.Simulates

end IRComparison.Circuit
