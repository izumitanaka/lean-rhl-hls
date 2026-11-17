import IRComparison.Circuit.Graph

namespace IRComparison.Circuit

/-- Instructions without a program counter. This is proof structure for laying
out the existing sequential controller, not an additional optimization IR. -/
inductive Action (α : Type := Expr) where
  | wire (slot : Nat) (value : α)
  | assign (reg : Nat) (value : α)
  | store (array : Nat) (index value : α)
  | snapshot (destination source : Nat)
  | erase (array : Nat)
  | clear (queue : Nat)
  | send (queue : Nat) (value : α)
  | receive (queue slot : Nat)
  deriving Repr

def Action.node (next : Nat) : Action α → Node α
  | .wire n e => .wire n e next
  | .assign n e => .assign n e next
  | .store a j e => .store a j e next
  | .snapshot a b => .snapshot a b next
  | .erase a => .erase a next
  | .clear q => .clear q next
  | .send q e => .send q e next
  | .receive q r => .receive q r next

structure Payload where
  data : IRComparison.State
  wires : Nat → Int
  queues : Nat → List Int

def Payload.at (p : Payload) (pc : Nat) : Runtime :=
  ⟨pc,p.data,p.wires,p.queues,false,false⟩
def Runtime.payload (r : Runtime) : Payload := ⟨r.data,r.wires,r.queues⟩

def Action.eval {α : Type} [ExpressionEvaluation α] (cap : Nat → Nat) (action : Action α) (p : Payload) : Option Payload :=
  (execute cap (action.node 0) (p.at 0)).map Runtime.payload

theorem Action.execute_eq {α : Type} [ExpressionEvaluation α] (a : Action α) (p : Payload) (entry next : Nat) :
    execute cap (a.node next) (p.at entry) = (a.eval cap p).map (fun q => q.at next) := by
  cases a <;> simp only [Action.node,Action.eval,execute,Payload.at,Runtime.payload] <;> try rfl
  case wire slot e | assign slot e => cases ExpressionEvaluation.eval e p.data p.wires <;> rfl
  case store a j e =>
    cases ExpressionEvaluation.eval j p.data p.wires with
    | none => rfl
    | some k => cases ExpressionEvaluation.eval e p.data p.wires with
      | none => rfl
      | some v => simp only [bind,Option.bind]; cases p.data.write a k v <;> rfl
  case send q e =>
    cases ExpressionEvaluation.eval e p.data p.wires with
    | none => rfl
    | some v => simp only [bind,Option.bind]; split <;> rfl
  case receive q slot => cases p.queues q <;> rfl

inductive Schedule (α : Type := Expr) where
  | skip
  | step (action : Action α)
  | seq (first second : Schedule α)
  | branch (condition : α) (yes no : Schedule α)
  | loop (condition : α) (body : Schedule α)
  deriving Repr

/-- The loop judgement describes finite execution. Source-side counted-loop
termination supplies such a derivation; this layer assumes no fixed bound. -/
inductive Schedule.Eval {α : Type} [ExpressionEvaluation α] (cap : Nat → Nat) : Schedule α → Payload → Option Payload → Prop where
  | skip : Eval cap .skip p (some p)
  | step : Eval cap (.step a) p (a.eval cap p)
  | seq_error : Eval cap a p none → Eval cap (.seq a b) p none
  | seq : Eval cap a p (some q) → Eval cap b q r → Eval cap (.seq a b) p r
  | branch_error : ExpressionEvaluation.eval e p.data p.wires = none → Eval cap (.branch e a b) p none
  | branch_yes {v : Int} {a : Schedule α} {p : Payload} {r : Option Payload} {e : α} {b : Schedule α} : ExpressionEvaluation.eval e p.data p.wires = some v → v ≠ 0 → Eval cap a p r → Eval cap (.branch e a b) p r
  | branch_no {b : Schedule α} {p : Payload} {r : Option Payload} {e : α} {a : Schedule α} : ExpressionEvaluation.eval e p.data p.wires = some 0 → Eval cap b p r → Eval cap (.branch e a b) p r
  | loop_error : ExpressionEvaluation.eval e p.data p.wires = none → Eval cap (.loop e body) p none
  | loop_stop : ExpressionEvaluation.eval e p.data p.wires = some 0 → Eval cap (.loop e body) p (some p)
  | loop_body_error {v : Int} {body : Schedule α} {p : Payload} {e : α} : ExpressionEvaluation.eval e p.data p.wires = some v → v ≠ 0 → Eval cap body p none → Eval cap (.loop e body) p none
  | loop_next {v : Int} {body : Schedule α} {p q : Payload} {e : α} {r : Option Payload} : ExpressionEvaluation.eval e p.data p.wires = some v → v ≠ 0 → Eval cap body p (some q) →
      Eval cap (.loop e body) q r → Eval cap (.loop e body) p r

/-- Explicit structural layout avoids patching labels after proofs have been
constructed. Loop bodies jump back to the condition node. -/
def Schedule.size : Schedule α → Nat
  | .skip | .step _ => 1
  | .seq a b => a.size + b.size
  | .branch _ a b => 1 + a.size + b.size
  | .loop _ b => 1 + b.size

def Schedule.layout (base next : Nat) : Schedule α → List (Node α)
  | .skip => [.jump next]
  | .step a => [a.node next]
  | .seq a b => a.layout base (base+a.size) ++ b.layout (base+a.size) next
  | .branch e a b => .branch e (base+1) (base+1+a.size) ::
      (a.layout (base+1) next ++ b.layout (base+1+a.size) next)
  | .loop e b => .branch e (base+1) next :: b.layout (base+1) base

theorem Schedule.layout_length (c : Schedule α) : (c.layout base next).length = c.size := by
  induction c generalizing base next <;> simp_all [layout,size] <;> omega

/-- A list of laid-out instructions is embedded at the given address. -/
def Fits (m : Machine α) (base : Nat) (code : List (Node α)) : Prop :=
  ∀ k, k < code.length → m.nodes[base+k]? = code[k]?

theorem Fits.head {m : Machine α} {base : Nat} {n : Node α} {ns : List (Node α)}
    (h : Fits m base (n::ns)) : m.nodes[base]? = some n := by
  simpa using h 0 (by simp)

theorem Fits.tail {m : Machine α} {base : Nat} {n : Node α} {ns : List (Node α)}
    (h : Fits m base (n::ns)) : Fits m (base+1) ns := by
  intro k hk
  simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h (k+1) (by simpa using Nat.succ_lt_succ hk)

theorem Fits.left {m : Machine α} {base : Nat} {a b : List (Node α)}
    (h : Fits m base (a++b)) : Fits m base a := by
  intro k hk
  simpa [List.getElem?_append,show k < a.length from hk] using h k (by simp; omega)

theorem Fits.right {m : Machine α} {base : Nat} {a b : List (Node α)}
    (h : Fits m base (a++b)) : Fits m (base+a.length) b := by
  intro k hk
  have hh := h (a.length+k) (by simp; omega)
  simpa [List.getElem?_append,show ¬ a.length+k < a.length from by omega,Nat.add_assoc] using hh

/-- The semantic outcome ignores unreachable payload contents after failure. -/
def PayloadOutcome (next : Nat) (result : Option Payload) (r : Runtime) : Prop :=
  match result with
  | none => r.done = true ∧ r.error = true
  | some p => r = p.at next

theorem branch_taken {α : Type} [ExpressionEvaluation α] {m : Machine α} {p : Payload} {e : α} {entry yes no : Nat}
    (hn : m.nodes[entry]? = some (.branch e yes no)) (he : ExpressionEvaluation.eval e p.data p.wires = some v) :
    Steps m (p.at entry) (p.at (if v != 0 then yes else no)) := by
  apply Steps.one
  apply tick_node rfl (by exact hn)
  simp [execute,Payload.at,he]

theorem branch_failed {α : Type} [ExpressionEvaluation α] {m : Machine α} {p : Payload} {e : α} {entry yes no : Nat}
    (hn : m.nodes[entry]? = some (.branch e yes no)) (he : ExpressionEvaluation.eval e p.data p.wires = none) :
    ∃ t, Steps m (p.at entry) t ∧ t.done = true ∧ t.error = true := by
  refine ⟨{ p.at entry with done := true,error := true },?_,rfl,rfl⟩
  apply Steps.one
  exact tick_failure rfl (by exact hn) (by simp [execute,Payload.at,he])

/-- General correctness of address allocation and sequential scheduling.
The theorem is proved once for arbitrary expressions, nested branches/loops,
queue actions and execution derivations. -/
theorem Schedule.layout_correct {α : Type} [ExpressionEvaluation α] {m : Machine α} {c : Schedule α} {p : Payload} {result : Option Payload}
    (he : c.Eval m.capacity p result) :
    ∀ base next, Fits m base (c.layout base next) →
      ∃ t, Steps m (p.at base) t ∧ PayloadOutcome next result t := by
  induction he with
  | @skip p =>
    intro base next hf
    refine ⟨p.at next,Steps.one ?_,rfl⟩
    exact tick_node rfl (by exact hf.head) rfl
  | @step a p =>
    intro base next hf
    have hn : m.nodes[base]? = some (a.node next) := hf.head
    cases hr : a.eval m.capacity p with
    | none =>
      refine ⟨{ p.at base with done := true,error := true },Steps.one ?_,by simp [PayloadOutcome,hr]⟩
      exact tick_failure rfl (by exact hn) (by rw [Action.execute_eq,hr]; rfl)
    | some q =>
      refine ⟨q.at next,Steps.one ?_,by simp [PayloadOutcome,hr]⟩
      exact tick_node rfl (by exact hn) (by rw [Action.execute_eq,hr]; rfl)
  | @seq_error a p b ha ih =>
    intro base next hf
    obtain ⟨t,ht,ho⟩ := ih base (base+a.size) hf.left
    exact ⟨t,ht,ho⟩
  | @seq a p q b result ha hb ia ib =>
    intro base next hf
    obtain ⟨t,ht,ho⟩ := ia base (base+a.size) hf.left
    have eq : t = q.at (base+a.size) := ho
    subst t
    have right : Fits m (base+a.size) (b.layout (base+a.size) next) := by
      simpa [Schedule.layout_length] using hf.right
    obtain ⟨u,hu,hou⟩ := ib (base+a.size) next right
    exact ⟨u,ht.trans hu,hou⟩
  | @branch_error e a b p he =>
    intro base next hf
    exact branch_failed hf.head he
  | @branch_yes v a p result e b he hv ha ih =>
    intro base next hf
    obtain ⟨t,ht,ho⟩ := ih (base+1) next hf.tail.left
    have step := branch_taken hf.head he
    simp [hv] at step
    exact ⟨t,step.trans ht,ho⟩
  | @branch_no b p result e a he hb ih =>
    intro base next hf
    have right : Fits m (base+1+a.size) (b.layout (base+1+a.size) next) := by
      simpa [Schedule.layout_length] using hf.tail.right
    obtain ⟨t,ht,ho⟩ := ih (base+1+a.size) next right
    have step := branch_taken hf.head he
    have step' : Steps m (p.at base) (p.at (base+1+a.size)) := by simpa using step
    exact ⟨t,step'.trans ht,ho⟩
  | @loop_error e body p he =>
    intro base next hf
    exact branch_failed hf.head he
  | @loop_stop e body p he =>
    intro base next hf
    refine ⟨p.at next,?_,rfl⟩
    simpa using branch_taken hf.head he
  | @loop_body_error v body p e he hv hb ih =>
    intro base next hf
    obtain ⟨t,ht,ho⟩ := ih (base+1) base hf.tail
    have step := branch_taken hf.head he
    simp [hv] at step
    exact ⟨t,step.trans ht,ho⟩
  | @loop_next v body p q e result he hv hb hl ib il =>
    intro base next hf
    obtain ⟨t,ht,ho⟩ := ib (base+1) base hf.tail
    have eq : t = q.at base := ho
    subst t
    obtain ⟨u,hu,hou⟩ := il base next hf
    have step := branch_taken hf.head he
    simp [hv] at step
    exact ⟨u,step.trans (ht.trans hu),hou⟩

def Schedule.assemble (s : Schedule α) (capacities : Array (Nat × Nat)) : Machine α :=
  ⟨1,(Node.halt :: s.layout 1 0).toArray,capacities⟩

theorem Schedule.assemble_fits (s : Schedule α) : Fits (s.assemble capacities) 1 (s.layout 1 0) := by
  intro k hk
  simp [assemble,Nat.add_comm]

/-- The actual array-valued assembler, including its final halt state. -/
theorem Schedule.assemble_finishes {α : Type} [ExpressionEvaluation α] (s : Schedule α) (p : Payload)
    (he : s.Eval (s.assemble capacities).capacity p result) :
    ∃ cycles, ((s.assemble capacities).run cycles (p.at 1)).result = some (result.map Payload.data) := by
  obtain ⟨t,ht,ho⟩ := s.layout_correct he 1 0 s.assemble_fits
  cases result with
  | none =>
    obtain ⟨n,hn⟩ := ht.finite
    exact ⟨n,by rw [hn]; simp only [PayloadOutcome] at ho; simp [Runtime.result,ho.1,ho.2]⟩
  | some q =>
    have eq : t = q.at 0 := ho
    subst t
    have hh : (s.assemble capacities).tick (q.at 0) = { q.at 0 with done := true } := by
      apply tick_node (instruction := .halt) rfl
      · simp [assemble,Payload.at]
      · rfl
    obtain ⟨n,hn⟩ := (ht.trans (Steps.one hh)).finite
    exact ⟨n,by rw [hn]; rfl⟩

end IRComparison.Circuit
