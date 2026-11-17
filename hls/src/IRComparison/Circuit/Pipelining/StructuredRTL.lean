import IRComparison.Circuit.Pipelining.Structured

namespace IRComparison.Circuit.Pipelining

/-- The existing controller nodes with a list of simultaneous actions in a
compute case. No additional expression, memory or FIFO semantics. -/
inductive ClockNode (α : Type := Expr) where
  | batch (actions : List (Action α)) (next : Nat)
  | branch (condition : α) (yes no : Nat)
  | jump (next : Nat)
  | halt
  deriving Repr

variable {α : Type} [ExpressionEvaluation α] [ExpressionDependencies α]

def ClockNode.eval (cap : Nat → Nat) (n : ClockNode α) (r : Circuit.Runtime) : Circuit.Runtime :=
  match n with
  | .batch as next => match clock cap as r.payload with
    | none => {r with done := true,error := true}
    | some p => {withPayload r p with pc := next}
  | .branch e yes no => match ExpressionEvaluation.eval e r.data r.wires with
    | none => {r with done := true,error := true}
    | some v => {r with pc := if v != 0 then yes else no}
  | .jump next => {r with pc := next}
  | .halt => {r with done := true}

def ClockNode.statement : ClockNode α → RTL.Statement α
  | .batch as next => lowerClock next as
  | .branch e yes no => RTL.lowerNode (.branch e yes no)
  | .jump next => RTL.advance next
  | .halt => RTL.halt

theorem ClockNode.statement_correct (n : ClockNode) (hb : InputsBound r.data r.wires wr) :
    n.statement.eval wr cap r r = n.eval cap r := by
  cases n with
  | batch as next => exact lowerClock_bit_correct next as r hb
  | branch e yes no =>
    rw [ClockNode.statement,RTL.lowerNode_correct,bitExecute_correct _ hb]
    cases he : ExpressionEvaluation.eval e r.data r.wires <;> simp [execute,ClockNode.eval,he]
  | jump | halt => rfl

structure ClockGraph (α : Type := Expr) where
  nodes : Array (ClockNode α)
  capacities : Array (Nat × Nat)
  deriving Repr

def ClockGraph.capacity (g : ClockGraph α) := capacityOf g.capacities

def ClockGraph.tick (g : ClockGraph α) (r : Circuit.Runtime) : Circuit.Runtime :=
  if r.done then r else match g.nodes[r.pc]? with
    | none => {r with done := true,error := true}
    | some node => node.eval g.capacity r

def ClockGraph.run (g : ClockGraph α) : Nat → Circuit.Runtime → Circuit.Runtime
  | 0,r => r
  | n+1,r => g.run n (g.tick r)

def ClockGraph.rtl (g : ClockGraph α) : RTL.Program α :=
  ⟨1,g.nodes.map ClockNode.statement,g.capacities⟩

inductive ClockGraph.Steps (g : ClockGraph α) : Circuit.Runtime → Circuit.Runtime → Prop where
  | refl (r) : Steps g r r
  | next : Steps g (g.tick r) t → Steps g r t

variable {g : ClockGraph α}

theorem ClockGraph.Steps.trans (h : Steps g r s) (k : Steps g s t) : Steps g r t := by
  induction h with
  | refl => exact k
  | next _ ih => exact .next (ih k)

theorem ClockGraph.Steps.finite (h : Steps g r t) : ∃ n, g.run n r = t := by
  induction h with
  | refl => exact ⟨0,rfl⟩
  | next _ ih => obtain ⟨n,hn⟩ := ih; exact ⟨n+1,hn⟩

theorem ClockGraph.Steps.one (h : g.tick r = t) : Steps g r t := by
  rw [← h]; exact .next (.refl _)

def ClockFits (g : ClockGraph α) (base : Nat) (ns : List (ClockNode α)) : Prop :=
  ∀ k, k < ns.length → g.nodes[base+k]? = ns[k]?

theorem ClockFits.head (h : ClockFits g base (n::ns)) : g.nodes[base]? = some n := by
  simpa using h 0 (by simp)

theorem ClockFits.tail (h : ClockFits g base (n::ns)) : ClockFits g (base+1) ns := by
  intro k hk
  simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h (k+1) (by simpa using Nat.succ_lt_succ hk)

theorem ClockFits.left (h : ClockFits g base (a++b)) : ClockFits g base a := by
  intro k hk
  simpa [List.getElem?_append,show k < a.length from hk] using h k (by simp; omega)

theorem ClockFits.right (h : ClockFits g base (a++b)) : ClockFits g (base+a.length) b := by
  intro k hk
  simpa [List.getElem?_append,show ¬ a.length+k < a.length from by omega,Nat.add_assoc] using
    h (a.length+k) (by simp; omega)

def clockBlockLayout (base next : Nat) : Batches α → List (ClockNode α)
  | [] => [.jump next]
  | as::rest => .batch as (base+1) :: clockBlockLayout (base+1) next rest

def ClockTree.size : ClockTree α → Nat
  | .block bs => bs.length+1
  | .seq a b => a.size+b.size
  | .branch _ a b => 1+a.size+b.size
  | .loop _ body => 1+body.size

def ClockTree.layout (base next : Nat) : ClockTree α → List (ClockNode α)
  | .block bs => clockBlockLayout base next bs
  | .seq a b => a.layout base (base+a.size) ++ b.layout (base+a.size) next
  | .branch e a b => .branch e (base+1) (base+1+a.size) ::
      (a.layout (base+1) next ++ b.layout (base+1+a.size) next)
  | .loop e body => .branch e (base+1) next :: body.layout (base+1) base

variable {s : Circuit.Schedule α} {strategy : Array (Action α) → Cycles}
variable {g : ClockGraph α} {p : Payload} {e : α} {t : ClockTree α}
  {base next : Nat} {result : Option Payload}

theorem clockBlockLayout_length (bs : Batches α) : (clockBlockLayout base next bs).length = bs.length+1 := by
  induction bs generalizing base <;> simp_all [clockBlockLayout]

theorem ClockTree.layout_length (t : ClockTree α) : (t.layout base next).length = t.size := by
  induction t generalizing base next <;> simp_all [layout,size,clockBlockLayout_length] <;> omega

theorem clockBlock_correct (bs : Batches α) (p : Payload) :
    ∀ base next, ClockFits g base (clockBlockLayout base next bs) →
      ∃ r, g.Steps (p.at base) r ∧ PayloadOutcome next (runBatches g.capacity bs p) r := by
  induction bs generalizing p with
  | nil =>
    intro base next hf
    refine ⟨p.at next,.one ?_,rfl⟩
    simp [ClockGraph.tick,Payload.at,hf.head,ClockNode.eval]
  | cons as rest ih =>
    intro base next hf
    cases he : clock g.capacity as p with
    | none =>
      refine ⟨{p.at base with done := true,error := true},.one ?_,?_⟩
      · simp [ClockGraph.tick,Payload.at,hf.head,ClockNode.eval,Circuit.Runtime.payload,he]
      · simp [runBatches,he,PayloadOutcome]
    | some q =>
      obtain ⟨r,hr,ho⟩ := ih q (base+1) next hf.tail
      have one : g.Steps (p.at base) (q.at (base+1)) := .one (by
        simp [ClockGraph.tick,Payload.at,hf.head,ClockNode.eval,Circuit.Runtime.payload,he,withPayload])
      exact ⟨r,one.trans hr,by simpa [runBatches,he] using ho⟩

theorem clockBranch_taken (hn : g.nodes[base]? = some (.branch e yes no))
    (he : ExpressionEvaluation.eval e p.data p.wires = some v) :
    g.Steps (p.at base) (p.at (if v != 0 then yes else no)) := .one (by
  simp [ClockGraph.tick,Payload.at,hn,ClockNode.eval,he])

theorem clockBranch_failed (hn : g.nodes[base]? = some (.branch e yes no))
    (he : ExpressionEvaluation.eval e p.data p.wires = none) :
    ∃ t, g.Steps (p.at base) t ∧ t.done = true ∧ t.error = true := by
  refine ⟨{p.at base with done := true,error := true},.one ?_,rfl,rfl⟩
  simp [ClockGraph.tick,Payload.at,hn,ClockNode.eval,he]

theorem ClockTree.layout_correct (he : t.Eval g.capacity p result) :
    ∀ base next, ClockFits g base (t.layout base next) →
      ∃ r, g.Steps (p.at base) r ∧ PayloadOutcome next result r := by
  induction he with
  | block => exact clockBlock_correct _ _
  | @seq_error a p b ha ih =>
    intro base next hf
    obtain ⟨r,hr,ho⟩ := ih base (base+a.size) hf.left
    exact ⟨r,hr,ho⟩
  | @seq a p q b result ha hb ia ib =>
    intro base next hf
    obtain ⟨r,hr,ho⟩ := ia base (base+a.size) hf.left
    have eq : r = q.at (base+a.size) := ho
    subst r
    obtain ⟨u,hu,hou⟩ := ib (base+a.size) next (by simpa [layout_length] using hf.right)
    exact ⟨u,hr.trans hu,hou⟩
  | @branch_error e a b p he => intro base next hf; exact clockBranch_failed hf.head he
  | @branch_yes v a p result e b he ne ha ih =>
    intro base next hf
    obtain ⟨r,hr,ho⟩ := ih (base+1) next hf.tail.left
    have step := clockBranch_taken hf.head he
    simp [ne] at step
    exact ⟨r,step.trans hr,ho⟩
  | @branch_no b p result e a he hb ih =>
    intro base next hf
    obtain ⟨r,hr,ho⟩ := ih (base+1+a.size) next (by simpa [layout_length] using hf.tail.right)
    have step := clockBranch_taken hf.head he
    have step' : g.Steps (p.at base) (p.at (base+1+a.size)) := by simpa using step
    exact ⟨r,step'.trans hr,ho⟩
  | @loop_error e body p he => intro base next hf; exact clockBranch_failed hf.head he
  | @loop_stop e body p he =>
    intro base next hf
    exact ⟨p.at next,by simpa using clockBranch_taken hf.head he,rfl⟩
  | @loop_body_error v body p e he ne hb ih =>
    intro base next hf
    obtain ⟨r,hr,ho⟩ := ih (base+1) base hf.tail
    have step := clockBranch_taken hf.head he
    simp [ne] at step
    exact ⟨r,step.trans hr,ho⟩
  | @loop_next v body p q e result he ne hb hl ib il =>
    intro base next hf
    obtain ⟨r,hr,ho⟩ := ib (base+1) base hf.tail
    have eq : r = q.at base := ho
    subst r
    obtain ⟨u,hu,hou⟩ := il base next hf
    have step := clockBranch_taken hf.head he
    simp [ne] at step
    exact ⟨u,step.trans (hr.trans hu),hou⟩

def ClockTree.assemble (t : ClockTree α) (capacities : Array (Nat × Nat)) : ClockGraph α :=
  ⟨(.halt :: t.layout 1 0).toArray,capacities⟩

theorem ClockTree.assemble_payload_finishes (he : t.Eval (capacityOf capacities) p (some q)) :
    ∃ n, (t.assemble capacities).run n (p.at 1) = {q.at 0 with done := true} := by
  have fit : ClockFits (t.assemble capacities) 1 (t.layout 1 0) := by
    intro k hk; simp [assemble,Nat.add_comm]
  obtain ⟨r,hr,ho⟩ := layout_correct (g := t.assemble capacities) he 1 0 fit
  have eq : r = q.at 0 := ho
  subst r
  have hh : (t.assemble capacities).tick (q.at 0) = {q.at 0 with done := true} := by
    simp [assemble,ClockGraph.tick,Payload.at,ClockNode.eval]
  exact (hr.trans (.one hh)).finite

theorem ClockTree.assemble_finishes (he : t.Eval (capacityOf capacities) p result) :
    ∃ n, ((t.assemble capacities).run n (p.at 1)).result = some (result.map Payload.data) := by
  have fit : ClockFits (t.assemble capacities) 1 (t.layout 1 0) := by
    intro k hk; simp [assemble,Nat.add_comm]
  obtain ⟨r,hr,ho⟩ := layout_correct (g := t.assemble capacities) he 1 0 fit
  cases result with
  | none =>
    obtain ⟨n,hn⟩ := hr.finite
    exact ⟨n,by rw [hn]; simp only [PayloadOutcome] at ho; simp [Circuit.Runtime.result,ho.1,ho.2]⟩
  | some q =>
    obtain ⟨n,hn⟩ := assemble_payload_finishes he
    exact ⟨n,by rw [hn]; rfl⟩

theorem scheduleStructure_finishes (he : s.Eval (capacityOf capacities) p result) :
    ∃ n, (((scheduleStructure strategy s).assemble capacities).run n (p.at 1)).result =
      some (result.map Payload.data) :=
  ClockTree.assemble_finishes (scheduleStructure_correct he strategy)

end IRComparison.Circuit.Pipelining
