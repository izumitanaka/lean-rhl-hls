import IRComparison.Circuit.Pipelining.Integration
import IRComparison.Circuit.RTL.ExpressionMapping

namespace IRComparison.Circuit.Pipelining

section Generic
variable {α : Type} [ExpressionEvaluation α] [ExpressionDependencies α]

/-- Guards and writes use the existing RTL statement language. Every RHS is
read before the edge; a failed bundle raises error without committing writes. -/
def ready : Action α → RTL.Test α
  | .wire _ e | .assign _ e => .valid e
  | .store a j e => .and (.address a j) (.valid e)
  | .send q e => .and (.valid e) (.room q)
  | .receive q _ => .nonempty q
  | .snapshot .. | .erase .. | .clear .. => .valid ExpressionEvaluation.zero

def writes : Action α → RTL.Statement α
  | .wire k e => .assign (.wire k) (.value e)
  | .assign k e => .assign (.data k) (.value e)
  | .store a j e => .memory a (.set a j e)
  | .snapshot a b => .memory a (.copy b)
  | .erase a => .memory a .empty
  | .clear q => .queue q .empty
  | .send q e => .queue q (.append q e)
  | .receive q k => .seq (.assign (.wire k) (.queueHead q)) (.queue q (.tail q))

def oldRead (e : α) (r : Circuit.Runtime) : Option Int := ExpressionEvaluation.eval e r.data r.wires

def withPayload (r : Circuit.Runtime) (p : Payload) : Circuit.Runtime :=
  { r with data := p.data, wires := p.wires, queues := p.queues }

theorem ready_correct (a : Action α) (old : Circuit.Runtime) :
    (ready a).evalWith oldRead cap old = (prepare cap a old.payload).isSome := by
  cases a with
  | wire k e | assign k e =>
    cases he : ExpressionEvaluation.eval e old.data old.wires <;>
      simp [ready,RTL.Test.evalWith,oldRead,prepare,Circuit.Runtime.payload,he]
  | store a j e =>
    cases hj : ExpressionEvaluation.eval j old.data old.wires <;> cases he : ExpressionEvaluation.eval e old.data old.wires <;>
      simp [ready,RTL.Test.evalWith,oldRead,prepare,Circuit.Runtime.payload,hj,he]
    split <;> simp_all
  | snapshot | erase | clear => simp [ready,RTL.Test.evalWith,oldRead,prepare]
  | send q e =>
    cases he : ExpressionEvaluation.eval e old.data old.wires <;>
      simp [ready,RTL.Test.evalWith,oldRead,prepare,Circuit.Runtime.payload,he]
    split <;> simp_all
  | receive q k => cases hq : old.queues q <;> simp [ready,RTL.Test.evalWith,prepare,Circuit.Runtime.payload,hq]

theorem writes_correct (a : Action α) (old pending : Circuit.Runtime)
    (h : prepare cap a old.payload = some us) :
    (writes a).evalWith oldRead cap old pending = withPayload pending (commit us pending.payload) := by
  cases a with
  | wire k e | assign k e =>
    cases he : ExpressionEvaluation.eval e old.data old.wires <;> simp [prepare,Circuit.Runtime.payload,he] at h
    subst us
    simp [writes,RTL.Statement.evalWith,RTL.Scalar.evalWith,RTL.Register.write,oldRead,he,
      withPayload,commit,put,Circuit.Runtime.payload,Circuit.Runtime.setWire]
  | store a j e =>
    cases hj : ExpressionEvaluation.eval j old.data old.wires <;> cases he : ExpressionEvaluation.eval e old.data old.wires <;>
      simp [prepare,Circuit.Runtime.payload,hj,he] at h
    obtain ⟨bounds,h⟩ := h; subst us
    simp [writes,RTL.Statement.evalWith,RTL.MemoryRhs.evalWith,oldRead,hj,he,
      withPayload,commit,put,Circuit.Runtime.payload,Circuit.Runtime.setArray,Array.set!,Array.setIfInBounds,bounds.2]
  | snapshot a b | erase a | clear q =>
    simp [prepare] at h; subst us; rfl
  | send q e =>
    cases he : ExpressionEvaluation.eval e old.data old.wires <;> simp [prepare,Circuit.Runtime.payload,he] at h
    obtain ⟨_,h⟩ := h; subst us
    simp [writes,RTL.Statement.evalWith,RTL.QueueRhs.evalWith,oldRead,he,
      withPayload,commit,put,Circuit.Runtime.payload,Circuit.Runtime.setQueue]
  | receive q k =>
    cases hq : old.queues q <;> simp [prepare,Circuit.Runtime.payload,hq] at h
    subst us
    simp [writes,RTL.Statement.evalWith,RTL.Scalar.evalWith,RTL.QueueRhs.evalWith,
      RTL.Register.write,hq,withPayload,commit,put,Circuit.Runtime.payload,Circuit.Runtime.setQueue,Circuit.Runtime.setWire]

def allReady : List (Action α) → RTL.Test α
  | [] => .valid ExpressionEvaluation.zero
  | a :: as => .and (ready a) (allReady as)

def allWrites : List (Action α) → RTL.Statement α
  | [] => .skip
  | a :: as => .seq (writes a) (allWrites as)

def allPrepared (cap : Nat → Nat) (old : Payload) : List (Action α) → Option (List Update)
  | [] => some []
  | a :: as => do return (← prepare cap a old) ++ (← allPrepared cap old as)

theorem clockFrom_prepared (as : List (Action α)) (old pending : Payload) :
    clockFrom cap old as pending = (allPrepared cap old as).map (fun us => commit us pending) := by
  induction as generalizing pending with
  | nil => rfl
  | cons a as ih =>
    simp only [clockFrom,allPrepared]
    cases ha : prepare cap a old <;> cases hs : allPrepared cap old as <;> simp [ih,hs,commit_append]

theorem allReady_correct (as : List (Action α)) (old : Circuit.Runtime) :
    (allReady as).evalWith oldRead cap old = (allPrepared cap old.payload as).isSome := by
  induction as with
  | nil => simp [allReady,RTL.Test.evalWith,oldRead,allPrepared]
  | cons a as ih =>
    simp only [allReady,RTL.Test.evalWith,ready_correct,ih,allPrepared]
    cases prepare cap a old.payload <;> cases allPrepared cap old.payload as <;> rfl

theorem allWrites_correct (as : List (Action α)) (old pending : Circuit.Runtime)
    (h : allPrepared cap old.payload as = some us) :
    (allWrites as).evalWith oldRead cap old pending = withPayload pending (commit us pending.payload) := by
  induction as generalizing pending us with
  | nil => simp [allPrepared] at h; subst us; cases pending; rfl
  | cons a as ih =>
    cases ha : prepare cap a old.payload <;> cases hs : allPrepared cap old.payload as <;>
      simp [allPrepared,ha,hs] at h
    subst us
    simp only [allWrites,RTL.Statement.evalWith,writes_correct a old pending ha,ih _ hs,commit_append]
    rfl

def lowerClock (next : Nat) (as : List (Action α)) : RTL.Statement α :=
  .branch (allReady as) (.seq (allWrites as) (RTL.advance next)) RTL.fault

theorem lowerClock_correct (next : Nat) (as : List (Action α)) (old : Circuit.Runtime) :
    (lowerClock next as).evalWith oldRead cap old old =
      match clock cap as old.payload with
      | none => {old with done := true,error := true}
      | some p => {withPayload old p with pc := next} := by
  simp only [lowerClock,RTL.Statement.evalWith,allReady_correct,clock,clockFrom_prepared]
  cases hp : allPrepared cap old.payload as with
  | none => rfl
  | some us =>
    simp only [Option.isSome_some,ite_true,allWrites_correct as old old hp,
      RTL.advance,RTL.Statement.evalWith,RTL.Register.write,RTL.Scalar.evalWith,Option.map_some]
    rfl

end Generic

/-- Existing finite-width RTL semantics agrees whenever the already defined
operand-width invariant holds. No replacement arithmetic is introduced. -/
theorem statement_bound (s : RTL.Statement) (h : InputsBound old.data old.wires wr) :
    s.eval wr cap old pending = s.evalWith oldRead cap old pending := by
  have expr (e : Expr) : e.bitEval wr old.data old.wires = oldRead e old := Expr.bitEval_correct e h
  have scalar (v : RTL.Scalar) : v.eval wr old = v.evalWith oldRead old := by
    cases v <;> simp [RTL.Scalar.eval,RTL.Scalar.evalWith,expr]
  have test (v : RTL.Test) : v.eval wr cap old = v.evalWith oldRead cap old := by
    induction v <;> simp_all [RTL.Test.eval,RTL.Test.evalWith]
    rfl
  have mem (v : RTL.MemoryRhs) : v.eval wr old = v.evalWith oldRead old := by
    cases v <;> simp [RTL.MemoryRhs.eval,RTL.MemoryRhs.evalWith,expr]
  have queue (v : RTL.QueueRhs) : v.eval wr old = v.evalWith oldRead old := by
    cases v <;> simp [RTL.QueueRhs.eval,RTL.QueueRhs.evalWith,expr]
  induction s generalizing pending with
  | skip => rfl
  | assign => simp [RTL.Statement.eval,RTL.Statement.evalWith,scalar]
  | memory => simp [RTL.Statement.eval,RTL.Statement.evalWith,mem]
  | queue => simp [RTL.Statement.eval,RTL.Statement.evalWith,queue]
  | seq a b ia ib => simp [RTL.Statement.eval,RTL.Statement.evalWith,ia,ib]
  | branch c a b ia ib => simp [RTL.Statement.eval,RTL.Statement.evalWith,test,ia,ib]

theorem lowerClock_bit_correct (next : Nat) (as : List Action) (old : Circuit.Runtime)
    (h : InputsBound old.data old.wires wr) :
    (lowerClock next as).eval wr cap old old =
      match clock cap as old.payload with
      | none => {old with done := true,error := true}
      | some p => {withPayload old p with pc := next} := by
  rw [statement_bound _ h,lowerClock_correct]

end IRComparison.Circuit.Pipelining
