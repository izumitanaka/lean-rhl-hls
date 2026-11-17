import IRComparison.Circuit.Structured
import IRComparison.Circuit.Pipelining.Reorder

/-! Scheduling metadata for the EXISTING Circuit.Action / Circuit.Expr.
Arrays and queues are conservatively treated as whole resources. This does
not change their semantics or restrict the source language. -/
namespace IRComparison.Circuit.Pipelining

inductive Cell where
  | reg (n : Nat) | wire (n : Nat) | array (n : Nat) | queue (n : Nat)
  deriving DecidableEq, Repr

inductive Content where
  | scalar (v : Int) | array (v : Array Int) | queue (v : List Int)
  deriving DecidableEq, Repr

def get (p : Payload) : Cell → Content
  | .reg n => .scalar (p.data.regs n)
  | .wire n => .scalar (p.wires n)
  | .array n => .array (p.data.arrays n)
  | .queue n => .queue (p.queues n)

def put (p : Payload) : Cell → Content → Payload
  | .reg n, .scalar v => { p with data := p.data.set n v }
  | .wire n, .scalar v => { p with wires := fun k => if k = n then v else p.wires k }
  | .array n, .array v => { p with data := { p.data with arrays := fun k => if k = n then v else p.data.arrays k } }
  | .queue n, .queue v => { p with queues := fun k => if k = n then v else p.queues k }
  | _, _ => p

theorem get_put_other (p : Payload) (a b : Cell) (v : Content) (h : a ≠ b) :
    get (put p a v) b = get p b := by
  cases a <;> cases b <;> cases v <;> simp_all [get,put,IRComparison.State.set]
  all_goals intro he; exact False.elim (h he.symm)

theorem put_commute (p : Payload) (a b : Cell) (u v : Content) (h : a ≠ b) :
    put (put p a u) b v = put (put p b v) a u := by
  cases a <;> cases b <;> cases u <;> cases v <;> simp_all [put,IRComparison.State.set]
  all_goals congr 1 <;> (try congr 1) <;> funext k <;> split <;> split <;> simp_all

def Agrees (xs : List Cell) (p q : Payload) : Prop := ∀ c ∈ xs, get p c = get q c

theorem agrees_append (h : Agrees (xs ++ ys) p q) : Agrees xs p q ∧ Agrees ys p q := by
  exact ⟨fun c hc => h c (List.mem_append_left _ hc), fun c hc => h c (List.mem_append_right _ hc)⟩

def reads : Expr → List Cell
  | .fail | .lit _ => []
  | .wire n => [.wire n]
  | .reg n => [.reg n]
  | .memory a j => .array a :: reads j
  | .bin _ a b | .seq a b => reads a ++ reads b
  | .wrap32 a => reads a
  | .natIndex a => reads a
  | .select c a b => reads c ++ reads a ++ reads b

theorem expr_agrees (e : Expr) (p q : Payload) (h : Agrees (reads e) p q) :
    e.eval p.data p.wires = e.eval q.data q.wires := by
  induction e with
  | fail | lit => rfl
  | wire n => have hh := h (.wire n) (by simp [reads]); simpa [get,Expr.eval] using hh
  | reg n => have hh := h (.reg n) (by simp [reads]); simpa [get,Expr.eval] using hh
  | memory a j ih =>
    have ha : p.data.arrays a = q.data.arrays a := by
      have hh := h (.array a) (by simp [reads]); simpa [get] using hh
    have hj := ih (fun c hc => h c (by simp [reads,hc]))
    simp [Expr.eval,hj,ha]
  | bin op a b ia ib | seq a b ia ib =>
    have hs := agrees_append h
    simp [Expr.eval,ia hs.1,ib hs.2]
  | natIndex a ih | wrap32 a ih => simp [Expr.eval,ih h]
  | select c a b ic ia ib =>
    have hs := agrees_append h
    have hs' := agrees_append hs.1
    simp [Expr.eval,ic hs'.1,ia hs'.2,ib hs.2]

/-- Scheduling depends on sound resource footprints, not expression trees. -/
class ExpressionDependencies (α : Type) [ExpressionEvaluation α] where
  reads : α → List Cell
  agrees : ∀ e p q, Agrees (reads e) p q →
    ExpressionEvaluation.eval e p.data p.wires = ExpressionEvaluation.eval e q.data q.wires

@[default_instance] instance : ExpressionDependencies Expr where
  reads := reads
  agrees := expr_agrees

@[simp] theorem expressionDependencies_original (e : Expr) :
    ExpressionDependencies.reads e = reads e := rfl

variable {α : Type} [ExpressionEvaluation α] [ExpressionDependencies α]

def actionReads : Action α → List Cell
  | .wire _ e | .assign _ e => ExpressionDependencies.reads e
  | .store a j e => .array a :: (ExpressionDependencies.reads j ++ ExpressionDependencies.reads e)
  | .snapshot _ b => [.array b]
  | .erase _ | .clear _ => []
  | .send q e => .queue q :: ExpressionDependencies.reads e
  | .receive q _ => [.queue q]

def actionWrites : Action α → List Cell
  | .wire n _ => [.wire n]
  | .assign n _ => [.reg n]
  | .store a _ _ | .snapshot a _ | .erase a => [.array a]
  | .send q _ | .clear q => [.queue q]
  | .receive q n => [.queue q, .wire n]

abbrev Update := Cell × Content

/-- Evaluate all operands against the old clock state. Only commit writes
later. In particular, failed ExpressionDependencies.reads, bounded queues, and bounds checks remain. -/
def prepare (cap : Nat → Nat) (a : Action α) (p : Payload) : Option (List Update) :=
  match a with
  | .wire n e => return [(.wire n,.scalar (← ExpressionEvaluation.eval e p.data p.wires))]
  | .assign n e => return [(.reg n,.scalar (← ExpressionEvaluation.eval e p.data p.wires))]
  | .store a j e => do
      let k ← ExpressionEvaluation.eval j p.data p.wires
      let v ← ExpressionEvaluation.eval e p.data p.wires
      if h : 0 ≤ k ∧ k.toNat < (p.data.arrays a).size then
        return [(.array a,.array ((p.data.arrays a).set k.toNat v h.2))]
      else none
  | .snapshot a b => some [(.array a,.array (p.data.arrays b))]
  | .erase a => some [(.array a,.array #[])]
  | .clear q => some [(.queue q,.queue [])]
  | .send q e => do
      let v ← ExpressionEvaluation.eval e p.data p.wires
      if (p.queues q).length < cap q then
        return [(.queue q,.queue (p.queues q ++ [v]))]
      else none
  | .receive q n => match p.queues q with
      | [] => none
      | v :: vs => some [(.queue q,.queue vs),(.wire n,.scalar v)]

def commit (us : List Update) (p : Payload) : Payload :=
  us.foldl (fun s u => put s u.1 u.2) p

theorem commit_append (us vs : List Update) (p : Payload) :
    commit (us ++ vs) p = commit vs (commit us p) := by simp [commit,List.foldl_append]

theorem prepare_correct (cap : Nat → Nat) (a : Action α) (p : Payload) :
    (prepare cap a p).map (fun us => commit us p) = a.eval cap p := by
  cases a with
  | wire n e | assign n e =>
    cases he : ExpressionEvaluation.eval e p.data p.wires <;>
      simp [prepare,Action.eval,Action.node,execute,Payload.at,he,Runtime.payload,
        commit,put,Runtime.setWire,IRComparison.State.set]
  | store a j e =>
    cases hj : ExpressionEvaluation.eval j p.data p.wires with
    | none => simp [prepare,Action.eval,Action.node,execute,Payload.at,hj]
    | some k =>
      cases he : ExpressionEvaluation.eval e p.data p.wires with
      | none => simp [prepare,Action.eval,Action.node,execute,Payload.at,hj,he]
      | some v =>
        by_cases hn : k < 0
        · have hnn : ¬ 0 ≤ k := by omega
          simp [prepare,Action.eval,Action.node,execute,Payload.at,hj,he,
            IRComparison.State.write,hn,hnn]
        · have hnn : 0 ≤ k := by omega
          by_cases hb : k.toNat < (p.data.arrays a).size
          · simp [prepare,Action.eval,Action.node,execute,Payload.at,hj,he,
              IRComparison.State.write,hn,hnn,hb,commit,put,Runtime.payload]
          · simp [prepare,Action.eval,Action.node,execute,Payload.at,hj,he,
              IRComparison.State.write,hn,hnn,hb]
  | snapshot a b | erase a | clear q =>
    rfl
  | send q e =>
    cases he : ExpressionEvaluation.eval e p.data p.wires <;>
      simp [prepare,Action.eval,Action.node,execute,Payload.at,he,Runtime.payload,
        commit,put,Runtime.setQueue]
  | receive q n =>
    cases hq : p.queues q <;>
      simp [prepare,Action.eval,Action.node,execute,Payload.at,hq,Runtime.payload,
        commit,put,Runtime.setQueue,Runtime.setWire]

theorem prepare_agrees (cap : Nat → Nat) (a : Action α) (p q : Payload)
    (h : Agrees (actionReads a) p q) : prepare cap a p = prepare cap a q := by
  cases a with
  | wire n e | assign n e => simp [prepare,ExpressionDependencies.agrees e p q h]
  | store a j e =>
    have ha : p.data.arrays a = q.data.arrays a := by
      have hh := h (.array a) (by simp [actionReads]); simpa [get] using hh
    have hs : Agrees (ExpressionDependencies.reads j ++ ExpressionDependencies.reads e) p q := fun c hc => h c (by simp [actionReads,hc])
    have hs' := agrees_append hs
    simp [prepare,ha,ExpressionDependencies.agrees j p q hs'.1,ExpressionDependencies.agrees e p q hs'.2]
  | snapshot a b =>
    have hh := h (.array b) (by simp [actionReads])
    have hb : p.data.arrays b = q.data.arrays b := by simpa [get] using hh
    simp [prepare,hb]
  | erase | clear => rfl
  | send n e =>
    have hh := h (.queue n) (by simp [actionReads])
    have hq : p.queues n = q.queues n := by simpa [get] using hh
    have he := ExpressionDependencies.agrees e p q (fun c hc => h c (by simp [actionReads,hc]))
    simp [prepare,hq,he]
  | receive n r =>
    have hh := h (.queue n) (by simp [actionReads])
    have hq : p.queues n = q.queues n := by simpa [get] using hh
    simp [prepare,hq]

theorem prepare_writes {a : Action α} (h : prepare cap a p = some us) :
    ∀ u ∈ us, u.1 ∈ actionWrites a := by
  cases a with
  | wire n e | assign n e =>
    cases he : ExpressionEvaluation.eval e p.data p.wires <;> simp [prepare,he] at h
    all_goals subst us; simp [actionWrites]
  | store n j e =>
    cases hj : ExpressionEvaluation.eval j p.data p.wires <;> cases he : ExpressionEvaluation.eval e p.data p.wires <;>
      simp [prepare,hj,he] at h
    obtain ⟨_,h⟩ := h; subst us; simp [actionWrites]
  | send q e =>
    cases he : ExpressionEvaluation.eval e p.data p.wires <;> simp [prepare,he] at h
    rcases h with ⟨_,h⟩; subst us; simp [actionWrites]
  | receive q n =>
    cases hq : p.queues q <;> simp [prepare,hq] at h
    subst us; simp [actionWrites]
  | snapshot | erase | clear =>
    simp [prepare] at h; subst us; simp [actionWrites]

end IRComparison.Circuit.Pipelining
