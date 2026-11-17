import IRComparison.Circuit.Pipelining.RTL

namespace IRComparison.Circuit.Pipelining

def renameExpr (m : Nat → Nat) : Expr → Expr
  | .wire k => .wire (m k)
  | .memory a j => .memory a (renameExpr m j)
  | .bin op a b => .bin op (renameExpr m a) (renameExpr m b)
  | .wrap32 a => .wrap32 (renameExpr m a)
  | .natIndex a => .natIndex (renameExpr m a)
  | .select c a b => .select (renameExpr m c) (renameExpr m a) (renameExpr m b)
  | .seq a b => .seq (renameExpr m a) (renameExpr m b)
  | e => e

def renameAction (m : Nat → Nat) : Action → Action
  | .wire k e => .wire (m k) (renameExpr m e)
  | .assign k e => .assign k (renameExpr m e)
  | .store a j e => .store a (renameExpr m j) (renameExpr m e)
  | .send q e => .send q (renameExpr m e)
  | .receive q k => .receive q (m k)
  | a => a

def wireIds (cs : List Cell) : List Nat := cs.filterMap (fun c => match c with | .wire k => some k | _ => none)

theorem wireIds_mem : k ∈ wireIds cs ↔ Cell.wire k ∈ cs := by
  simp only [wireIds,List.mem_filterMap]
  constructor
  · rintro ⟨c,hc,hh⟩; cases c <;> simp_all
  · intro h; exact ⟨.wire k,h,rfl⟩

def LiveRel (m : Nat → Nat) (live : List Nat) (p q : Payload) : Prop :=
  p.data = q.data ∧ p.queues = q.queues ∧ ∀ k ∈ live, p.wires k = q.wires (m k)

theorem liveRel_mono (h : LiveRel m (wireIds ys) p q) (sub : ∀ c ∈ xs, c ∈ ys) :
    LiveRel m (wireIds xs) p q :=
  ⟨h.1,h.2.1,fun k hk => h.2.2 k (wireIds_mem.mpr (sub _ (wireIds_mem.mp hk)))⟩

theorem renameExpr_correct (e : Expr) (h : LiveRel m (wireIds (reads e)) p q) :
    (renameExpr m e).eval q.data q.wires = e.eval p.data p.wires := by
  induction e with
  | fail | lit => rfl
  | wire k => simp [renameExpr,Expr.eval,← h.2.2 k (by simp [wireIds,reads])]
  | reg k => simp [renameExpr,Expr.eval,h.1]
  | memory a j ih =>
    have hj := ih (liveRel_mono h (by intro c hc; simp [reads,hc]))
    simp [renameExpr,Expr.eval,hj,h.1]
  | bin op a b ia ib | seq a b ia ib =>
    simp [renameExpr,Expr.eval,ia (liveRel_mono h (by intro c hc; simp [reads,hc])),
      ib (liveRel_mono h (by intro c hc; simp [reads,hc]))]
  | natIndex a ih | wrap32 a ih => simp [renameExpr,Expr.eval,ih h]
  | select c a b ic ia ib =>
    simp [renameExpr,Expr.eval,ic (liveRel_mono h (by intro c hc; simp [reads,hc])),
      ia (liveRel_mono h (by intro c hc; simp [reads,hc])),ib (liveRel_mono h (by intro c hc; simp [reads,hc]))]

def renameCell (m : Nat → Nat) : Cell → Cell
  | .wire k => .wire (m k)
  | c => c

def renameUpdate (m : Nat → Nat) (u : Update) : Update := (renameCell m u.1,u.2)

theorem prepare_rename (a : Action) (h : LiveRel m (wireIds (actionReads a)) p q) :
    prepare cap (renameAction m a) q = (prepare cap a p).map (List.map (renameUpdate m)) := by
  have sub (e : Expr) (hx : ∀ c ∈ reads e, c ∈ actionReads a) : LiveRel m (wireIds (reads e)) p q :=
    ⟨h.1,h.2.1,fun k hk => h.2.2 k (wireIds_mem.mpr (hx _ (wireIds_mem.mp hk)))⟩
  cases a with
  | wire k e | assign k e =>
    have he := renameExpr_correct e (sub e (by intro c hc; simp [actionReads,hc]))
    simp only [renameAction,prepare,expressionEvaluation_original,he]
    cases e.eval p.data p.wires <;> rfl
  | store a j e =>
    have hj := renameExpr_correct j (sub j (by intro c hc; simp [actionReads,hc]))
    have he := renameExpr_correct e (sub e (by intro c hc; simp [actionReads,hc]))
    simp only [renameAction,prepare,expressionEvaluation_original]
    rw [hj,he]
    simp only [← h.1]
    cases hjv : j.eval p.data p.wires <;> cases hev : e.eval p.data p.wires <;> simp only [hjv,hev,bind,Option.bind,Option.map_none]
    split <;> rfl
  | send n e =>
    have he := renameExpr_correct e (sub e (by intro c hc; simp [actionReads,hc]))
    simp only [renameAction,prepare,expressionEvaluation_original,he,← h.2.1]
    cases hev : e.eval p.data p.wires <;> simp only [hev,bind,Option.bind,Option.map_none]
    split <;> rfl
  | snapshot | erase | clear => simp [renameAction,prepare,expressionEvaluation_original,renameUpdate,renameCell,← h.1,← h.2.1]
  | receive n k =>
    simp only [renameAction,prepare,expressionEvaluation_original,← h.2.1]
    cases p.queues n <;> rfl

def batchReads (as : List Action) := wireIds (as.flatMap actionReads)
def batchWrites (as : List Action) := wireIds (as.flatMap actionWrites)

theorem allPrepared_rename (as : List Action) (h : LiveRel m (batchReads as) p q) :
    allPrepared cap q (as.map (renameAction m)) =
      (allPrepared cap p as).map (List.map (renameUpdate m)) := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    have ha : LiveRel m (wireIds (actionReads a)) p q :=
      ⟨h.1,h.2.1,fun k hk => h.2.2 k (by simpa [batchReads,wireIds] using Or.inl hk)⟩
    have hs : LiveRel m (batchReads as) p q :=
      ⟨h.1,h.2.1,fun k hk => h.2.2 k (by simpa [batchReads,wireIds] using Or.inr hk)⟩
    simp only [List.map_cons,allPrepared,prepare_rename a ha,ih hs]
    cases allPrepared cap p as <;> cases prepare cap a p <;> simp [List.map_append]

theorem allPrepared_writes (as : List Action) (h : allPrepared cap p as = some us) :
    ∀ u ∈ us, u.1 ∈ as.flatMap actionWrites := by
  induction as generalizing us with
  | nil => simp [allPrepared] at h; subst us; simp
  | cons a as ih =>
    cases ha : prepare cap a p <;> cases hs : allPrepared cap p as <;> simp [allPrepared,ha,hs] at h
    subst us
    intro u hu
    rcases List.mem_append.mp hu with hu | hu
    · exact List.mem_append_left _ (prepare_writes ha u hu)
    · exact List.mem_append_right _ (ih hs u hu)

/-- New values may overwrite a register whose LAST read occurs on this edge:
all operands read the old state. Only values live AFTER the edge interfere. -/
def NoClobber (m : Nat → Nat) (live : List Nat) (us : List Update) : Prop :=
  ∀ k, Cell.wire k ∈ us.map Prod.fst → ∀ j ∈ live, m k = m j → k = j

def PendingRel (m : Nat → Nat) (live : List Nat) (us : List Update) (p q : Payload) : Prop :=
  p.data = q.data ∧ p.queues = q.queues ∧
  ∀ k ∈ live, Cell.wire k ∉ us.map Prod.fst → p.wires k = q.wires (m k)

def GoodUpdate (u : Update) : Prop := match u with
  | (.wire _,.scalar _) | (.reg _,.scalar _) | (.array _,.array _) | (.queue _,.queue _) => True
  | _ => False

theorem prepare_shape {α : Type} [ExpressionEvaluation α] {a : Action α} (h : prepare cap a p = some us) :
    us.map Prod.fst = actionWrites a ∧ ∀ u ∈ us, GoodUpdate u := by
  cases a with
  | wire n e | assign n e =>
    cases he : ExpressionEvaluation.eval e p.data p.wires <;> simp [prepare,he] at h
    all_goals subst us; simp [actionWrites,GoodUpdate]
  | store n j e =>
    cases hj : ExpressionEvaluation.eval j p.data p.wires <;> cases he : ExpressionEvaluation.eval e p.data p.wires <;> simp [prepare,hj,he] at h
    obtain ⟨_,h⟩ := h; subst us; simp [actionWrites,GoodUpdate]
  | send q e =>
    cases he : ExpressionEvaluation.eval e p.data p.wires <;> simp [prepare,he] at h
    obtain ⟨_,h⟩ := h; subst us; simp [actionWrites,GoodUpdate]
  | receive q n =>
    cases hq : p.queues q <;> simp [prepare,hq] at h
    subst us; simp [actionWrites,GoodUpdate]
  | snapshot | erase | clear =>
    simp [prepare] at h; subst us; simp [actionWrites,GoodUpdate]

theorem allPrepared_shape (as : List Action) (h : allPrepared cap p as = some us) :
    us.map Prod.fst = as.flatMap actionWrites ∧ ∀ u ∈ us, GoodUpdate u := by
  induction as generalizing us with
  | nil => simp [allPrepared] at h; subst us; simp
  | cons a as ih =>
    cases ha : prepare cap a p <;> cases hs : allPrepared cap p as <;> simp [allPrepared,ha,hs] at h
    subst us
    have ha' := prepare_shape ha
    have hs' := ih hs
    refine ⟨by simp [List.map_append,ha'.1,hs'.1],?_⟩
    intro u hu
    rcases List.mem_append.mp hu with hu | hu
    · exact ha'.2 u hu
    · exact hs'.2 u hu

theorem pending_put (u : Update) (good : GoodUpdate u)
    (h : PendingRel m live (u::us) p q) (hn : NoClobber m live (u::us)) :
    PendingRel m live us (put p u.1 u.2) (put q (renameCell m u.1) u.2) := by
  rcases h with ⟨hd,hq,hw⟩
  rcases u with ⟨c,v⟩
  cases c with
  | reg slot | array slot | queue slot =>
    cases v <;> simp only [GoodUpdate] at good <;> try contradiction
    all_goals refine ⟨?_,?_,?_⟩
    all_goals try {simp [put,renameCell,IRComparison.State.set,hd,hq]}
    all_goals intro k hk hm
    all_goals simpa [put,renameCell] using hw k hk (by simpa using hm)
  | wire slot =>
    cases v <;> simp only [GoodUpdate] at good <;> try contradiction
    rename_i value
    refine ⟨hd,hq,?_⟩
    intro k hk hmissing
    by_cases he : k = slot
    · subst k; simp [put,renameCell]
    · have hm : m k ≠ m slot := by
        intro eq; exact he (hn slot (by simp) k hk eq.symm).symm
      simp [put,renameCell,he,hm,hw k hk (by simpa [he] using hmissing)]

theorem commit_rename (us : List Update) (p q : Payload)
    (good : ∀ u ∈ us, GoodUpdate u)
    (h : PendingRel m live us p q) (hn : NoClobber m live us) :
    LiveRel m live (commit us p) (commit (us.map (renameUpdate m)) q) := by
  induction us generalizing p q with
  | nil => exact ⟨h.1,h.2.1,fun k hk => h.2.2 k hk (by simp)⟩
  | cons u us ih =>
    change LiveRel m live (commit us (put p u.1 u.2))
      (commit (us.map (renameUpdate m)) (put q (renameCell m u.1) u.2))
    exact ih _ _ (fun u hu => good u (by simp [hu])) (pending_put u (good u (by simp)) h hn)
      (fun k hk j hj he => hn k (by simp [hk]) j hj he)

def liveBefore (as : List Action) (after : List Nat) : List Nat :=
  batchReads as ++ after.filter (fun k => !(batchWrites as).contains k)

def allocationSafe (m : Nat → Nat) (as : List Action) (after : List Nat) : Bool :=
  (batchWrites as).all (fun k => after.all (fun j => m k != m j || k == j))

theorem clock_rename (as : List Action) (h : LiveRel m (liveBefore as after) p q)
    (safe : allocationSafe m as after = true) :
    Option.Rel (LiveRel m after) (clock cap as p) (clock cap (as.map (renameAction m)) q) := by
  have hr : LiveRel m (batchReads as) p q :=
    ⟨h.1,h.2.1,fun k hk => h.2.2 k (List.mem_append_left _ hk)⟩
  simp only [clock,clockFrom_prepared,allPrepared_rename as hr]
  cases hp : allPrepared cap p as with
  | none => exact .none
  | some us =>
    apply Option.Rel.some
    apply commit_rename us p q (allPrepared_shape as hp).2
    · refine ⟨h.1,h.2.1,?_⟩
      intro k hk hmissing
      apply h.2.2 k
      apply List.mem_append_right
      have notWritten : k ∉ batchWrites as := by
        intro written
        exact hmissing (by rw [(allPrepared_shape as hp).1]; exact wireIds_mem.mp written)
      simpa [notWritten] using hk
    · intro k hk j hj he
      obtain ⟨u,hu,hu'⟩ := List.mem_map.mp hk
      have kw : k ∈ batchWrites as := wireIds_mem.mpr (hu' ▸ allPrepared_writes as hp u hu)
      have hs := List.all_eq_true.mp (List.all_eq_true.mp safe k kw) j hj
      simpa [he] using hs

end IRComparison.Circuit.Pipelining
