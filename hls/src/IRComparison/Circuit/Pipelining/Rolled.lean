import IRComparison.Circuit.Pipelining.StructuredRules

namespace IRComparison.Circuit.Pipelining

variable {α : Type} [ExpressionEvaluation α] [ExpressionDependencies α]
variable {a b steady t : ClockTree α} {e : α} {bs : Batches α}
variable {tail head : List (Action α)} {rest : Batches α}

/-- Rotation does not enumerate iterations. `a` is the prologue, `b` the
drain; the steady loop overlaps the previous tail with the next head. -/
def rotate (e : α) (a b steady : ClockTree α) : ClockTree α :=
  .branch e (.seq a (.seq (.loop e steady) b)) (.block [])

private theorem drain_error
    (hb : b.Eval cap p none)
    (merge : ∀ p r, (ClockTree.seq b a).Eval cap p r → steady.Eval cap p r) :
    (ClockTree.seq (.loop e steady) b).Eval cap p none := by
  cases he : ExpressionEvaluation.eval e p.data p.wires with
  | none => exact .seq_error (.loop_error he)
  | some v =>
    by_cases hv : v = 0
    · subst v; exact .seq (.loop_stop he) hb
    · exact .seq_error (.loop_body_error he hv (merge _ _ (.seq_error hb)))

private theorem rotate_tail
    (stable : ∀ p q, b.Eval cap p (some q) → ExpressionEvaluation.eval e p.data p.wires = ExpressionEvaluation.eval e q.data q.wires)
    (merge : ∀ p r, (ClockTree.seq b a).Eval cap p r → steady.Eval cap p r)
    (run : (ClockTree.loop e (.seq a b)).Eval cap q r)
    (before : b.Eval cap p (some q)) :
    (ClockTree.seq (.loop e steady) b).Eval cap p r := by
  generalize eq : ClockTree.loop e (.seq a b) = c at run
  induction run generalizing p with
  | block | seq_error | seq | branch_error | branch_yes | branch_no => cases eq
  | loop_error he =>
    cases eq
    exact .seq_error (.loop_error ((stable _ _ before).trans he))
  | loop_stop he =>
    cases eq
    exact .seq (.loop_stop ((stable _ _ before).trans he)) before
  | loop_body_error he ne body ih =>
    cases eq
    have guard := (stable _ _ before).trans he
    cases body with
    | seq_error ha =>
      exact .seq_error (.loop_body_error guard ne (merge _ _ (.seq before ha)))
    | seq ha hb =>
      have tail := drain_error (e := e) hb merge
      cases tail with
      | seq_error hl => exact .seq_error (.loop_next guard ne (merge _ _ (.seq before ha)) hl)
      | seq hl hb => exact .seq (.loop_next guard ne (merge _ _ (.seq before ha)) hl) hb
  | loop_next he ne body rest ib ir =>
    cases eq
    have guard := (stable _ _ before).trans he
    cases body with
    | seq ha hb =>
      have tail := ir hb rfl
      cases tail with
      | seq_error hl => exact .seq_error (.loop_next guard ne (merge _ _ (.seq before ha)) hl)
      | seq hl hb => exact .seq (.loop_next guard ne (merge _ _ (.seq before ha)) hl) hb

/-- General finite-execution rotation rule, including zero iterations and
failed reads. No trip count, counter shape, or successful-execution premise. -/
theorem rotate_correct
    (stable : ∀ p q, b.Eval cap p (some q) → ExpressionEvaluation.eval e p.data p.wires = ExpressionEvaluation.eval e q.data q.wires)
    (merge : ∀ p r, (ClockTree.seq b a).Eval cap p r → steady.Eval cap p r)
    (run : (ClockTree.loop e (.seq a b)).Eval cap p r) :
    (rotate e a b steady).Eval cap p r := by
  cases run with
  | loop_error he => exact .branch_error he
  | loop_stop he => exact .branch_no he (.block)
  | loop_body_error he ne body =>
    apply ClockTree.Eval.branch_yes he ne
    cases body with
    | seq_error ha => exact .seq_error ha
    | seq ha hb => exact .seq ha (drain_error hb merge)
  | loop_next he ne body rest =>
    apply ClockTree.Eval.branch_yes he ne
    cases body with
    | seq ha hb => exact .seq ha (rotate_tail stable merge rest hb)

private theorem clockFrom_frame (as : List (Action α))
    (apart : ∀ a ∈ as, Apart (actionWrites a) [c])
    (h : clockFrom cap old as p = some q) : get p c = get q c := by
  induction as generalizing p with
  | nil => cases h; rfl
  | cons a as ih =>
    simp only [clockFrom] at h
    cases hp : prepare cap a old with
    | none => simp [hp] at h
    | some us =>
      simp only [hp,Option.bind_some] at h
      have frame := commit_frame us p c (fun u hu eq =>
        apart a (by simp) _ (prepare_writes hp u hu) (by simp [eq]))
      exact frame.symm.trans (ih (fun b hb => apart b (by simp [hb])) h)

private theorem block_result (h : (ClockTree.block bs).Eval cap p r) :
    runBatches cap bs p = r := by cases h; rfl

private theorem tail_stable
    (apart : ∀ a ∈ tail, Apart (actionWrites a) (ExpressionDependencies.reads e))
    (h : (ClockTree.block [tail]).Eval cap p (some q)) :
    ExpressionEvaluation.eval e p.data p.wires = ExpressionEvaluation.eval e q.data q.wires := by
  have hh := block_result h
  simp only [runBatches] at hh
  apply ExpressionDependencies.agrees
  intro c hc
  apply clockFrom_frame tail (cap := cap) (old := p)
  · intro a ha d hd he
    have eq : d = c := by simpa using he
    exact apart a ha d hd (eq ▸ hc)
  · simpa using hh

private theorem runBatches_append (as bs : Batches α) (p : Payload) :
    runBatches cap (as ++ bs) p = (runBatches cap as p).bind (runBatches cap bs) := by
  induction as generalizing p with
  | nil => rfl
  | cons a as ih =>
    simp only [List.cons_append,runBatches,Option.bind_assoc]
    cases he : clock cap a p <;> simp [ih]

private theorem block_split (as bs : Batches α)
    (h : (ClockTree.block (as ++ bs)).Eval cap p r) :
    (ClockTree.seq (.block as) (.block bs)).Eval cap p r := by
  cases h
  rw [runBatches_append]
  cases he : runBatches cap as p with
  | none => exact .seq_error (by simpa [he] using (ClockTree.Eval.block (cap := cap) (bs := as) (p := p)))
  | some q =>
    exact .seq (by simpa [he] using (ClockTree.Eval.block (cap := cap) (bs := as) (p := p))) (.block)

private theorem loop_map
    (body : ∀ p r, a.Eval cap p r → b.Eval cap p r)
    (h : (ClockTree.loop e a).Eval cap p r) : (ClockTree.loop e b).Eval cap p r := by
  generalize eq : ClockTree.loop e a = c at h
  induction h with
  | block | seq_error | seq | branch_error | branch_yes | branch_no => cases eq
  | loop_error he => cases eq; exact .loop_error he
  | loop_stop he => cases eq; exact .loop_stop he
  | loop_body_error he ne hb ih => cases eq; exact .loop_body_error he ne (body _ _ hb)
  | loop_next he ne hb hl ib il => cases eq; exact .loop_next he ne (body _ _ hb) (il rfl)

private theorem boundary_merge
    (safe : BundleSafe (tail ++ head))
    (h : (ClockTree.seq (.block [tail]) (.block (head::rest))).Eval cap p r) :
    (ClockTree.block ((tail ++ head)::rest)).Eval cap p r := by
  have parts := List.pairwise_append.mp safe
  have eq : ∀ p, clock cap (tail ++ head) p = (clock cap tail p).bind (clock cap head) := by
    intro p
    rw [clock_correct _ safe,evalList_append,← clock_correct _ parts.1]
    cases hc : clock cap tail p <;> simp [clock_correct _ parts.2.1]

  have hr : runBatches cap ((tail ++ head)::rest) p =
      (runBatches cap [tail] p).bind (runBatches cap (head::rest)) := by
    simp [runBatches,eq,Option.bind_assoc]
  have result : (runBatches cap [tail] p).bind (runBatches cap (head::rest)) = r := by
    cases h with
    | seq_error hb => rw [block_result hb]; rfl
    | seq hb ha => rw [block_result hb]; exact block_result ha
  rw [← result,← hr]
  exact .block

/-- Only a straight-line clock block is rotated. The check is over effects,
not a bound on iteration count or a restriction on accepted input programs.
A rejected candidate remains a rolled loop. -/
def overlapLoop (e : α) (bs : Batches α) : ClockTree α :=
  match bs.reverse with
  | tail :: revPrefix => match revPrefix.reverse with
    | head :: rest =>
      if BundleSafe (tail ++ head) ∧ (∀ a ∈ tail, Apart (actionWrites a) (ExpressionDependencies.reads e)) then
        rotate e (.block (head::rest)) (.block [tail]) (.block ((tail ++ head)::rest))
      else .loop e (.block bs)
    | [] => .loop e (.block bs)
  | [] => .loop e (.block bs)

theorem overlapLoop_correct (h : (ClockTree.loop e (.block bs)).Eval cap p r) :
    (overlapLoop e bs).Eval cap p r := by
  unfold overlapLoop
  split
  · rename_i tail revPrefix hr
    split
    · rename_i head rest hp
      split
      · rename_i checks
        have shape : bs = (head::rest) ++ [tail] := by
          have hh := congrArg List.reverse hr
          simpa [hp] using hh
        rw [shape] at h
        exact rotate_correct (fun _ _ hb => tail_stable checks.2 hb)
          (fun _ _ hm => boundary_merge checks.1 hm)
          (loop_map (fun _ _ hb => block_split _ _ hb) h)
      · exact h
    · exact h
  · exact h

/-- One bottom-up pass. It never traverses the newly produced steady loop,
so code growth depends on syntax, not on runtime trip counts. -/
def overlapLoops : ClockTree α → ClockTree α
  | .block bs => .block bs
  | .seq a b => .seq (overlapLoops a) (overlapLoops b)
  | .branch e a b => .branch e (overlapLoops a) (overlapLoops b)
  | .loop e (.block bs) => overlapLoop e bs
  | .loop e body => .loop e (overlapLoops body)

theorem overlapLoops_correct (h : t.Eval cap p r) : (overlapLoops t).Eval cap p r := by
  induction h with
  | block => exact .block
  | seq_error _ ih => exact .seq_error ih
  | seq _ _ ia ib => exact .seq ia ib
  | branch_error he => exact .branch_error he
  | branch_yes he ne _ ih => exact .branch_yes he ne ih
  | branch_no he _ ih => exact .branch_no he ih
  | @loop_error e body p he =>
    cases body <;> simp only [overlapLoops]
    · exact overlapLoop_correct (.loop_error he)
    all_goals exact .loop_error he
  | @loop_stop e body p he =>
    cases body <;> simp only [overlapLoops]
    · exact overlapLoop_correct (.loop_stop he)
    all_goals exact .loop_stop he
  | @loop_body_error v body p e he ne hb ih =>
    cases body <;> simp only [overlapLoops] at *
    · exact overlapLoop_correct (.loop_body_error he ne hb)
    all_goals exact .loop_body_error he ne ih
  | @loop_next v body p q e result he ne hb hl ib il =>
    cases body <;> simp only [overlapLoops] at *
    · exact overlapLoop_correct (.loop_next he ne hb hl)
    all_goals exact .loop_next he ne ib il

end IRComparison.Circuit.Pipelining
