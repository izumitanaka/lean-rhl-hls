import IRComparison.Circuit.Pipelining.Independence

/-! A schedule is metadata on existing actions: a list of operation IDs for
each clock. No new expression, memory or communication language is introduced.
Rejected schedules fall back to the original action order, not rejection of
the program. -/
namespace IRComparison.Circuit.Pipelining

variable {α : Type} [ExpressionEvaluation α] [ExpressionDependencies α]

abbrev Cycles := List (List Nat)

def actionAt (code : Array (Action α)) (id : Nat) : Action α :=
  code[id]?.getD (.wire 0 ExpressionEvaluation.invalid)

def sourceIds (code : Array (Action α)) : List Nat := List.range code.size

def sequential (code : Array (Action α)) : Cycles := (sourceIds code).map (fun id => [id])

def runCycles (cap : Nat → Nat) (code : Array (Action α)) : Cycles → Payload → Option Payload
  | [], p => some p
  | ids :: rest, p => (clock cap (ids.map (actionAt code)) p).bind (runCycles cap code rest)

def safe (code : Array (Action α)) (cycles : Cycles) : Bool :=
  cycles.all (fun ids => decide (BundleSafe (ids.map (actionAt code))))

def valid (code : Array (Action α)) (cycles : Cycles) : Bool :=
  safe code cycles &&
    reorder (fun a b => independent (actionAt code a) (actionAt code b))
      cycles.flatten (sourceIds code)

theorem evalList_map {δ ε σ : Type} (f : δ → ε) (act : ε → σ → Option σ) (xs : List δ) :
    evalList act (xs.map f) = evalList (fun x => act (f x)) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => funext s; simp only [List.map_cons,evalList,ih]

theorem runCycles_flatten (cap : Nat → Nat) (code : Array (Action α)) (cycles : Cycles)
    (h : safe code cycles = true) :
    runCycles cap code cycles = evalList (fun id => (actionAt code id).eval cap) cycles.flatten := by
  induction cycles with
  | nil => rfl
  | cons ids rest ih =>
    have hs : BundleSafe (ids.map (actionAt code)) ∧ safe code rest = true := by
      simpa [safe] using h
    funext p
    have first := bundle_rule (cap := cap) hs.1
    have rest := Relational.of_eq (fun p => (congrFun (ih hs.2) p).symm)
    have composed := Relational.eq_of_translation (Relational.seq first rest) p
    simpa only [runCycles,List.flatten_cons,evalList_append,evalList_map] using composed.symm

def sourceEval (cap : Nat → Nat) (code : Array (Action α)) : Payload → Option Payload :=
  evalList (fun id => (actionAt code id).eval cap) (sourceIds code)

theorem actions_sourceIds (code : Array (Action α)) :
    (sourceIds code).map (actionAt code) = code.toList := by
  apply List.ext_getElem
  · simp [sourceIds]
  · intro i h₁ h₂
    simp only [sourceIds,List.getElem_map,List.getElem_range,actionAt]
    simp [Array.getElem?_eq_getElem (by simpa using h₂)]

theorem sourceEval_eq (code : Array (Action α)) :
    sourceEval cap code = evalList (Action.eval cap) code.toList := by
  rw [← actions_sourceIds code,evalList_map]
  rfl

theorem evalList_flatMap {δ ε σ : Type} (act : ε → σ → Option σ) (f : δ → List ε) (xs : List δ) :
    evalList act (xs.flatMap f) = evalList (fun x => evalList act (f x)) xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih => funext s; simp only [List.flatMap_cons,evalList_append,ih,evalList]

theorem valid_correct {code : Array (Action α)} (h : valid code cycles = true) :
    ∀ p, runCycles cap code cycles p = sourceEval cap code p := by
  have hs : safe code cycles = true ∧
      reorder (fun a b => independent (actionAt code a) (actionAt code b)) cycles.flatten (sourceIds code) = true := by
    simpa [valid] using h
  rw [runCycles_flatten cap code cycles hs.1]
  exact reorder_sound (fun id => (actionAt code id).eval cap)
    (fun a b => independent (actionAt code a) (actionAt code b))
    (fun a b => independent_sound cap (actionAt code a) (actionAt code b)) _ _ hs.2

theorem sequential_correct (code : Array (Action α)) :
    runCycles cap code (sequential code) = sourceEval cap code := by
  have h (ids : List Nat) : runCycles cap code (ids.map (fun id => [id])) =
      evalList (fun id => (actionAt code id).eval cap) ids := by
    induction ids with
    | nil => rfl
    | cons a ids ih =>
      funext p
      simp only [List.map_cons,runCycles,clock,clockFrom,ih,evalList,
        List.map_cons,List.map_nil]
      rw [← prepare_correct]
      cases prepare cap (actionAt code a) p <;> rfl
  exact h _

structure Plan where
  cycles : Cycles
  accepted : Bool
  deriving Repr

/-- Both candidate construction and acceptance are ordinary compiler code.
`compile_correct` covers all proposals, initial states and failure outcomes. -/
def compile (code : Array (Action α)) (proposal : Cycles) : Plan :=
  if valid code proposal then ⟨proposal,true⟩ else ⟨sequential code,false⟩

theorem compile_correct (code : Array (Action α)) (proposal : Cycles) (p : Payload) :
    runCycles cap code (compile code proposal).cycles p = sourceEval cap code p := by
  unfold compile
  split
  · exact valid_correct ‹_› p
  · exact congrFun (sequential_correct code) p

theorem compile_rhl (code : Array (Action α)) (proposal : Cycles) :
    RHL Eq (sourceEval cap code) (runCycles cap code (compile code proposal).cycles) Eq := by
  intro p q h; subst q
  exact (compile_correct code proposal p).symm

/-- The unchanged sequential Schedule language can still express the source
of this pass. This connects to the existing assembler correctness theorem. -/
def asSchedule (code : Array (Action α)) : List Nat → Circuit.Schedule α
  | [] => .skip
  | id :: ids => .seq (.step (actionAt code id)) (asSchedule code ids)

theorem asSchedule_eval (code : Array (Action α)) (ids : List Nat) (p : Payload) :
    (asSchedule code ids).Eval cap p (evalList (fun id => (actionAt code id).eval cap) ids p) := by
  induction ids generalizing p with
  | nil => exact .skip
  | cons id ids ih =>
    cases ha : (actionAt code id).eval cap p with
    | none =>
      simp only [asSchedule,evalList,ha,Option.bind_none]
      exact .seq_error (by simpa [ha] using Circuit.Schedule.Eval.step (a := actionAt code id) (p := p) (cap := cap))
    | some q =>
      simp only [asSchedule,evalList,ha,Option.bind_some]
      exact .seq (by simpa [ha] using Circuit.Schedule.Eval.step (a := actionAt code id) (p := p) (cap := cap)) (ih q)

/-- Counted loop with stage boundaries selected by a strategy. The body is
existing code instantiated at each iteration; bounds and arbitrary II are
not baked into the proof. Explicit instantiation is a prototype limitation. -/
structure Loop (α : Type := Expr) where
  count : Nat
  stages : Nat
  body : Nat → Nat → Action α

def Loop.code (l : Loop α) : Array (Action α) :=
  ((List.range l.count).flatMap (fun i => (List.range l.stages).map (l.body i))).toArray

/-- The sequential loop semantics uses the same existing actions. -/
def Loop.eval (l : Loop α) (cap : Nat → Nat) : Payload → Option Payload :=
  evalList (fun i => evalList (fun k => (l.body i k).eval cap) (List.range l.stages))
    (List.range l.count)

theorem Loop.source_correct (l : Loop α) : sourceEval cap l.code = l.eval cap := by
  rw [sourceEval_eq]
  simp only [Loop.code,List.toList_toArray,evalList_flatMap,evalList_map,Loop.eval]

/-- A diagonal wavefront: iteration i, stage k executes at i * II + k.
II=0 is normalized to one. Warm-up, empty cycles and drain are explicit. -/
def Loop.proposal (l : Loop α) (ii : Nat) : Cycles :=
  let cycles := if l.count = 0 then 0 else (l.count - 1) * max 1 ii + l.stages
  (List.range cycles).map (fun t => (sourceIds l.code).filter (fun id =>
    id / l.stages * max 1 ii + id % l.stages == t))

def Loop.pipeline (l : Loop α) (ii : Nat) : Plan := compile l.code (l.proposal ii)

theorem Loop.pipeline_correct (l : Loop α) (ii : Nat) (p : Payload) :
    runCycles cap l.code (l.pipeline ii).cycles p = sourceEval cap l.code p :=
  compile_correct l.code (l.proposal ii) p

theorem Loop.pipeline_rhl (l : Loop α) (ii : Nat) :
    RHL Eq (l.eval cap) (runCycles cap l.code (l.pipeline ii).cycles) Eq := by
  rw [← l.source_correct]
  exact compile_rhl l.code (l.proposal ii)

/-- State relation at an arbitrary target clock: the original execution and
the remaining scheduled continuation have the same eventual result. This
allows different iteration progress; it does not equate intermediate stores. -/
def Related (cap : Nat → Nat) (code : Array (Action α)) (initial : Payload)
    (remaining : Cycles) (current : Option Payload) : Prop :=
  sourceEval cap code initial = current.bind (runCycles cap code remaining)

theorem related_initial (code : Array (Action α)) (proposal : Cycles) (initial : Payload) :
    Related cap code initial (compile code proposal).cycles (some initial) :=
  (compile_correct code proposal initial).symm

theorem related_tick {code : Array (Action α)} (h : Related cap code initial (ids :: rest) current) :
    Related cap code initial rest (current.bind (clock cap (ids.map (actionAt code)))) := by
  unfold Related at *
  simpa only [runCycles, Option.bind_assoc] using h

theorem related_done {code : Array (Action α)} (h : Related cap code initial [] current) :
    current = sourceEval cap code initial := by
  simpa [Related,runCycles] using h.symm

structure Runtime where
  remaining : Cycles
  payload : Option Payload

def tick (cap : Nat → Nat) (code : Array (Action α)) (r : Runtime) : Runtime :=
  match r.remaining with
  | [] => r
  | ids :: rest => ⟨rest,r.payload.bind (clock cap (ids.map (actionAt code)))⟩

def run (cap : Nat → Nat) (code : Array (Action α)) : Nat → Runtime → Runtime
  | 0,r => r
  | n+1,r => run cap code n (tick cap code r)

theorem run_finishes {code : Array (Action α)} (cycles : Cycles) (p : Option Payload) :
    run cap code cycles.length ⟨cycles,p⟩ = ⟨[],p.bind (runCycles cap code cycles)⟩ := by
  induction cycles generalizing p with
  | nil => simp [run,runCycles]
  | cons ids rest ih =>
    simp only [List.length_cons,run,tick,ih,runCycles,Option.bind_assoc]

theorem pipeline_finishes (l : Loop α) (ii : Nat) (p : Payload) :
    run cap l.code (l.pipeline ii).cycles.length ⟨(l.pipeline ii).cycles,some p⟩ =
      ⟨[],sourceEval cap l.code p⟩ := by
  rw [run_finishes]
  simp only [Option.bind_some,l.pipeline_correct]

end IRComparison.Circuit.Pipelining
