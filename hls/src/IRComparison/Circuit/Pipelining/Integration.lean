import IRComparison.Circuit.Pipelining.Schedule
import IRComparison.Circuit.CommandSound

namespace IRComparison.Circuit.Pipelining

/-- Extract only existing straight-line actions. Dynamic control is retained
by `transform`; it is never silently flattened or speculatively executed. -/
def flatten {α : Type} : Circuit.Schedule α → Option (List (Action α))
  | .skip => some []
  | .step a => some [a]
  | .seq a b => do return (← flatten a) ++ (← flatten b)
  | .branch .. | .loop .. => none

theorem flatten_correct {α : Type} [ExpressionEvaluation α] {s : Circuit.Schedule α} {actions : List (Action α)} (h : s.Eval cap p result) (hf : flatten s = some actions) :
    evalList (Action.eval cap) actions p = result := by
  induction h generalizing actions with
  | skip => simp [flatten] at hf; subst actions; rfl
  | step => simp [flatten] at hf; subst actions; simp [evalList]
  | @seq_error a p b ha ih =>
    cases hx : flatten a <;> cases hy : flatten b <;> simp [flatten,hx,hy] at hf
    subst actions
    rw [evalList_append,ih hx]; rfl
  | @seq a p q b result ha hb ia ib =>
    cases hx : flatten a <;> cases hy : flatten b <;> simp [flatten,hx,hy] at hf
    subst actions
    rw [evalList_append,ia hx]; exact ib hy
  | branch_error | branch_yes | branch_no | loop_error | loop_stop | loop_body_error | loop_next =>
    simp [flatten] at hf

/-- Pass result: either the original structured control, or the SAME actions
with clock metadata. This wrapper is not a second operation language. -/
inductive Transformed where
  | original (code : Circuit.Schedule)
  | scheduled (code : Array Action) (plan : Plan)

def transform (s : Circuit.Schedule) (strategy : Array Action → Cycles) : Transformed :=
  match flatten s with
  | none => .original s
  | some actions => .scheduled actions.toArray (compile actions.toArray (strategy actions.toArray))

def Transformed.Eval (cap : Nat → Nat) (p : Payload) (r : Option Payload) : Transformed → Prop
  | .original s => s.Eval cap p r
  | .scheduled code plan => runCycles cap code plan.cycles p = r

theorem transform_correct (h : s.Eval cap p r) (strategy : Array Action → Cycles) :
    (transform s strategy).Eval cap p r := by
  unfold transform
  cases hf : flatten s with
  | none => exact h
  | some actions =>
    change runCycles cap actions.toArray (compile actions.toArray _).cycles p = r
    rw [compile_correct,sourceEval_eq]
    exact flatten_correct h hf

/-- In particular, every existing source-to-control theorem composes with
this pass without re-proving its source semantics. -/
theorem transformed_command_correct (c : HybridIR.Cmd) (b : Build) (i : Expr) (ls : List Expr)
    (p : Payload) (iv xv yv : Int) (lvs : List Int)
    (ctx : Context b.wires.size i ls p iv xv yv lvs)
    (strategy : Array Action → Cycles) :
    ∃ result, (transform (command i ls output c b).1 strategy).Eval cap p result ∧
      result.map (observe output) = bounded (cap output) iv xv yv c p.data (p.queues output) lvs := by
  obtain ⟨result,he,ho⟩ := command_correct c b i ls p iv xv yv lvs ctx
  exact ⟨result,transform_correct he strategy,ho⟩

def sequence : List Circuit.Schedule → Circuit.Schedule
  | [] => .skip
  | s :: ss => .seq s (sequence ss)

/-- Reuse the actual existing command lowerer and fresh-register allocator.
The loop is explicitly instantiated for this first scheduling experiment. -/
def materialize (body : HybridIR.Cmd) (output : Nat) (stride : Int) :
    Nat → Int → Build → List Circuit.Schedule × Build
  | 0,_,b => ([],b)
  | n+1,i,b =>
      let (first,b') := command (.lit i) [] output body b
      let (rest,b'') := materialize body output stride n (i+stride) b'
      (first::rest,b'')

def boundedLoop (body : HybridIR.Cmd) (capacity : Nat) (x y stride : Int) :
    Nat → Int → State × List Int → Option (State × List Int)
  | 0,_,s => some s
  | n+1,i,(s,q) => (bounded capacity i x y body s q []).bind
      (boundedLoop body capacity x y stride n (i+stride))

theorem materialize_correct (body : HybridIR.Cmd) (output : Nat) (stride : Int)
    (count : Nat) (start : Int) (b : Build) (p : Payload) (hb : 2 ≤ b.wires.size) :
    ∃ result, (sequence (materialize body output stride count start b).1).Eval cap p result ∧
      result.map (observe output) = boundedLoop body (cap output) (p.wires 0) (p.wires 1)
        stride count start (p.data,p.queues output) := by
  induction count generalizing start b p with
  | zero => exact ⟨some p,.skip,rfl⟩
  | succ n ih =>
    have ctx : Context b.wires.size (.lit start) [] p start (p.wires 0) (p.wires 1) [] :=
      ⟨hb,.lit,by simp,rfl,rfl,rfl,matches_nil⟩
    obtain ⟨r,hr,ho⟩ := command_correct body b (.lit start) [] p start (p.wires 0) (p.wires 1) [] ctx (output := output) (cap := cap)
    have frame := command_frame body (.lit start) [] output b
    dsimp only [StateT.run] at hr frame
    cases hc : command (.lit start) [] output body b with
    | mk first b' =>
      simp only [hc] at hr frame
      simp only [materialize,hc,sequence]
      cases r with
      | none =>
        refine ⟨none,.seq_error hr,?_⟩
        simp only [boundedLoop,← ho,Option.map_none,Option.bind_none]
      | some q =>
        have below := first.preserves_below hr frame.2 rfl
        have h0 := below 0 (by omega)
        have h1 := below 1 (by omega)
        obtain ⟨r',hr',ho'⟩ := ih (start+stride) b' q (Nat.le_trans hb frame.1)
        refine ⟨r',.seq hr hr',?_⟩
        simpa only [boundedLoop,← ho,Option.map_some,Option.bind_some,observe,← h0,← h1] using ho'

/-- Strategy for arbitrary per-iteration stage counts. Empty iterations do
not inject phantom actions; missing/duplicated actions are still checked. -/
def timedIds (ii : Nat) : List (List Action) → Nat → Nat → List (Nat × Nat)
  | [],_,_ => []
  | actions :: rest,iteration,base =>
      ((List.range actions.length).map (fun k => (base+k,iteration*max 1 ii+k))) ++
        timedIds ii rest (iteration+1) (base+actions.length)

def groupTimes (times : List (Nat × Nat)) : Cycles :=
  let duration := times.foldl (fun bound p => max bound (p.2+1)) 0
  (List.range duration).map (fun t => (times.filter (fun p => p.2 == t)).map Prod.fst)

def iterationProposal (bodies : List Circuit.Schedule) (ii : Nat) : Cycles :=
  match bodies.mapM flatten with
  | none => []
  | some actions => groupTimes (timedIds ii actions 0 0)

def pipelineCommands (body : HybridIR.Cmd) (output : Nat) (stride : Int)
    (count : Nat) (start : Int) (b : Build) (ii : Nat) : Transformed × Build :=
  let (bodies,b') := materialize body output stride count start b
  (transform (sequence bodies) (fun _ => iterationProposal bodies ii),b')

theorem pipelineCommands_correct (body : HybridIR.Cmd) (output : Nat) (stride : Int)
    (count : Nat) (start : Int) (b : Build) (p : Payload) (hb : 2 ≤ b.wires.size) (ii : Nat) :
    ∃ result, (pipelineCommands body output stride count start b ii).1.Eval cap p result ∧
      result.map (observe output) = boundedLoop body (cap output) (p.wires 0) (p.wires 1)
        stride count start (p.data,p.queues output) := by
  obtain ⟨result,he,ho⟩ := materialize_correct body output stride count start b p hb (cap := cap)
  refine ⟨result,?_,ho⟩
  unfold pipelineCommands
  cases hm : materialize body output stride count start b with
  | mk bodies b' =>
    simp only [hm] at he
    exact transform_correct he (fun _ => iterationProposal bodies ii)

def capacityOf (capacities : Array (Nat × Nat)) (q : Nat) : Nat :=
  ((capacities.toList.find? (fun p => p.1 == q)).map Prod.snd).getD 0

/-- Executable result interface. A structured fallback uses the existing
sequential machine; scheduled code uses simultaneous clock updates. `none`
means insufficient fuel, `some none` means program failure. -/
def Transformed.execute (capacities : Array (Nat × Nat)) (fuel : Nat) (p : Payload) :
    Transformed → Option (Option State)
  | .original s => ((s.assemble capacities).run fuel (p.at 1)).result
  | .scheduled code plan =>
      let r := run (capacityOf capacities) code fuel ⟨plan.cycles,some p⟩
      if r.remaining.isEmpty then some (r.payload.map Payload.data) else none

theorem Transformed.finishes (t : Transformed)
    (he : t.Eval (capacityOf capacities) p result) :
    ∃ cycles, t.execute capacities cycles p = some (result.map Payload.data) := by
  cases t with
  | original s => exact s.assemble_finishes p he
  | scheduled code plan =>
    refine ⟨plan.cycles.length,?_⟩
    simp only [Transformed.execute,run_finishes,Option.bind_some,List.isEmpty_nil,ite_true]
    rw [show runCycles (capacityOf capacities) code plan.cycles p = result from he]

end IRComparison.Circuit.Pipelining
