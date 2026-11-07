/-! A single-outstanding-request component protocol. This is an abstract
clocked component contract, not a synthesis of an arbitrary Lean function.
Every tick reads the old state; the returned state is committed at the edge.
`extra r + 1` is the number of edges from request acceptance to response valid.
Response data is retained until accepted, independently of further requests. -/
namespace IRComparison.ClockedComponent

inductive State (Request Result : Type) where
  | idle
  | busy (remaining : Nat) (request : Request)
  | response (request : Request) (value : Result)
  deriving DecidableEq, Repr

structure Input (Request : Type) where
  request : Option Request
  responseReady : Bool
  deriving Repr

def ready : State Request Result → Bool
  | .idle => true
  | _ => false

def output : State Request Result → Option Result
  | .response _ value => some value
  | _ => none

def accepted (s : State Request Result) (i : Input Request) : Option Request :=
  if ready s then i.request else none

def retired (s : State Request Result) (i : Input Request) : Option Result :=
  if i.responseReady then output s else none

def tick (effect : Request → Result) (extra : Request → Nat)
    (s : State Request Result) (i : Input Request) : State Request Result :=
  match s with
  | .idle => match i.request with
    | none => .idle
    | some r => .busy (extra r) r
  | .busy 0 r => .response r (effect r)
  | .busy (n+1) r => .busy n r
  | .response r v => if i.responseReady then .idle else .response r v

/-- The abstract effect is evaluated only on completion; its concrete hardware
implementation must separately refine this contract. -/
def WellFormed (effect : Request → Result) : State Request Result → Prop
  | .response r v => v = effect r
  | _ => True

theorem tick_wellFormed (h : WellFormed effect s) :
    WellFormed effect (tick effect extra s i) := by
  cases s with
  | idle => cases hi : i.request <;> simp [tick,hi,WellFormed]
  | busy n r => cases n <;> trivial
  | response r v => cases hi : i.responseReady <;> simp_all [tick, WellFormed]

/-- A full response cannot be overwritten or accepted as a fresh request. -/
theorem response_stall (h : i.responseReady = false) :
    tick effect extra (.response r v) i = .response r v ∧
      accepted (.response r v) i = none ∧ retired (.response r v) i = none := by
  simp [tick, accepted, retired, ready, h]

theorem busy_no_accept : accepted (.busy n r : State Request Result) i = none := rfl

/-- In this initial non-pipelined contract there is no simultaneous retirement
and acceptance. It deliberately makes no throughput claim of one per cycle. -/
theorem retire_once (h : i.responseReady = true) :
    tick effect extra (.response r v) i = .idle ∧
      retired (.response r v) i = some v ∧
      accepted (.response r v) i = none := by
  simp [tick, retired, output, accepted, ready, h]

def pending : State Request Result → List Request
  | .idle => []
  | .busy _ r | .response r _ => [r]

def completed (s : State Request Result) (i : Input Request) : List Request :=
  match s with
  | .response r _ => if i.responseReady then [r] else []
  | _ => []

/-- Every accepted request is either still held or retired exactly once.
The result below is for arbitrary input signals, including request attempts
while busy and arbitrary response backpressure. -/
theorem tick_conservation :
    pending s ++ (accepted s i).toList =
      completed s i ++ pending (tick effect extra s i) := by
  cases s with
  | idle => cases hr : i.request <;> simp [pending,accepted,ready,completed,tick,hr]
  | busy n r => cases n <;> rfl
  | response r v => cases hi : i.responseReady <;>
      simp [pending,accepted,ready,completed,tick,hi]

theorem retired_correct (h : WellFormed effect s) :
    (retired s i).toList = (completed s i).map effect := by
  cases s with
  | idle => cases hi : i.responseReady <;> simp [retired,output,completed,hi]
  | busy => cases hi : i.responseReady <;> simp [retired,output,completed,hi]
  | response r v =>
    change v = effect r at h
    cases hi : i.responseReady <;> simp [retired,output,completed,hi,h]

def run (effect : Request → Result) (extra : Request → Nat) :
    State Request Result → List (Input Request) → State Request Result
  | s, [] => s
  | s, i::is => run effect extra (tick effect extra s i) is

def accepts (effect : Request → Result) (extra : Request → Nat) :
    State Request Result → List (Input Request) → List Request
  | _, [] => []
  | s, i::is => (accepted s i).toList ++ accepts effect extra (tick effect extra s i) is

def completes (effect : Request → Result) (extra : Request → Nat) :
    State Request Result → List (Input Request) → List Request
  | _, [] => []
  | s, i::is => completed s i ++ completes effect extra (tick effect extra s i) is

def results (effect : Request → Result) (extra : Request → Nat) :
    State Request Result → List (Input Request) → List Result
  | _, [] => []
  | s, i::is => (retired s i).toList ++ results effect extra (tick effect extra s i) is

theorem results_correct (is : List (Input Request)) (h : WellFormed effect s) :
    results effect extra s is = (completes effect extra s is).map effect := by
  induction is generalizing s with
  | nil => rfl
  | cons i is ih =>
    simp only [results,completes,List.map_append]
    rw [retired_correct h, ih (tick_wellFormed h)]

theorem run_conservation (is : List (Input Request)) (s : State Request Result) :
    pending s ++ accepts effect extra s is =
      completes effect extra s is ++ pending (run effect extra s is) := by
  induction is generalizing s with
  | nil => simp [run,accepts,completes]
  | cons i is ih =>
    simp only [accepts,completes,run]
    rw [← List.append_assoc, tick_conservation, List.append_assoc, ih, List.append_assoc]

theorem run_wellFormed (is : List (Input Request)) (h : WellFormed effect s) :
    WellFormed effect (run effect extra s is) := by
  induction is generalizing s with
  | nil => exact h
  | cons i is ih => exact ih (tick_wellFormed h)

/-- For every finite signal trace that drains the component, actual response
values are exactly the effects of accepted requests, in order. Attempts made
while not ready do not count as accepted requests. -/
theorem drained_trace_correct (is : List (Input Request))
    (h : run effect extra .idle is = .idle) :
    results effect extra .idle is = (accepts effect extra .idle is).map effect := by
  have hc := run_conservation (effect:=effect) (extra:=extra) is .idle
  simp only [h,pending,List.nil_append,List.append_nil] at hc
  rw [results_correct is (show WellFormed effect .idle from trivial),hc]

/-- Completion does not require responseReady, nor does it accept another
request. A fixed-latency response is buffered rather than lost during a stall. -/
theorem busy_finishes (is : List (Input Request)) (h : is.length = n+1) :
    run effect extra (.busy n r) is = .response r (effect r) := by
  induction n generalizing is with
  | zero =>
    cases is with
    | nil => simp at h
    | cons i is =>
      have he : is = [] := by simpa using h
      subst is
      rfl
  | succ n ih =>
    cases is with
    | nil => simp at h
    | cons i is =>
      exact ih is (by simpa using h)

theorem request_finishes (is : List (Input Request))
    (h : is.length = extra r + 1) :
    run effect extra .idle (⟨some r, ack⟩ :: is) = .response r (effect r) := by
  exact busy_finishes is h

end IRComparison.ClockedComponent
