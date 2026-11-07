import IRComparison.Components.ClockedComponent

/-! The initial sequential controller for one component operation. Controller
and component both read the pre-edge state and commit together. A response
created at an edge is observed by the controller on the following cycle.
This is a reusable operation boundary, not a whole-program backend. -/
namespace IRComparison.ClockedOperation
open ClockedComponent

inductive Control (Request Result : Type) where
  | offer (request : Request)
  | awaiting
  | done (value : Result)
  deriving DecidableEq, Repr

structure Machine (Request Result : Type) where
  control : Control Request Result
  component : ClockedComponent.State Request Result
  deriving DecidableEq, Repr

def signals : Control Request Result → ClockedComponent.Input Request
  | .offer r => ⟨some r,false⟩
  | .awaiting => ⟨none,true⟩
  | .done _ => ⟨none,false⟩

def advance (c : Control Request Result) (s : ClockedComponent.State Request Result) :
    Control Request Result :=
  match c with
  | .offer r => if ready s then .awaiting else .offer r
  | .awaiting => match output s with
    | none => .awaiting
    | some v => .done v
  | .done v => .done v

def tick (effect : Request → Result) (extra : Request → Nat) (m : Machine Request Result) :
    Machine Request Result :=
  ⟨advance m.control m.component,
    ClockedComponent.tick effect extra m.component (signals m.control)⟩

def start (r : Request) : Machine Request Result := ⟨.offer r,.idle⟩
def stop (v : Result) : Machine Request Result := ⟨.done v,.idle⟩

def run (effect : Request → Result) (extra : Request → Nat) :
    Nat → Machine Request Result → Machine Request Result
  | 0,m => m
  | n+1,m => run effect extra n (tick effect extra m)

theorem stop_stable (effect : Request → Result) (extra : Request → Nat) (v : Result) :
    tick effect extra (stop v : Machine Request Result) = stop v := rfl

theorem await_finishes (n : Nat) :
    run effect extra (n+2) ⟨.awaiting,.busy n r⟩ = stop (effect r) := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

/-- Acceptance, L completion cycles, then response capture: L+2 edges total.
Here L=extra r+1. This count is for the abstract latency contract only. -/
theorem finishes (r : Request) :
    run effect extra (extra r + 3) (start r) = stop (effect r) := by
  exact await_finishes (extra r)

theorem offer_preserves (h : ready s = false) :
    advance (.offer r) s = .offer r := by simp [advance,h]

theorem awaiting_does_not_issue :
    (signals (.awaiting : Control Request Result)).request = none := rfl

end IRComparison.ClockedOperation
