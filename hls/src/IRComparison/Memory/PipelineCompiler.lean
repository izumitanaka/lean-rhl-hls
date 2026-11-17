import IRComparison.Memory.StreamChain
import IRComparison.Memory.AutoPipeline
import IRComparison.Memory.GlobalPipeline

namespace IRComparison.PipelineCompiler
open WindowPipeline PipelineShapes PipelineUse

inductive Plan (outputs : List Nat) (sizes : Nat → Nat) : List Stage → Type where
  | global (code : GlobalPipeline.Program outputs sizes stages) : Plan outputs sizes stages
  | regions (code : AutoPipeline.Plan outputs sizes stages) : Plan outputs sizes stages
  | chain (code : StreamChain.Plan outputs sizes [] first rest) : Plan outputs sizes (first::rest)

/-- All decisions are made for complete arrays across the entire stage list.
    The conservative fallback performs no channel elimination. -/
def retain (outputs : List Nat) (sizes : Nat → Nat) : (stages : List Stage) → AutoPipeline.Plan outputs sizes stages
  | [] => .nil
  | p::ps => .keep p .globalPolicyUnavailable (retain outputs sizes ps)

def compile (outputs : List Nat) (sizes : Nat → Nat) (stages : List Stage) : Plan outputs sizes stages :=
  match GlobalPipeline.compile outputs sizes stages with
  | some program => .global program
  | none => .regions (retain outputs sizes stages)

def Plan.eval (p : Plan outputs sizes stages) (x y : Int) (s : State) : Option State :=
  match p with
  | .global code => code.eval x y s
  | .regions code => code.eval x y s
  | @Plan.chain _ _ first _ code => do code.eval x y s (← first.queue s)

def Plan.channels : Plan outputs sizes stages → List (Nat × Nat)
  | .global code => code.plan.code.zipIdx.filterMap (fun (c,i) => match c.action with
      | .keep _ => none
      | .send a _ => some (i,a))
  | .regions code => code.channels
  | .chain code => code.channels.zipIdx.map (fun (a,i) => (i,a))

theorem Plan.correct (p : Plan outputs sizes stages) (s : State)
    (layout : Layout sizes s) (ready : Ready x y stages s) :
    (p.eval x y s).map (observe outputs) = (source x y stages s).map (observe outputs) := by
  cases p with
  | global code => exact code.correct s layout ready
  | regions code => exact code.correct s layout ready
  | @chain first rest code =>
    obtain ⟨q,hq,hc⟩ := first.queue_ready s ready.1
    simp only [Plan.eval,hq,bind,Option.bind]
    exact code.correct s layout ready (by simp) hc

theorem compile_correct (outputs : List Nat) (sizes : Nat → Nat) (stages : List Stage)
    (s : State) (layout : Layout sizes s) (ready : Ready x y stages s) :
    ((compile outputs sizes stages).eval x y s).map (observe outputs) =
      (source x y stages s).map (observe outputs) := (compile outputs sizes stages).correct s layout ready

end IRComparison.PipelineCompiler
