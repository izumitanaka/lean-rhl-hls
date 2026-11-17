import IRComparison.Hybrid.HybridCompactChainControl
import IRComparison.Hybrid.HybridControl
import IRComparison.Hybrid.HybridRegions
import IRComparison.Hybrid.HybridSymbolicGlobal

namespace IRComparison.HybridUnifiedPipeline
abbrev Kernel := HybridIR.Kernel

def compactStage (k : Kernel) : HybridCompactStage.Stage :=
  (HybridCompactStage.ofSelected (HybridSymbolicLoop.select k.size k.array k.body k.start k.stride k.count)).rebase
    k.source (by intro x y s; exact Source.iterate_congr _ _ (fun i t => k.correct i x y t) k.stride k.count k.start s)

def compactStages (ks : List Kernel) := ks.map compactStage

theorem source_same (ks : List Kernel) (s : State) :
    HybridCompactStage.source x y (compactStages ks) s = HybridIR.source x y ks s := by
  induction ks generalizing s with
  | nil => rfl
  | cons k ks ih =>
    change (k.source x y s).bind (HybridCompactStage.source x y (compactStages ks)) =
      (k.source x y s).bind (HybridIR.source x y ks)
    cases k.source x y s with
    | none => rfl
    | some t => exact ih t

inductive Plan (outputs : List Nat) (sizes : Nat → Nat) : List Kernel → Type where
  | symbolic (plan : HybridSymbolicGlobal.Program outputs sizes (compactStages ks)) : Plan outputs sizes ks
  | regions : Plan outputs sizes ks
  | expanded (plan : HybridIR.Program outputs sizes (HybridIR.stages ks)) : Plan outputs sizes ks
  | compact (plan : HybridCompactChain.Plan outputs sizes (compactStage first) (compactStage second) (compactStages rest)) :
      Plan outputs sizes (first::second::rest)

/-- Apply the same whole-array check as the existing counted chain, directly
    to mixed bodies. No enumeration of source iterations or supplier indices. -/
def compactPolicyBodies (policy : List Nat) : List HybridCompactStage.Stage → Bool
  | [] => true
  | [last] => (HybridCompactStage.check policy last.code.body).isSome
  | stage::following::rest =>
      (HybridCompactStage.check (policy.filter (· != following.array)) stage.code.body).isSome &&
      compactPolicyBodies policy (following::rest)

def compactWholePolicy (ks : List Kernel) : Bool :=
  match compactStages ks with
  | [] => true
  | first::rest =>
    let policy := rest.map (·.array)
    first.array ∉ policy && compactPolicyBodies policy (first::rest)

/-- Per-array rule composition in source order. Every generated loop is counted;
no supplier index list or reference-block expansion is evaluated here. -/
def compile (outputs : List Nat) (sizes : Nat → Nat) (ks : List Kernel) : Option (Plan outputs sizes ks) :=
  match HybridSymbolicGlobal.compile outputs sizes (compactStages ks) with
  | some p => some (.symbolic p)
  | none => some .regions

/-- Memory optimization always has a semantics-preserving memory route. This
is generation totality of this pass only, not of the circuit/RTL backend. -/
theorem compile_total (outputs : List Nat) (sizes : Nat → Nat) (ks : List Kernel) :
    ∃ plan, compile outputs sizes ks = some plan := by
  unfold compile
  split <;> exact ⟨_,rfl⟩

/-- SMT proposes affine receive/discard parameters. Checked rule constructors
certify accepted candidates; unproved policies retain memory. -/
def compileWithSMTCore (outputs : List Nat) (sizes : Nat → Nat) (ks : List Kernel)
    (directory : System.FilePath) : IO (Option (Plan outputs sizes ks)) := do
  match ← HybridSymbolicGlobal.compileWithSMT outputs sizes (compactStages ks) directory with
  | some p => return some (.symbolic p)
  | none => return some .regions

def compileWithSMT (outputs : List Nat) (sizes : Nat → Nat) (ks : List Kernel)
    (directory : System.FilePath) : IO (Option (Plan outputs sizes ks)) := do
  try compileWithSMTCore outputs sizes ks directory
  catch _ => return compile outputs sizes ks

def Plan.eval (p : Plan outputs sizes ks) (x y : Int) (s : State) : Option State :=
  match p with
  | .symbolic code => code.eval x y s
  | .regions => HybridRegions.eval x y (HybridRegions.ofStages (compactStages ks)) s
  | .expanded code => HybridIR.Program.eval code x y s
  | .compact code => code.eval x y s

def Plan.Ready (p : Plan outputs sizes ks) (x y : Int) (s : State) : Prop :=
  match p with
  | .symbolic _ | .regions => ∀ p ∈ compactStages ks, (s.arrays p.array).size = p.size
  | .expanded _ => HybridStage.Ready x y (HybridIR.stages ks) s
  | .compact _ => True

theorem Plan.correct (p : Plan outputs sizes ks) (s : State)
    (layout : PipelineShapes.Layout sizes s) (ready : p.Ready x y s) :
    (p.eval x y s).map (PipelineUse.observe outputs) =
      (HybridIR.source x y ks s).map (PipelineUse.observe outputs) := by
  cases p with
  | symbolic code => exact (code.correct s layout ready).trans (congrArg (Option.map (PipelineUse.observe outputs)) (source_same ks s))
  | regions =>
    have h := (HybridRegions.ofStages_correct (x:=x) (y:=y) (compactStages ks) ready).trans (source_same ks s)
    exact congrArg (Option.map (PipelineUse.observe outputs)) h
  | expanded code => exact HybridIR.kernels_correct code s layout ready
  | @compact first second rest code =>
    simpa only [← source_same,compactStages,List.map_cons] using code.correct s layout

inductive Code where
  | symbolic (code : List HybridSymbolicGlobal.Instruction)
  | regions (code : List HybridRegions.Region)
  | expanded (code : List HybridIR.Instruction)
  | compact (code : HybridCompactChainControl.RootCode)

def lower (p : Plan outputs sizes ks) : Code :=
  match p with
  | .symbolic code => .symbolic code.plan.code
  | .regions => .regions (HybridRegions.ofStages (compactStages ks))
  | .expanded code => .expanded code.code
  | .compact code => .compact (HybridCompactChainControl.lowerRoot code)

inductive Config where
  | symbolic (code : List HybridSymbolicGlobal.Instruction) (state : State)
  | regions (code : List HybridRegions.Region) (state : State)
  | expanded (control : HybridControl.Config)
  | compact (control : HybridCompactChainControl.RootConfig)
  | stopped (result : Option State)

def start (code : Code) (s : State) : Config :=
  match code with
  | .symbolic c => .symbolic c s
  | .regions c => .regions c s
  | .expanded c => .expanded (.start c s (fun _ => []))
  | .compact c => .compact (.start c s)

/-- Abstract plan interpreter. A regions step evaluates a complete structured
region list, not a hardware clock. Actual cycle execution and termination are
proved through `Circuit.regions_pipeline_schedule` and the circuit assembler. -/
def run (x y : Int) (steps : Nat) : Config → Config
  | .stopped r => .stopped r
  | .symbolic c s => if steps = 0 then .symbolic c s else .stopped (HybridSymbolicGlobal.execute x y c s (fun _ => []))
  | .regions c s => if steps = 0 then .regions c s else .stopped (HybridRegions.eval x y c s)
  | .expanded c => match HybridControl.run x y steps c with
      | .stopped r => .stopped r
      | other => .expanded other
  | .compact c => match HybridCompactChainControl.runRoot x y steps c with
      | .stopped r => .stopped r
      | other => .compact other

theorem plan_finishes (p : Plan outputs sizes ks) (s : State)
    (layout : PipelineShapes.Layout sizes s) (ready : p.Ready x y s) :
    ∃ n result, run x y n (start (lower p) s) = .stopped result ∧
      result.map (PipelineUse.observe outputs) =
        (HybridIR.source x y ks s).map (PipelineUse.observe outputs) := by
  cases p with
  | symbolic code =>
    refine ⟨1,code.eval x y s,rfl,?_⟩
    exact (Plan.symbolic code).correct s layout ready
  | regions =>
    refine ⟨1,HybridRegions.eval x y (HybridRegions.ofStages (compactStages ks)) s,rfl,?_⟩
    exact (Plan.regions (ks:=ks) (outputs:=outputs) (sizes:=sizes)).correct s layout ready
  | expanded code =>
    obtain ⟨n,result,hn,hcorrect⟩ := HybridControl.program_finishes (x:=x) (y:=y) code s layout ready
    exact ⟨n,result,by simp [lower,start,run,hn],hcorrect.trans (congrArg (Option.map (PipelineUse.observe outputs)) (HybridIR.stages_source _))⟩
  | @compact first second rest code =>
    obtain ⟨n,result,hn,hcorrect⟩ := HybridCompactChainControl.plan_finishes (x:=x) (y:=y) code s layout
    exact ⟨n,result,by simp [lower,start,run,hn],hcorrect.trans (congrArg (Option.map (PipelineUse.observe outputs)) (source_same (first::second::rest) s))⟩
end IRComparison.HybridUnifiedPipeline
