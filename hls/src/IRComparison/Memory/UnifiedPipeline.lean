import IRComparison.Memory.CompactChainControl
import IRComparison.Memory.PipelineCompilerControl

namespace IRComparison.UnifiedPipeline

/-- The expanded alternative is lazy. Constructing a large counted kernel
    must not enumerate its iterations or supplier indices in advance. -/
structure Kernel where
  compact : CompactStage.Stage
  expanded : Unit → WindowPipeline.Stage
  same : ∀ x y s, (expanded ()).source x y s = compact.source x y s

def compactStages (ks : List Kernel) := ks.map Kernel.compact
def expandedStages (ks : List Kernel) := ks.map (fun k => k.expanded ())

theorem source_same (ks : List Kernel) (s : State) :
    WindowPipeline.source x y (expandedStages ks) s = CompactStage.source x y (compactStages ks) s := by
  induction ks generalizing s with
  | nil => rfl
  | cons k ks ih =>
    simp only [expandedStages,compactStages,List.map_cons,WindowPipeline.source,CompactStage.source,k.same]
    cases k.compact.source x y s with
    | none => rfl
    | some t => exact ih t

inductive Plan (outputs : List Nat) (sizes : Nat → Nat) : List Kernel → Type where
  | expanded (plan : PipelineCompiler.Plan outputs sizes (expandedStages ks)) : Plan outputs sizes ks
  | compact (plan : CompactChain.Plan outputs sizes first.compact second.compact (compactStages rest)) :
      Plan outputs sizes (first::second::rest)

/-- Before the compact fast path, check the same whole-array policy against
    all bodies, including accesses preceding a channel's producer. -/
def compactPolicyBodies (policy : List Nat) : List CompactStage.Stage → Bool
  | [] => true
  | [last] => (CompactStage.check policy last.code.body).isSome
  | stage::following::rest =>
      (CompactStage.check (policy.filter (· != following.array)) stage.code.body).isSome &&
      compactPolicyBodies policy (following::rest)

def compactWholePolicy (ks : List Kernel) : Bool :=
  match compactStages ks with
  | [] => true
  | first::rest =>
    let policy := rest.map (·.array)
    first.array ∉ policy && compactPolicyBodies policy (first::rest)

def compile (outputs : List Nat) (sizes : Nat → Nat) (ks : List Kernel) : Plan outputs sizes ks :=
  match ks with
  | first::second::rest =>
    match (if compactWholePolicy ks then CompactChain.compile outputs sizes first.compact second.compact (compactStages rest) else none) with
    | some p => .compact p
    | none => .expanded (PipelineCompiler.compile outputs sizes (expandedStages (first::second::rest)))
  | other => .expanded (PipelineCompiler.compile outputs sizes (expandedStages other))

/-- Solver failure never supplies a proof. The fallback can still perform
    independently checked static transformations. -/
def compileWithSMT (outputs : List Nat) (sizes : Nat → Nat) (ks : List Kernel)
    (directory : System.FilePath) : IO (Plan outputs sizes ks) := do
  match ks with
  | first::second::rest =>
    match ← (if compactWholePolicy ks then CompactChain.compileWithSMT outputs sizes first.compact second.compact (compactStages rest) directory else pure none) with
    | some p => return .compact p
    | none => return .expanded (PipelineCompiler.compile outputs sizes (expandedStages (first::second::rest)))
  | other => return .expanded (PipelineCompiler.compile outputs sizes (expandedStages other))

def Plan.eval (p : Plan outputs sizes ks) (x y : Int) (s : State) : Option State :=
  match p with
  | .expanded code => code.eval x y s
  | .compact code => code.eval x y s

/-- Expanded-path readiness is needed only if that path was selected. It is
    a proposition and does not force an expanded fallback during execution. -/
def Plan.Ready (p : Plan outputs sizes ks) (x y : Int) (s : State) : Prop :=
  match p with
  | .expanded _ => WindowPipeline.Ready x y (expandedStages ks) s
  | .compact _ => True

theorem Plan.correct (p : Plan outputs sizes ks) (s : State)
    (layout : PipelineShapes.Layout sizes s) (ready : p.Ready x y s) :
    (p.eval x y s).map (PipelineUse.observe outputs) =
      (CompactStage.source x y (compactStages ks) s).map (PipelineUse.observe outputs) := by
  cases p with
  | expanded code => rw [Plan.eval,code.correct s layout ready,source_same]
  | compact code => exact code.correct s layout

inductive Code where
  | expanded (code : PipelineCompilerControl.Code)
  | compact (code : CompactChainControl.RootCode)

def lower (p : Plan outputs sizes ks) : Code :=
  match p with
  | .expanded code => .expanded (PipelineCompilerControl.lower code)
  | .compact code => .compact (CompactChainControl.lowerRoot code)

inductive Config where
  | expanded (control : PipelineCompilerControl.Config)
  | compact (control : CompactChainControl.RootConfig)
  | stopped (result : Option State)

def start (code : Code) (s : State) : Config :=
  match code with
  | .expanded c => .expanded (.start c s)
  | .compact c => .compact (.start c s)

def run (x y : Int) (steps : Nat) : Config → Config
  | .stopped r => .stopped r
  | .expanded c => match PipelineCompilerControl.run x y steps c with
      | .stopped r => .stopped r
      | other => .expanded other
  | .compact c => match CompactChainControl.runRoot x y steps c with
      | .stopped r => .stopped r
      | other => .compact other

theorem plan_finishes (p : Plan outputs sizes ks) (s : State)
    (layout : PipelineShapes.Layout sizes s) (ready : p.Ready x y s) :
    ∃ n result, run x y n (start (lower p) s) = .stopped result ∧
      result.map (PipelineUse.observe outputs) =
        (CompactStage.source x y (compactStages ks) s).map (PipelineUse.observe outputs) := by
  cases p with
  | expanded code =>
    obtain ⟨n,hn⟩ := (PipelineCompilerControl.correct (x:=x) (y:=y) (PipelineCompilerControl.lower code) s).finite
    rw [PipelineCompilerControl.lower_correct] at hn
    exact ⟨n,code.eval x y s,by simp [lower,start,run,hn],by rw [code.correct s layout ready,source_same]⟩
  | compact code =>
    obtain ⟨n,result,hn,correct⟩ := CompactChainControl.plan_finishes (x:=x) (y:=y) code s layout
    exact ⟨n,result,by simp [lower,start,run,hn],correct⟩

end IRComparison.UnifiedPipeline
