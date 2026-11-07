import IRComparison.Hybrid.HybridCompactChainControl
import IRComparison.Hybrid.HybridControl

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

def compile (outputs : List Nat) (sizes : Nat → Nat) (ks : List Kernel) : Option (Plan outputs sizes ks) :=
  match ks with
  | first::second::rest =>
    match (if compactWholePolicy ks then HybridCompactChain.compile outputs sizes (compactStage first) (compactStage second) (compactStages rest) else none) with
    | some p => some (.compact p)
    | none => (HybridIR.compileKernels outputs sizes (first::second::rest)).map Plan.expanded
  | other => (HybridIR.compileKernels outputs sizes other).map Plan.expanded

/-- SAT models are rechecked by CompactSequence; other answers do not certify
    a candidate. IO failures use the independently proved static compiler. -/
def compileWithSMTCore (outputs : List Nat) (sizes : Nat → Nat) (ks : List Kernel)
    (directory : System.FilePath) : IO (Option (Plan outputs sizes ks)) := do
  match ks with
  | first::second::rest =>
    match ← (if compactWholePolicy ks then
        HybridCompactChain.compileWithSMT outputs sizes (compactStage first) (compactStage second) (compactStages rest) directory
        else pure none) with
    | some p => return some (.compact p)
    | none => return compile outputs sizes (first::second::rest)
  | other => return compile outputs sizes other

def compileWithSMT (outputs : List Nat) (sizes : Nat → Nat) (ks : List Kernel)
    (directory : System.FilePath) : IO (Option (Plan outputs sizes ks)) := do
  try compileWithSMTCore outputs sizes ks directory
  catch _ => return compile outputs sizes ks

def Plan.eval (p : Plan outputs sizes ks) (x y : Int) (s : State) : Option State :=
  match p with
  | .expanded code => HybridIR.Program.eval code x y s
  | .compact code => code.eval x y s

def Plan.Ready (p : Plan outputs sizes ks) (x y : Int) (s : State) : Prop :=
  match p with
  | .expanded _ => HybridStage.Ready x y (HybridIR.stages ks) s
  | .compact _ => True

theorem Plan.correct (p : Plan outputs sizes ks) (s : State)
    (layout : PipelineShapes.Layout sizes s) (ready : p.Ready x y s) :
    (p.eval x y s).map (PipelineUse.observe outputs) =
      (HybridIR.source x y ks s).map (PipelineUse.observe outputs) := by
  cases p with
  | expanded code => exact HybridIR.kernels_correct code s layout ready
  | @compact first second rest code =>
    simpa only [← source_same,compactStages,List.map_cons] using code.correct s layout

inductive Code where
  | expanded (code : List HybridIR.Instruction)
  | compact (code : HybridCompactChainControl.RootCode)

def lower (p : Plan outputs sizes ks) : Code :=
  match p with
  | .expanded code => .expanded code.code
  | .compact code => .compact (HybridCompactChainControl.lowerRoot code)

inductive Config where
  | expanded (control : HybridControl.Config)
  | compact (control : HybridCompactChainControl.RootConfig)
  | stopped (result : Option State)

def start (code : Code) (s : State) : Config :=
  match code with
  | .expanded c => .expanded (.start c s (fun _ => []))
  | .compact c => .compact (.start c s)

def run (x y : Int) (steps : Nat) : Config → Config
  | .stopped r => .stopped r
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
  | expanded code =>
    obtain ⟨n,result,hn,hcorrect⟩ := HybridControl.program_finishes (x:=x) (y:=y) code s layout ready
    exact ⟨n,result,by simp [lower,start,run,hn],hcorrect.trans (congrArg (Option.map (PipelineUse.observe outputs)) (HybridIR.stages_source _))⟩
  | @compact first second rest code =>
    obtain ⟨n,result,hn,hcorrect⟩ := HybridCompactChainControl.plan_finishes (x:=x) (y:=y) code s layout
    exact ⟨n,result,by simp [lower,start,run,hn],hcorrect.trans (congrArg (Option.map (PipelineUse.observe outputs)) (source_same (first::second::rest) s))⟩
end IRComparison.HybridUnifiedPipeline
