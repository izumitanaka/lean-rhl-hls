import IRComparison.Memory.GlobalPipelineControl
import IRComparison.Memory.PipelineCompiler
import IRComparison.Memory.StreamChainControl
import IRComparison.Memory.AutoPipelineControl

namespace IRComparison.PipelineCompilerControl

inductive Code where
  | global (code : List GlobalPipeline.Instruction)
  | regions (code : List AutoPipelineControl.Region)
  | chain (inputArray : Nat) (order : List Int) (fifo : Bool) (code : StreamChainControl.Code)

def lower (p : PipelineCompiler.Plan outputs sizes stages) : Code :=
  match p with
  | .global code => .global code.plan.code
  | .regions code => .regions (AutoPipelineControl.lower code)
  | @PipelineCompiler.Plan.chain _ _ first _ code =>
      .chain first.array first.producer first.fifo (StreamChainControl.lower code)

def Code.eval (code : Code) (x y : Int) (s : State) : Option State :=
  match code with
  | .global code => GlobalPipeline.execute x y code s (fun _ => [])
  | .regions rs => AutoPipelineControl.eval x y rs s
  | .chain a order fifo body => do
      body.eval x y s (← AutoPipelineControl.queue a order fifo s)

theorem lower_correct (p : PipelineCompiler.Plan outputs sizes stages) :
    (lower p).eval x y s = p.eval x y s := by
  cases p with
  | global code => rfl
  | regions code => exact AutoPipelineControl.lower_correct code
  | @chain first rest code =>
    simp only [lower,Code.eval,PipelineCompiler.Plan.eval]
    change (first.queue s).bind ((StreamChainControl.lower code).eval x y s) =
      (first.queue s).bind (code.eval x y s)
    cases first.queue s with
    | none => rfl
    | some q => exact StreamChainControl.lower_correct code

inductive Config where
  | start (code : Code) (state : State)
  | global (control : GlobalPipelineControl.Config)
  | regions (control : AutoPipelineControl.Config)
  | chain (control : StreamChainControl.Config)
  | stopped (result : Option State)

def step (x y : Int) : Config → Config
  | .start (.global code) s => .global (.start code s (fun _ => []))
  | .global (.stopped r) => .stopped r
  | .global c@(.start ..) => .global (GlobalPipelineControl.step x y c)
  | .global c@(.memory ..) => .global (GlobalPipelineControl.step x y c)
  | .global c@(.sending ..) => .global (GlobalPipelineControl.step x y c)
  | .start (.regions code) s => .regions (.start code s)
  | .start (.chain a order fifo code) s => match AutoPipelineControl.queue a order fifo s with
      | none => .stopped none
      | some q => .chain (.start code s q)
  | .regions (.stopped r) => .stopped r
  | .regions c@(.start ..) => .regions (AutoPipelineControl.step x y c)
  | .regions c@(.memory ..) => .regions (AutoPipelineControl.step x y c)
  | .regions c@(.stream ..) => .regions (AutoPipelineControl.step x y c)
  | .chain (.stopped r) => .stopped r
  | .chain c@(.start ..) => .chain (StreamChainControl.step x y c)
  | .chain c@(.sending ..) => .chain (StreamChainControl.step x y c)
  | .chain c@(.finishing ..) => .chain (StreamChainControl.step x y c)
  | .stopped r => .stopped r

inductive Reaches (x y : Int) : Config → Config → Prop where
  | refl (a) : Reaches x y a a
  | next : Reaches x y (step x y a) b → Reaches x y a b

theorem Reaches.trans (h : Reaches x y a b) (g : Reaches x y b c) : Reaches x y a c := by
  induction h with
  | refl => exact g
  | next _ ih => exact .next (ih g)

theorem lift_regions (h : AutoPipelineControl.Reaches x y a b) : Reaches x y (.regions a) (.regions b) := by
  induction h with
  | refl => exact .refl _
  | @next a b h ih => cases a with
    | start | memory | stream => exact .next ih
    | stopped => simpa [AutoPipelineControl.step] using ih

theorem lift_chain (h : StreamChainControl.Reaches x y a b) : Reaches x y (.chain a) (.chain b) := by
  induction h with
  | refl => exact .refl _
  | @next a b h ih => cases a with
    | start | sending | finishing => exact .next ih
    | stopped => simpa [StreamChainControl.step] using ih

theorem lift_global (h : GlobalPipelineControl.Reaches x y a b) : Reaches x y (.global a) (.global b) := by
  induction h with
  | refl => exact .refl _
  | @next a b h ih => cases a with
    | start | memory | sending => exact .next ih
    | stopped => simpa [GlobalPipelineControl.step] using ih

theorem correct (code : Code) (s : State) : Reaches x y (.start code s) (.stopped (code.eval x y s)) := by
  cases code with
  | global code =>
    apply Reaches.next
    apply (lift_global (GlobalPipelineControl.correct code s (fun _ => []))).trans
    exact .next (.refl _)
  | regions rs =>
    apply Reaches.next
    apply (lift_regions (AutoPipelineControl.correct rs s)).trans
    exact .next (.refl _)
  | chain a order fifo code =>
    apply Reaches.next
    simp only [step,Code.eval]
    cases AutoPipelineControl.queue a order fifo s with
    | none => exact .refl _
    | some q =>
      apply (lift_chain (StreamChainControl.correct code s q)).trans
      exact .next (.refl _)

def run (x y : Int) : Nat → Config → Config
  | 0,c => c
  | n+1,c => run x y n (step x y c)

theorem Reaches.finite (h : Reaches x y a b) : ∃ n, run x y n a = b := by
  induction h with
  | refl => exact ⟨0,rfl⟩
  | next _ ih => obtain ⟨n,hn⟩ := ih; exact ⟨n+1,hn⟩

theorem compile_finishes (outputs : List Nat) (sizes : Nat → Nat) (stages : List WindowPipeline.Stage)
    (s : State) (layout : PipelineShapes.Layout sizes s) (ready : WindowPipeline.Ready x y stages s) :
    ∃ n result, run x y n (.start (lower (PipelineCompiler.compile outputs sizes stages)) s) = .stopped result ∧
      result.map (PipelineUse.observe outputs) = (WindowPipeline.source x y stages s).map (PipelineUse.observe outputs) := by
  obtain ⟨n,hn⟩ := (correct (x:=x) (y:=y) (lower (PipelineCompiler.compile outputs sizes stages)) s).finite
  rw [lower_correct] at hn
  exact ⟨n,_,hn,PipelineCompiler.compile_correct outputs sizes stages s layout ready⟩

end IRComparison.PipelineCompilerControl
