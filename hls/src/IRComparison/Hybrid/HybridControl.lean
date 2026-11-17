import IRComparison.Core.Execution
import IRComparison.Hybrid.HybridBlocksControl
import IRComparison.Hybrid.HybridPipeline
namespace IRComparison.HybridControl
open HybridIR GlobalPipeline StreamConsumer

inductive Config where
  | start (code : List HybridIR.Instruction) (state : State) (queues : Queues)
  | executing (rest : List HybridIR.Instruction) (array : Nat) (output : Option Nat) (queues : Queues)
      (input : Input) (control : HybridBlocksControl.Config)
  | stopped (result : Option State)

def step (x y : Int) : Config → Config
  | .start [] s _ => .stopped (some s)
  | .start (c::cs) s qs => match c.mode.eval s qs with
    | none => .stopped none
    | some q => .executing cs c.input c.output qs (arrayInput (s.arrays c.input))
        (.start c.blocks [] (match c.output with | none => s | some a => erase a s) q [])
  | .executing _ _ _ _ _ (.stopped none) => .stopped none
  | .executing cs a none qs _ (.stopped (some (s,_,_))) => .start cs s (put qs a [])
  | .executing cs a (some output) qs _ (.stopped (some (s,_,qo))) =>
      .start cs (erase output s) (put (put qs a []) output qo)
  | .executing cs a output qs input c@(.start ..) =>
      .executing cs a output qs input (HybridBlocksControl.step input x y c)
  | .executing cs a output qs input c@(.loading ..) =>
      .executing cs a output qs input (HybridBlocksControl.step input x y c)
  | .executing cs a output qs input c@(.body ..) =>
      .executing cs a output qs input (HybridBlocksControl.step input x y c)
  | .stopped r => .stopped r

abbrev Reaches (x y : Int) : Config → Config → Prop :=
  Execution.Reaches (step x y)

theorem lift_blocks (h : HybridBlocksControl.Reaches input x y a b) :
    Reaches x y (.executing rest array output qs input a) (.executing rest array output qs input b) := by
  induction h with
  | refl => exact .refl _
  | @next a b h ih => cases a with
    | start | loading | body => exact .next ih
    | stopped => simpa [HybridBlocksControl.step] using ih

theorem correct (code : List HybridIR.Instruction) (s : State) (qs : Queues) :
    Reaches x y (.start code s qs) (.stopped (HybridIR.execute x y code s qs)) := by
  induction code generalizing s qs with
  | nil => exact .next (.refl _)
  | cons c cs ih =>
    cases hq : c.mode.eval s qs with
    | none =>
      apply Execution.Reaches.next
      simpa [step,HybridIR.execute,HybridIR.Instruction.eval,hq] using (Execution.Reaches.refl (Config.stopped none))
    | some q =>
      apply Execution.Reaches.next
      simp only [step,hq]
      let initial := match c.output with | none => s | some a => erase a s
      apply (lift_blocks (HybridBlocksControl.correct (input:=arrayInput (s.arrays c.input))
        (x:=x) (y:=y) c.blocks [] initial q [])).trans
      cases he : blocksEval (arrayInput (s.arrays c.input)) x y c.blocks [] initial q [] with
      | none =>
        cases ho : c.output <;> simp only [initial,ho] at he <;>
          simp only [HybridIR.execute,HybridIR.Instruction.eval,hq,bind,Option.bind,ho,he] <;>
          exact .next (.refl _)
      | some triple =>
        obtain ⟨t,remaining,qo⟩ := triple
        cases ho : c.output with
        | none =>
          simp only [initial,ho] at he
          simp only [HybridIR.execute,HybridIR.Instruction.eval,hq,bind,Option.bind,ho,he]
          exact .next (ih t (put qs c.input []))
        | some a =>
          simp only [initial,ho] at he
          simp only [HybridIR.execute,HybridIR.Instruction.eval,hq,bind,Option.bind,ho,he]
          exact .next (ih (erase a t) (put (put qs c.input []) a qo))

def run (x y : Int) : Nat → Config → Config :=
  Execution.run (step x y)

theorem program_finishes (p : HybridIR.Program outputs sizes ps) (s : State)
    (layout : PipelineShapes.Layout sizes s) (ready : HybridStage.Ready x y ps s) :
    ∃ n result, run x y n (.start p.code s (fun _ => [])) = .stopped result ∧
      result.map (PipelineUse.observe outputs) = (HybridStage.source x y ps s).map (PipelineUse.observe outputs) := by
  obtain ⟨n,hn⟩ := (correct (x:=x) (y:=y) p.code s (fun _ => [])).finite
  exact ⟨n,_,hn,HybridIR.Program.correct p s layout ready⟩

end IRComparison.HybridControl
