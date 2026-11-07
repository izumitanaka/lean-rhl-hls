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

inductive Reaches (x y : Int) : Config → Config → Prop where
  | refl (a) : Reaches x y a a
  | next : Reaches x y (step x y a) b → Reaches x y a b

theorem Reaches.trans (h : Reaches x y a b) (k : Reaches x y b c) : Reaches x y a c := by
  induction h with
  | refl => exact k
  | next _ ih => exact .next (ih k)

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
      apply Reaches.next
      simpa [step,HybridIR.execute,HybridIR.Instruction.eval,hq] using (Reaches.refl (.stopped none))
    | some q =>
      apply Reaches.next
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

def run (x y : Int) : Nat → Config → Config
  | 0,c => c
  | n+1,c => run x y n (step x y c)

theorem Reaches.finite (h : Reaches x y a b) : ∃ n, run x y n a = b := by
  induction h with
  | refl => exact ⟨0,rfl⟩
  | next _ ih => obtain ⟨n,hn⟩ := ih; exact ⟨n+1,hn⟩

theorem program_finishes (p : HybridIR.Program outputs sizes ps) (s : State)
    (layout : PipelineShapes.Layout sizes s) (ready : HybridStage.Ready x y ps s) :
    ∃ n result, run x y n (.start p.code s (fun _ => [])) = .stopped result ∧
      result.map (PipelineUse.observe outputs) = (HybridStage.source x y ps s).map (PipelineUse.observe outputs) := by
  obtain ⟨n,hn⟩ := (correct (x:=x) (y:=y) p.code s (fun _ => [])).finite
  exact ⟨n,_,hn,HybridIR.Program.correct p s layout ready⟩

end IRComparison.HybridControl
