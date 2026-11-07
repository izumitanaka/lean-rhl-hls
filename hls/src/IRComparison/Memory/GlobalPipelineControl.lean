import IRComparison.Memory.GlobalPipeline
import IRComparison.Memory.StreamBlocksControl
import IRComparison.Memory.WindowControl

namespace IRComparison.GlobalPipelineControl
open GlobalPipeline StreamConsumer

inductive Config where
  | start (code : List Instruction) (state : State) (queues : Queues)
  | memory (rest : List Instruction) (array : Nat) (queues : Queues) (input : Input) (control : WindowControl.Config)
  | sending (rest : List Instruction) (array output : Nat) (queues : Queues) (input : Input) (control : StreamBlocksControl.Config)
  | stopped (result : Option State)

def step (x y : Int) : Config → Config
  | .start [] s _ => .stopped (some s)
  | .start (c::cs) s qs => match c.mode.eval s qs with
    | none => .stopped none
    | some q => match c.action with
      | .keep code => .memory cs c.input qs (arrayInput (s.arrays c.input)) (.start (WindowControl.lower code) [] s q)
      | .send a code => .sending cs c.input a qs (arrayInput (s.arrays c.input)) (.start code [] (erase a s) q [])
  | .memory _ _ _ _ (.stopped none _) => .stopped none
  | .memory cs a qs _ (.stopped (some s) _) => .start cs s (put qs a [])
  | .memory cs a qs input c@(.start ..) => .memory cs a qs input (WindowControl.step input x y c)
  | .memory cs a qs input c@(.loading ..) => .memory cs a qs input (WindowControl.step input x y c)
  | .memory cs a qs input c@(.body ..) => .memory cs a qs input (WindowControl.step input x y c)
  | .sending _ _ _ _ _ (.stopped none) => .stopped none
  | .sending cs a output qs _ (.stopped (some (s,_,qo))) => .start cs (erase output s) (put (put qs a []) output qo)
  | .sending cs a output qs input c@(.start ..) => .sending cs a output qs input (StreamBlocksControl.step input x y c)
  | .sending cs a output qs input c@(.loading ..) => .sending cs a output qs input (StreamBlocksControl.step input x y c)
  | .sending cs a output qs input c@(.body ..) => .sending cs a output qs input (StreamBlocksControl.step input x y c)
  | .stopped r => .stopped r

inductive Reaches (x y : Int) : Config → Config → Prop where
  | refl (a) : Reaches x y a a
  | next : Reaches x y (step x y a) b → Reaches x y a b

theorem Reaches.trans (h : Reaches x y a b) (k : Reaches x y b c) : Reaches x y a c := by
  induction h with
  | refl => exact k
  | next _ ih => exact .next (ih k)

theorem lift_memory (h : WindowControl.Reaches input x y a b) :
    Reaches x y (.memory rest array qs input a) (.memory rest array qs input b) := by
  induction h with
  | refl => exact .refl _
  | @next a b h ih => cases a with
    | start | loading | body => exact .next ih
    | stopped => simpa [WindowControl.step] using ih

theorem lift_sender (h : StreamBlocksControl.Reaches input x y a b) :
    Reaches x y (.sending rest array output qs input a) (.sending rest array output qs input b) := by
  induction h with
  | refl => exact .refl _
  | @next a b h ih => cases a with
    | start | loading | body => exact .next ih
    | stopped => simpa [StreamBlocksControl.step] using ih

theorem correct (code : List Instruction) (s : State) (qs : Queues) :
    Reaches x y (.start code s qs) (.stopped (execute x y code s qs)) := by
  induction code generalizing s qs with
  | nil => exact .next (.refl _)
  | cons c cs ih =>
    cases hq : c.mode.eval s qs with
    | none =>
      apply Reaches.next
      simpa [step,execute,Instruction.eval,hq] using (Reaches.refl (.stopped none))
    | some q =>
      cases c with
      | mk a mode action =>
        cases action with
        | keep blocks =>
          apply Reaches.next
          simp only [step,hq]
          obtain ⟨errorQueue,h⟩ := WindowControl.lower_correct (input:=arrayInput (s.arrays a)) (x:=x) (y:=y) blocks [] s q
          apply (lift_memory h).trans
          cases he : WindowTransport.eval (arrayInput (s.arrays a)) x y blocks [] s q with
          | none =>
            simpa [execute,Instruction.eval,hq,he,WindowControl.resultEnd] using
              (Reaches.next (Reaches.refl (.stopped none)))
          | some pair =>
            obtain ⟨t,remaining⟩ := pair
            simpa [execute,Instruction.eval,hq,he,WindowControl.resultEnd] using
              (Reaches.next (ih t (put qs a [])))
        | send output blocks =>
          apply Reaches.next
          simp only [step,hq]
          have h := StreamBlocksControl.correct (input:=arrayInput (s.arrays a)) (x:=x) (y:=y) blocks [] (erase output s) q []
          apply (lift_sender h).trans
          cases he : StreamProducerBlocks.eval (arrayInput (s.arrays a)) x y blocks [] (erase output s) q [] with
          | none =>
            simpa [execute,Instruction.eval,hq,he] using (Reaches.next (Reaches.refl (.stopped none)))
          | some triple =>
            obtain ⟨t,remaining,qo⟩ := triple
            simpa [execute,Instruction.eval,hq,he] using
              (Reaches.next (ih (erase output t) (put (put qs a []) output qo)))

def run (x y : Int) : Nat → Config → Config
  | 0,c => c
  | n+1,c => run x y n (step x y c)

theorem Reaches.finite (h : Reaches x y a b) : ∃ n, run x y n a = b := by
  induction h with
  | refl => exact ⟨0,rfl⟩
  | next _ ih => obtain ⟨n,hn⟩ := ih; exact ⟨n+1,hn⟩

theorem program_finishes (p : Program outputs sizes ps) (s : State)
    (layout : PipelineShapes.Layout sizes s) (ready : WindowPipeline.Ready x y ps s) :
    ∃ n result, run x y n (.start p.plan.code s (fun _ => [])) = .stopped result ∧
      result.map (PipelineUse.observe outputs) = (WindowPipeline.source x y ps s).map (PipelineUse.observe outputs) := by
  obtain ⟨n,hn⟩ := (correct (x:=x) (y:=y) p.plan.code s (fun _ => [])).finite
  exact ⟨n,_,hn,p.correct s layout ready⟩

end IRComparison.GlobalPipelineControl
