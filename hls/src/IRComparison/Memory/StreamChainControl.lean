import IRComparison.Core.Execution
import IRComparison.Memory.StreamChain
import IRComparison.Memory.StreamBlocksControl
import IRComparison.Memory.WindowControl
namespace IRComparison.StreamChainControl
open StreamConsumer

inductive Code where
  | finish (consumer : List WindowTransport.Block)
  | stage (inputArray output : Nat) (sender : List StreamProducerBlocks.Block) (tail : Code)

def lower (p : StreamChain.Plan outputs sizes hidden stage rest) : Code :=
  match p with
  | .last .. => .finish stage.code
  | @StreamChain.Plan.next _ _ _ stage following _ emit _ _ _ tail =>
      .stage stage.array following.array emit.sender.code (lower tail)

def Code.eval (code : Code) (x y : Int) (s : State) (q : List Int) : Option State :=
  match code with
  | .finish blocks => (WindowTransport.eval (fun _ => none) x y blocks [] s q).map Prod.fst
  | .stage input a blocks tail => do
      let (t,_,qo) ← StreamProducerBlocks.eval (arrayInput (s.arrays input)) x y blocks [] (erase a s) q []
      tail.eval x y (erase a t) qo

theorem lower_correct (p : StreamChain.Plan outputs sizes hidden stage rest) :
    (lower p).eval x y s q = p.eval x y s q := by
  induction p generalizing s q with
  | last => rfl
  | next emit order sizeOK privateOutput tail ih =>
    simp only [lower,Code.eval,StreamChain.Plan.eval,StreamChainEmit.Plan.eval]
    cases StreamProducerBlocks.eval (arrayInput (s.arrays _)) x y emit.sender.code [] (erase _ s) q [] with
    | none => rfl
    | some triple => obtain ⟨t,qi,qo⟩ := triple; exact ih

inductive Config where
  | start (code : Code) (state : State) (queue : List Int)
  | sending (input : Input) (output : Nat) (tail : Code) (control : StreamBlocksControl.Config)
  | finishing (control : WindowControl.Config)
  | stopped (result : Option State)

def step (x y : Int) : Config → Config
  | .stopped r => .stopped r
  | .start (.finish blocks) s q => .finishing (.start (WindowControl.lower blocks) [] s q)
  | .start (.stage input a blocks tail) s q => .sending (arrayInput (s.arrays input)) a tail (.start blocks [] (erase a s) q [])
  | .sending _ _ _ (.stopped none) => .stopped none
  | .sending _ a tail (.stopped (some (s,_,qo))) => .start tail (erase a s) qo
  | .sending input a tail c@(.start ..) => .sending input a tail (StreamBlocksControl.step input x y c)
  | .sending input a tail c@(.loading ..) => .sending input a tail (StreamBlocksControl.step input x y c)
  | .sending input a tail c@(.body ..) => .sending input a tail (StreamBlocksControl.step input x y c)
  | .finishing (.stopped r _) => .stopped r
  | .finishing c@(.start ..) => .finishing (WindowControl.step (fun _ => none) x y c)
  | .finishing c@(.loading ..) => .finishing (WindowControl.step (fun _ => none) x y c)
  | .finishing c@(.body ..) => .finishing (WindowControl.step (fun _ => none) x y c)

abbrev Reaches (x y : Int) : Config → Config → Prop :=
  Execution.Reaches (step x y)

theorem lift_sender (h : StreamBlocksControl.Reaches input x y a b) :
    Reaches x y (.sending input output tail a) (.sending input output tail b) := by
  apply Execution.Reaches.map h (fun a => Config.sending input output tail a)
  intro a
  cases a <;> first | exact .next (.refl _) | exact .refl _

theorem lift_finisher (h : WindowControl.Reaches (fun _ => none) x y a b) :
    Reaches x y (.finishing a) (.finishing b) := by
  apply Execution.Reaches.map h (fun a => Config.finishing a)
  intro a
  cases a <;> first | exact .next (.refl _) | exact .refl _

theorem correct (code : Code) (s : State) (q : List Int) :
    Reaches x y (.start code s q) (.stopped (code.eval x y s q)) := by
  induction code generalizing s q with
  | finish blocks =>
    apply Execution.Reaches.next
    obtain ⟨failed,h⟩ := WindowControl.lower_correct (input:=fun _ => none) (x:=x) (y:=y) blocks [] s q
    apply (lift_finisher h).trans
    simp only [Code.eval]
    cases WindowTransport.eval (fun _ => none) x y blocks [] s q with
    | none => exact .next (.refl _)
    | some pair => obtain ⟨t,qs⟩ := pair; exact .next (.refl _)
  | stage input a blocks tail ih =>
    apply Execution.Reaches.next
    have h := StreamBlocksControl.correct (input:=arrayInput (s.arrays input)) (x:=x) (y:=y) blocks [] (erase a s) q []
    apply (lift_sender h).trans
    simp only [Code.eval]
    cases StreamProducerBlocks.eval (arrayInput (s.arrays input)) x y blocks [] (erase a s) q [] with
    | none => exact .next (.refl _)
    | some triple => obtain ⟨t,qi,qo⟩ := triple; exact .next (ih (erase a t) qo)

def run (x y : Int) : Nat → Config → Config :=
  Execution.run (step x y)

theorem plan_finishes (p : StreamChain.Plan outputs sizes hidden stage rest) (s : State) (q : List Int) :
    ∃ n, run x y n (.start (lower p) s q) = .stopped (p.eval x y s q) := by
  simpa only [lower_correct] using (correct (x:=x) (y:=y) (lower p) s q).finite

end IRComparison.StreamChainControl
