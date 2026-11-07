import IRComparison.Memory.StreamAlternatives
import IRComparison.Memory.AlternativeRouting
import IRComparison.Memory.StreamConsumer

namespace IRComparison.AlternativeFusion
open StreamState StreamConsumer

structure Plan (i : Int) (array size : Nat) (producer : Imperative.Cmd)
    (consumer : List NativeWindowPlan.Block) where
  sender : StreamAlternatives.Compiled i array size [[]] producer
  receiver : AlternativeRouting.Blocks consumer sender.after
  closed : Closed array receiver.code

def compile (i : Int) (array size : Nat) (producer : Imperative.Cmd)
    (consumer : List NativeWindowPlan.Block) : Option (Plan i array size producer consumer) := do
  let sender ← StreamAlternatives.compile i array size [[]] producer
  let receiver ← AlternativeRouting.compile consumer sender.after
  let closed ← checkBlocks array receiver.code
  return ⟨sender,receiver,closed⟩

def Plan.eval (p : Plan i array size producer consumer) (x y : Int) (s : State) : Option State := do
  let (t,q) ← p.sender.code.eval i x y (erase array s) [] []
  (WindowTransport.eval (fun _ => none) x y p.receiver.code [] (erase array t) q).map Prod.fst

def source (i x y : Int) (array : Nat) (producer : Imperative.Cmd)
    (consumer : List NativeWindowPlan.Block) (s : State) : Option State := do
  let t ← producer.eval i x y s []
  NativeWindowPlan.evalI (arrayInput (t.arrays array)) x y consumer [] t

theorem Plan.consume_correct (p : Plan i array size producer consumer)
    (hk : keys ∈ p.sender.after) (h : Related array size keys s t q) :
    (WindowTransport.eval (fun _ => none) x y p.receiver.code [] (erase array t) q).map Prod.fst =
      (NativeWindowPlan.evalI (arrayInput (s.arrays array)) x y consumer [] s).map (erase array) := by
  have same := p.receiver.eval_correct hk h.values [] s x y
  rw [← StreamConsumer.Agree.erase_eq h.agree]
  rw [← p.closed.correct (input:=arrayInput (s.arrays array)) (other:=fun _ => none)]
  simpa only [Option.map_map,Function.comp_def] using congrArg (Option.map (erase array)) same

theorem Plan.correct (p : Plan i array size producer consumer) (s : State)
    (sized : (s.arrays array).size = size) (x y : Int) :
    p.eval x y s = (source i x y array producer consumer s).map (erase array) := by
  have relation : Related array size [] s (erase array s) [] := ⟨erase_agree s,sized,.nil⟩
  have hp := p.sender.correct [] (by simp) s (erase array s) [] x y [] relation
  simp only [Plan.eval,source]
  cases hs : producer.eval i x y s [] <;>
    cases ht : p.sender.code.eval i x y (erase array s) [] [] <;>
    simp only [hs,ht] at hp
  · rfl
  · cases hp
  · cases hp
  · rename_i u pair
    obtain ⟨t,q⟩ := pair
    cases hp with
    | some member hr => exact p.consume_correct member hr

end IRComparison.AlternativeFusion
