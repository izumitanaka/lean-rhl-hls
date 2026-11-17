import IRComparison.Core.Execution
import IRComparison.Memory.CompactFusion
import IRComparison.Memory.SymbolicProducerControl
import IRComparison.Memory.CompactFIFOControl
namespace IRComparison.CompactFusionControl
open StreamConsumer

inductive Config where
  | producer (control : SymbolicProducerControl.Config)
  | consumer (control : CompactFIFOControl.Config)
  | stopped (result : Option State)

def step (output : Nat) (producer : SymbolicProducerLoop.Code) (consumer : CompactFIFO.Code)
    (input : Input) (x y : Int) : Config → Config
  | .stopped r => .stopped r
  | .producer (.stopped none) => .stopped none
  | .producer (.stopped (some (s,q))) => .consumer (.start (erase output s) q)
  | .producer c@(.start ..) => .producer (SymbolicProducerControl.step producer input x y c)
  | .producer c@(.loading ..) => .producer (SymbolicProducerControl.step producer input x y c)
  | .producer c@(.ready ..) => .producer (SymbolicProducerControl.step producer input x y c)
  | .producer c@(.body ..) => .producer (SymbolicProducerControl.step producer input x y c)
  | .consumer (.stopped r) => .stopped (r.map Prod.fst)
  | .consumer c@(.start ..) => .consumer (CompactFIFOControl.step consumer x y c)
  | .consumer c@(.loading ..) => .consumer (CompactFIFOControl.step consumer x y c)
  | .consumer c@(.ready ..) => .consumer (CompactFIFOControl.step consumer x y c)
  | .consumer c@(.body ..) => .consumer (CompactFIFOControl.step consumer x y c)

abbrev Reaches (output : Nat) (producer : SymbolicProducerLoop.Code) (consumer : CompactFIFO.Code)
    (input : Input) (x y : Int) : Config → Config → Prop :=
  Execution.Reaches (step output producer consumer input x y)

theorem lift_producer (h : SymbolicProducerControl.Reaches producer input x y a b) :
    Reaches output producer consumer input x y (.producer a) (.producer b) := by
  apply Execution.Reaches.map h (fun a => Config.producer a)
  intro a
  cases a <;> first | exact .next (.refl _) | exact .refl _

theorem lift_consumer (h : CompactFIFOControl.Reaches consumer x y a b) :
    Reaches output producer consumer input x y (.consumer a) (.consumer b) := by
  apply Execution.Reaches.map h (fun a => Config.consumer a)
  intro a
  cases a <;> first | exact .next (.refl _) | exact .refl _

def eval (output : Nat) (producer : SymbolicProducerLoop.Code) (consumer : CompactFIFO.Code)
    (input : Input) (x y : Int) (s : State) : Option State := do
  let (t,q) ← producer.eval input x y s
  (consumer.eval x y (erase output t) q).map Prod.fst

theorem correct (output : Nat) (producer : SymbolicProducerLoop.Code) (consumer : CompactFIFO.Code)
    (s : State) : Reaches output producer consumer input x y (.producer (.start s))
      (.stopped (eval output producer consumer input x y s)) := by
  apply (lift_producer (SymbolicProducerControl.correct (input:=input) (x:=x) (y:=y) producer s)).trans
  simp only [eval]
  cases producer.eval input x y s with
  | none => exact .next (.refl _)
  | some pair =>
    obtain ⟨t,q⟩ := pair
    apply Execution.Reaches.next
    apply (lift_consumer (CompactFIFOControl.correct (x:=x) (y:=y) consumer (erase output t) q)).trans
    exact .next (.refl _)

def run (output : Nat) (producer : SymbolicProducerLoop.Code) (consumer : CompactFIFO.Code)
    (input : Input) (x y : Int) : Nat → Config → Config :=
  Execution.run (step output producer consumer input x y)

theorem plan_finishes (p : CompactFusion.Plan inputArray output size producer consumer) (s : State)
    (sized : (s.arrays output).size = size) :
    ∃ n, run output p.sender.code p.receiver.code (arrayInput ((erase output s).arrays inputArray)) x y n
      (.producer (.start (erase output s))) =
      .stopped ((CompactFusion.source inputArray output producer consumer x y s).map (erase output)) := by
  have h := (correct (input:=arrayInput ((erase output s).arrays inputArray)) (x:=x) (y:=y)
    output p.sender.code p.receiver.code (erase output s)).finite
  change ∃ n, run output p.sender.code p.receiver.code _ x y n _ = .stopped (p.eval x y s) at h
  simpa only [p.correct s sized x y] using h

end IRComparison.CompactFusionControl
