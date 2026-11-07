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

inductive Reaches (output : Nat) (producer : SymbolicProducerLoop.Code) (consumer : CompactFIFO.Code)
    (input : Input) (x y : Int) : Config → Config → Prop where
  | refl (a) : Reaches output producer consumer input x y a a
  | next : Reaches output producer consumer input x y (step output producer consumer input x y a) b →
      Reaches output producer consumer input x y a b

theorem Reaches.trans (h : Reaches output producer consumer input x y a b)
    (g : Reaches output producer consumer input x y b c) : Reaches output producer consumer input x y a c := by
  induction h with
  | refl => exact g
  | next _ ih => exact .next (ih g)

theorem lift_producer (h : SymbolicProducerControl.Reaches producer input x y a b) :
    Reaches output producer consumer input x y (.producer a) (.producer b) := by
  induction h with
  | refl => exact .refl _
  | @next a b h ih => cases a with
    | start | loading | ready | body => exact .next ih
    | stopped => simpa [SymbolicProducerControl.step] using ih

theorem lift_consumer (h : CompactFIFOControl.Reaches consumer x y a b) :
    Reaches output producer consumer input x y (.consumer a) (.consumer b) := by
  induction h with
  | refl => exact .refl _
  | @next a b h ih => cases a with
    | start | loading | ready | body => exact .next ih
    | stopped => simpa [CompactFIFOControl.step] using ih

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
    apply Reaches.next
    apply (lift_consumer (CompactFIFOControl.correct (x:=x) (y:=y) consumer (erase output t) q)).trans
    exact .next (.refl _)

def run (output : Nat) (producer : SymbolicProducerLoop.Code) (consumer : CompactFIFO.Code)
    (input : Input) (x y : Int) : Nat → Config → Config
  | 0,c => c
  | n+1,c => run output producer consumer input x y n (step output producer consumer input x y c)

theorem Reaches.finite (h : Reaches output producer consumer input x y a b) :
    ∃ n, run output producer consumer input x y n a = b := by
  induction h with
  | refl => exact ⟨0,rfl⟩
  | next _ ih => obtain ⟨n,hn⟩ := ih; exact ⟨n+1,hn⟩

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
