import IRComparison.Hybrid.HybridCompactChain
import IRComparison.Hybrid.HybridCompactDuplexControl
import IRComparison.Hybrid.HybridSymbolicProducerControl
import IRComparison.Hybrid.HybridCompactFIFOControl

namespace IRComparison.HybridCompactChainControl
open StreamConsumer

inductive Code where
  | finish (receiver : HybridCompactFIFO.Code)
  | stage (output : Nat) (sender : HybridCompactDuplex.Code) (tail : Code)

def lower (p : HybridCompactChain.Tail outputs sizes hidden stage rest supplier) : Code :=
  match p with
  | .last _ receiver _ => .finish receiver.code
  | @HybridCompactChain.Tail.next _ _ _ _ _ following _ _ emit _ _ tail =>
      .stage following.array emit.duplex.code (lower tail)

def Code.eval (code : Code) (x y : Int) (s : State) (q : List Int) : Option State :=
  match code with
  | .finish receiver => (receiver.eval x y s q).map Prod.fst
  | .stage a sender tail => do
      let (t,qo) ← sender.eval x y (erase a s) q
      tail.eval x y (erase a t) qo

theorem lower_correct (p : HybridCompactChain.Tail outputs sizes hidden stage rest supplier) :
    (lower p).eval x y s q = p.eval x y s q := by
  induction p generalizing s q with
  | last => rfl
  | next sizeOK emit outputSize privateOutput tail ih =>
    simp only [lower,Code.eval,HybridCompactChain.Tail.eval,HybridCompactChainEmit.Plan.eval]
    cases emit.duplex.code.eval x y (erase _ s) q with
    | none => rfl
    | some pair => obtain ⟨t,qo⟩ := pair; exact ih

inductive Config where
  | start (code : Code) (state : State) (queue : List Int)
  | sending (output : Nat) (sender : HybridCompactDuplex.Code) (tail : Code) (control : HybridCompactDuplexControl.Config)
  | finishing (receiver : HybridCompactFIFO.Code) (control : HybridCompactFIFOControl.Config)
  | stopped (result : Option State)

def step (x y : Int) : Config → Config
  | .stopped r => .stopped r
  | .start (.finish receiver) s q => .finishing receiver (.start s q)
  | .start (.stage a sender tail) s q => .sending a sender tail (.start (erase a s) q)
  | .sending _ _ _ (.stopped none) => .stopped none
  | .sending a _ tail (.stopped (some (s,_,qo))) => .start tail (erase a s) qo
  | .sending a sender tail c@(.start ..) => .sending a sender tail (HybridCompactDuplexControl.step sender x y c)
  | .sending a sender tail c@(.loading ..) => .sending a sender tail (HybridCompactDuplexControl.step sender x y c)
  | .sending a sender tail c@(.ready ..) => .sending a sender tail (HybridCompactDuplexControl.step sender x y c)
  | .sending a sender tail c@(.body ..) => .sending a sender tail (HybridCompactDuplexControl.step sender x y c)
  | .finishing _ (.stopped r) => .stopped (r.map Prod.fst)
  | .finishing receiver c@(.start ..) => .finishing receiver (HybridCompactFIFOControl.step receiver x y c)
  | .finishing receiver c@(.loading ..) => .finishing receiver (HybridCompactFIFOControl.step receiver x y c)
  | .finishing receiver c@(.ready ..) => .finishing receiver (HybridCompactFIFOControl.step receiver x y c)
  | .finishing receiver c@(.body ..) => .finishing receiver (HybridCompactFIFOControl.step receiver x y c)

inductive Reaches (x y : Int) : Config → Config → Prop where
  | refl (a) : Reaches x y a a
  | next : Reaches x y (step x y a) b → Reaches x y a b

theorem Reaches.trans (h : Reaches x y a b) (g : Reaches x y b c) : Reaches x y a c := by
  induction h with
  | refl => exact g
  | next _ ih => exact .next (ih g)

theorem lift_sender (h : HybridCompactDuplexControl.Reaches sender x y a b) :
    Reaches x y (.sending output sender tail a) (.sending output sender tail b) := by
  induction h with
  | refl => exact .refl _
  | @next a b h ih => cases a with
    | start | loading | ready | body => exact .next ih
    | stopped => simpa [HybridCompactDuplexControl.step] using ih

theorem lift_finisher (h : HybridCompactFIFOControl.Reaches receiver x y a b) :
    Reaches x y (.finishing receiver a) (.finishing receiver b) := by
  induction h with
  | refl => exact .refl _
  | @next a b h ih => cases a with
    | start | loading | ready | body => exact .next ih
    | stopped => simpa [HybridCompactFIFOControl.step] using ih

theorem correct (code : Code) (s : State) (q : List Int) :
    Reaches x y (.start code s q) (.stopped (code.eval x y s q)) := by
  induction code generalizing s q with
  | finish receiver =>
    apply Reaches.next
    apply (lift_finisher (HybridCompactFIFOControl.correct (x:=x) (y:=y) receiver s q)).trans
    exact .next (.refl _)
  | stage a sender tail ih =>
    apply Reaches.next
    apply (lift_sender (HybridCompactDuplexControl.correct (x:=x) (y:=y) sender (erase a s) q)).trans
    simp only [Code.eval,← HybridCompactDuplexControl.evalFull_correct]
    cases HybridCompactDuplexControl.evalFull sender x y (erase a s) q with
    | none => exact .next (.refl _)
    | some triple => obtain ⟨t,qi,qo⟩ := triple; exact .next (ih (erase a t) qo)

def run (x y : Int) : Nat → Config → Config
  | 0,c => c
  | n+1,c => run x y n (step x y c)

theorem Reaches.finite (h : Reaches x y a b) : ∃ n, run x y n a = b := by
  induction h with
  | refl => exact ⟨0,rfl⟩
  | next _ ih => obtain ⟨n,hn⟩ := ih; exact ⟨n+1,hn⟩

structure RootCode where
  inputArray : Nat
  output : Nat
  sender : HybridSymbolicProducerLoop.Code
  tail : Code

def lowerRoot (p : HybridCompactChain.Plan outputs sizes first following rest) : RootCode :=
  ⟨first.array,following.array,p.sender.code,lower p.tail⟩

def RootCode.eval (code : RootCode) (x y : Int) (s : State) : Option State := do
  let initial := erase code.output s
  let (t,q) ← code.sender.eval (arrayInput (initial.arrays code.inputArray)) x y initial
  code.tail.eval x y (erase code.output t) q

theorem lowerRoot_correct (p : HybridCompactChain.Plan outputs sizes first following rest) :
    (lowerRoot p).eval x y s = p.eval x y s := by
  simp only [lowerRoot,RootCode.eval,HybridCompactChain.Plan.eval]
  cases p.sender.code.eval (arrayInput ((erase following.array s).arrays first.array)) x y (erase following.array s) with
  | none => rfl
  | some pair => obtain ⟨t,q⟩ := pair; exact lower_correct p.tail

inductive RootConfig where
  | start (code : RootCode) (state : State)
  | sending (code : RootCode) (input : Input) (control : HybridSymbolicProducerControl.Config)
  | tail (control : Config)
  | stopped (result : Option State)

def rootStep (x y : Int) : RootConfig → RootConfig
  | .start code s => .sending code (arrayInput ((erase code.output s).arrays code.inputArray)) (.start (erase code.output s))
  | .sending _ _ (.stopped none) => .stopped none
  | .sending code _ (.stopped (some (s,q))) => .tail (.start code.tail (erase code.output s) q)
  | .sending code input c@(.start ..) => .sending code input (HybridSymbolicProducerControl.step code.sender input x y c)
  | .sending code input c@(.loading ..) => .sending code input (HybridSymbolicProducerControl.step code.sender input x y c)
  | .sending code input c@(.ready ..) => .sending code input (HybridSymbolicProducerControl.step code.sender input x y c)
  | .sending code input c@(.body ..) => .sending code input (HybridSymbolicProducerControl.step code.sender input x y c)
  | .tail (.stopped r) => .stopped r
  | .tail c@(.start ..) => .tail (step x y c)
  | .tail c@(.sending ..) => .tail (step x y c)
  | .tail c@(.finishing ..) => .tail (step x y c)
  | .stopped r => .stopped r

inductive RootReaches (x y : Int) : RootConfig → RootConfig → Prop where
  | refl (a) : RootReaches x y a a
  | next : RootReaches x y (rootStep x y a) b → RootReaches x y a b

theorem RootReaches.trans (h : RootReaches x y a b) (g : RootReaches x y b c) : RootReaches x y a c := by
  induction h with
  | refl => exact g
  | next _ ih => exact .next (ih g)

theorem lift_root_sender (h : HybridSymbolicProducerControl.Reaches code.sender input x y a b) :
    RootReaches x y (.sending code input a) (.sending code input b) := by
  induction h with
  | refl => exact .refl _
  | @next a b h ih => cases a with
    | start | loading | ready | body => exact .next ih
    | stopped => simpa [HybridSymbolicProducerControl.step] using ih

theorem lift_tail (h : Reaches x y a b) : RootReaches x y (.tail a) (.tail b) := by
  induction h with
  | refl => exact .refl _
  | @next a b h ih => cases a with
    | start | sending | finishing => exact .next ih
    | stopped => simpa [step] using ih

theorem rootCorrect (code : RootCode) (s : State) :
    RootReaches x y (.start code s) (.stopped (code.eval x y s)) := by
  apply RootReaches.next
  apply (lift_root_sender (HybridSymbolicProducerControl.correct
    (input:=arrayInput ((erase code.output s).arrays code.inputArray)) (x:=x) (y:=y) code.sender (erase code.output s))).trans
  simp only [RootCode.eval]
  cases code.sender.eval (arrayInput ((erase code.output s).arrays code.inputArray)) x y (erase code.output s) with
  | none => exact .next (.refl _)
  | some pair =>
    obtain ⟨t,q⟩ := pair
    apply RootReaches.next
    apply (lift_tail (correct code.tail (erase code.output t) q)).trans
    exact .next (.refl _)

def runRoot (x y : Int) : Nat → RootConfig → RootConfig
  | 0,c => c
  | n+1,c => runRoot x y n (rootStep x y c)

theorem RootReaches.finite (h : RootReaches x y a b) : ∃ n, runRoot x y n a = b := by
  induction h with
  | refl => exact ⟨0,rfl⟩
  | next _ ih => obtain ⟨n,hn⟩ := ih; exact ⟨n+1,hn⟩

theorem plan_finishes (p : HybridCompactChain.Plan outputs sizes first following rest) (s : State)
    (layout : PipelineShapes.Layout sizes s) :
    ∃ n result, runRoot x y n (.start (lowerRoot p) s) = .stopped result ∧
      result.map (PipelineUse.observe outputs) =
        (HybridCompactStage.source x y (first::following::rest) s).map (PipelineUse.observe outputs) := by
  obtain ⟨n,hn⟩ := (rootCorrect (x:=x) (y:=y) (lowerRoot p) s).finite
  rw [lowerRoot_correct] at hn
  exact ⟨n,_,hn,p.correct s layout⟩

end IRComparison.HybridCompactChainControl
