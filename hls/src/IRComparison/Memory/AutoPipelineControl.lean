import IRComparison.Memory.AutoPipeline
import IRComparison.Memory.StreamFusionControl

namespace IRComparison.AutoPipelineControl
open StreamConsumer

inductive Region where
  | memory (array : Nat) (order : List Int) (fifo : Bool) (code : List WindowTransport.Block)
  | stream (privateArray inputArray : Nat) (order : List Int) (fifo : Bool)
      (producer : List StreamProducerBlocks.Block) (consumer : List WindowTransport.Block)

def queue (array : Nat) (order : List Int) (fifo : Bool) (s : State) : Option (List Int) :=
  if fifo then CommunicationIR.emit (arrayInput (s.arrays array)) order else some []

def Region.eval (r : Region) (x y : Int) (s : State) : Option State :=
  match r with
  | .memory a order fifo code => do
    let q ← queue a order fifo s
    (WindowTransport.eval (arrayInput (s.arrays a)) x y code [] s q).map Prod.fst
  | .stream a input order fifo producer consumer => do
    let initial := erase a s
    let q ← queue input order fifo initial
    StreamFusionControl.eval a producer consumer (arrayInput (initial.arrays input)) x y initial q

def lower (p : AutoPipeline.Plan outputs sizes ps) : List Region :=
  match p with
  | .nil => []
  | .keep first _ tail => .memory first.array first.producer first.fifo first.code :: lower tail
  | .fuse first second _ _ pair _ tail =>
    .stream second.array first.array first.producer first.fifo pair.producerCode.code second.code :: lower tail
  | .alternatives first second _ _ pair _ tail =>
    .stream second.array first.array first.producer first.fifo pair.producerCode.code pair.receiver.code :: lower tail

def eval (x y : Int) : List Region → State → Option State
  | [],s => some s
  | r::rs,s => do eval x y rs (← r.eval x y s)

theorem lower_correct (p : AutoPipeline.Plan outputs sizes ps) :
    eval x y (lower p) s = p.eval x y s := by
  induction p generalizing s with
  | nil => rfl
  | keep first reason tail ih =>
    change (first.eval x y s).bind (eval x y (lower tail)) = (first.eval x y s).bind (tail.eval x y)
    cases first.eval x y s with
    | none => rfl
    | some t => exact ih
  | fuse first second hidden sizeOK pair unused tail ih =>
    change (pair.eval x y s).bind (eval x y (lower tail)) = (pair.eval x y s).bind (tail.eval x y)
    cases pair.eval x y s with
    | none => rfl
    | some t => exact ih
  | alternatives first second hidden sizeOK pair unused tail ih =>
    change (pair.eval x y s).bind (eval x y (lower tail)) = (pair.eval x y s).bind (tail.eval x y)
    cases pair.eval x y s with
    | none => rfl
    | some t => exact ih

inductive Config where
  | start (regions : List Region) (state : State)
  | memory (rest : List Region) (input : Input) (control : WindowControl.Config)
  | stream (rest : List Region) (array : Nat) (consumer : List WindowTransport.Block)
      (input : Input) (control : StreamFusionControl.Config)
  | stopped (result : Option State)

def step (x y : Int) : Config → Config
  | .stopped r => .stopped r
  | .start [] s => .stopped (some s)
  | .start (.memory a order fifo code::rs) s =>
    match queue a order fifo s with
    | none => .stopped none
    | some q => .memory rs (arrayInput (s.arrays a)) (.start (WindowControl.lower code) [] s q)
  | .start (.stream a input order fifo producer consumer::rs) s =>
    let initial := erase a s
    match queue input order fifo initial with
    | none => .stopped none
    | some q => .stream rs a consumer (arrayInput (initial.arrays input)) (.producer (.start producer [] initial q []))
  | .memory _ _ (.stopped none _) => .stopped none
  | .memory rs _ (.stopped (some s) _) => .start rs s
  | .memory rs input c@(.start ..) => .memory rs input (WindowControl.step input x y c)
  | .memory rs input c@(.loading ..) => .memory rs input (WindowControl.step input x y c)
  | .memory rs input c@(.body ..) => .memory rs input (WindowControl.step input x y c)
  | .stream _ _ _ _ (.stopped none) => .stopped none
  | .stream rs _ _ _ (.stopped (some s)) => .start rs s
  | .stream rs a consumer input c@(.producer ..) => .stream rs a consumer input (StreamFusionControl.step a consumer input x y c)
  | .stream rs a consumer input c@(.consumer ..) => .stream rs a consumer input (StreamFusionControl.step a consumer input x y c)

inductive Reaches (x y : Int) : Config → Config → Prop where
  | refl (a) : Reaches x y a a
  | next : Reaches x y (step x y a) b → Reaches x y a b

theorem Reaches.trans (h : Reaches x y a b) (k : Reaches x y b c) : Reaches x y a c := by
  induction h with
  | refl => exact k
  | next _ ih => exact .next (ih k)

theorem lift_memory (h : WindowControl.Reaches input x y a b) :
    Reaches x y (.memory rest input a) (.memory rest input b) := by
  induction h with
  | refl => exact .refl _
  | @next a b h ih =>
    cases a with
    | start | loading | body => exact .next ih
    | stopped => simpa [WindowControl.step] using ih

theorem lift_stream (h : StreamFusionControl.Reaches array consumer input x y a b) :
    Reaches x y (.stream rest array consumer input a) (.stream rest array consumer input b) := by
  induction h with
  | refl => exact .refl _
  | @next a b h ih =>
    cases a with
    | producer | consumer => exact .next ih
    | stopped => simpa [StreamFusionControl.step] using ih

theorem correct (rs : List Region) (s : State) :
    Reaches x y (.start rs s) (.stopped (eval x y rs s)) := by
  induction rs generalizing s with
  | nil => exact .next (.refl _)
  | cons r rs ih =>
    cases r with
    | memory a order fifo code =>
      cases hq : queue a order fifo s with
      | none =>
        apply Reaches.next
        simpa [step,eval,Region.eval,hq] using (Reaches.refl (.stopped none))
      | some q =>
        apply Reaches.next
        simp only [step,hq]
        obtain ⟨errorQueue,h⟩ := WindowControl.lower_correct (input:=arrayInput (s.arrays a)) (x:=x) (y:=y) code [] s q
        apply (lift_memory h).trans
        cases he : WindowTransport.eval (arrayInput (s.arrays a)) x y code [] s q with
        | none =>
          simp only [WindowControl.resultEnd,eval,Region.eval,hq,he,bind,Option.bind,Option.map_none]
          exact .next (.refl _)
        | some pair =>
          obtain ⟨t,qs⟩ := pair
          simp only [WindowControl.resultEnd,eval,Region.eval,hq,he,bind,Option.bind,Option.map_some]
          exact .next (ih t)
    | stream a input order fifo producer consumer =>
      cases hq : queue input order fifo (erase a s) with
      | none =>
        apply Reaches.next
        simpa [step,eval,Region.eval,hq] using (Reaches.refl (.stopped none))
      | some q =>
        apply Reaches.next
        simp only [step,hq]
        apply (lift_stream (StreamFusionControl.correct (array:=a) (input:=arrayInput ((erase a s).arrays input))
          (x:=x) (y:=y) producer consumer (erase a s) q)).trans
        cases he : StreamFusionControl.eval a producer consumer (arrayInput ((erase a s).arrays input)) x y (erase a s) q with
        | none => simp only [eval,Region.eval,hq,he,bind,Option.bind]; exact .next (.refl _)
        | some t => simp only [eval,Region.eval,hq,he,bind,Option.bind]; exact .next (ih t)

def run (x y : Int) : Nat → Config → Config
  | 0,c => c
  | n+1,c => run x y n (step x y c)

theorem Reaches.finite (h : Reaches x y a b) : ∃ n, run x y n a = b := by
  induction h with
  | refl => exact ⟨0,rfl⟩
  | next _ ih => obtain ⟨n,hn⟩ := ih; exact ⟨n+1,hn⟩

theorem plan_finishes (p : AutoPipeline.Plan outputs sizes ps) (s : State) :
    ∃ n, run x y n (.start (lower p) s) = .stopped (p.eval x y s) := by
  simpa only [lower_correct] using (correct (x:=x) (y:=y) (lower p) s).finite

theorem compile_finishes (outputs : List Nat) (sizes : Nat → Nat) (ps : List WindowPipeline.Stage)
    (s : State) (layout : PipelineShapes.Layout sizes s) (ready : WindowPipeline.Ready x y ps s) :
    ∃ n result, run x y n (.start (lower (AutoPipeline.compile outputs sizes ps)) s) = .stopped result ∧
      result.map (PipelineUse.observe outputs) = (WindowPipeline.source x y ps s).map (PipelineUse.observe outputs) := by
  obtain ⟨n,hn⟩ := plan_finishes (x:=x) (y:=y) (AutoPipeline.compile outputs sizes ps) s
  exact ⟨n,_,hn,AutoPipeline.compile_correct outputs sizes ps s layout ready⟩

end IRComparison.AutoPipelineControl
