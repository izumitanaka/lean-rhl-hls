import IRComparison.Memory.StreamFusion
import IRComparison.Memory.StreamBlocksControl

namespace IRComparison.StreamFusionControl
open StreamConsumer

inductive Config where
  | producer (control : StreamBlocksControl.Config)
  | consumer (control : WindowControl.Config)
  | stopped (result : Option State)

def step (array : Nat) (consumer : List WindowTransport.Block) (input : Input) (x y : Int) : Config → Config
  | .stopped r => .stopped r
  | .producer (.stopped none) => .stopped none
  | .producer (.stopped (some (s,_,out))) =>
    .consumer (.start (WindowControl.lower consumer) [] (erase array s) out)
  | .producer c@(.start ..) => .producer (StreamBlocksControl.step input x y c)
  | .producer c@(.loading ..) => .producer (StreamBlocksControl.step input x y c)
  | .producer c@(.body ..) => .producer (StreamBlocksControl.step input x y c)
  | .consumer (.stopped r _) => .stopped r
  | .consumer c@(.start ..) => .consumer (WindowControl.step (fun _ => none) x y c)
  | .consumer c@(.loading ..) => .consumer (WindowControl.step (fun _ => none) x y c)
  | .consumer c@(.body ..) => .consumer (WindowControl.step (fun _ => none) x y c)

inductive Reaches (array : Nat) (consumer : List WindowTransport.Block) (input : Input) (x y : Int) : Config → Config → Prop where
  | refl (a) : Reaches array consumer input x y a a
  | next : Reaches array consumer input x y (step array consumer input x y a) b → Reaches array consumer input x y a b

theorem Reaches.trans (h : Reaches array consumer input x y a b) (k : Reaches array consumer input x y b c) :
    Reaches array consumer input x y a c := by
  induction h with
  | refl => exact k
  | next _ ih => exact .next (ih k)

theorem lift_producer (h : StreamBlocksControl.Reaches input x y a b) :
    Reaches array consumer input x y (.producer a) (.producer b) := by
  induction h with
  | refl => exact .refl _
  | @next a b h ih =>
    cases a with
    | start | loading | body => exact .next ih
    | stopped => simpa [StreamBlocksControl.step] using ih

theorem lift_consumer (h : WindowControl.Reaches (fun _ => none) x y a b) :
    Reaches array consumer input x y (.consumer a) (.consumer b) := by
  induction h with
  | refl => exact .refl _
  | @next a b h ih =>
    cases a with
    | start | loading | body => exact .next ih
    | stopped => simpa [WindowControl.step] using ih

def eval (array : Nat) (producer : List StreamProducerBlocks.Block) (consumer : List WindowTransport.Block)
    (input : Input) (x y : Int) (s : State) (qi : List Int) : Option State := do
  let (t,_,qo) ← StreamProducerBlocks.eval input x y producer [] s qi []
  (WindowTransport.eval (fun _ => none) x y consumer [] (erase array t) qo).map Prod.fst

theorem correct (producer : List StreamProducerBlocks.Block) (consumer : List WindowTransport.Block)
    (s : State) (qi : List Int) :
    Reaches array consumer input x y (.producer (.start producer [] s qi []))
      (.stopped (eval array producer consumer input x y s qi)) := by
  apply (lift_producer (StreamBlocksControl.correct producer [] s qi [])).trans
  cases hp : StreamProducerBlocks.eval input x y producer [] s qi [] with
  | none => simp only [eval,hp,bind,Option.bind]; exact .next (.refl _)
  | some pair =>
    obtain ⟨t,rest,qo⟩ := pair
    apply Reaches.next
    obtain ⟨errorQueue,h⟩ := WindowControl.lower_correct (input:=fun _ => none) (x:=x) (y:=y) consumer [] (erase array t) qo
    apply (lift_consumer h).trans
    cases hc : WindowTransport.eval (fun _ => none) x y consumer [] (erase array t) qo with
    | none => simp only [WindowControl.resultEnd,eval,hp,hc,bind,Option.bind,Option.map_none]; exact .next (.refl _)
    | some pair =>
      obtain ⟨u,qs⟩ := pair
      simp only [WindowControl.resultEnd,eval,hp,hc,bind,Option.bind,Option.map_some]
      exact .next (.refl _)

def run (array : Nat) (consumer : List WindowTransport.Block) (input : Input) (x y : Int) : Nat → Config → Config
  | 0,c => c
  | n+1,c => run array consumer input x y n (step array consumer input x y c)

theorem Reaches.finite (h : Reaches array consumer input x y a b) :
    ∃ n, run array consumer input x y n a = b := by
  induction h with
  | refl => exact ⟨0,rfl⟩
  | next _ ih => obtain ⟨n,hn⟩ := ih; exact ⟨n+1,hn⟩

theorem plan_finishes (p : StreamFusion.Plan producer consumer array size) (s : State)
    (ready : producer.Ready s) (sized : (s.arrays array).size = size) (x y : Int) :
    ∃ qi n, producer.queue (erase array s) = some qi ∧
      run array consumer.code (arrayInput ((erase array s).arrays producer.array)) x y n
        (.producer (.start p.producerCode.code [] (erase array s) qi [])) =
        .stopped (((do consumer.source x y (← producer.source x y s))).map (erase array)) := by
  obtain ⟨qi,hq,hc⟩ := producer.queue_ready s ready
  have ha : (erase array s).arrays producer.array = s.arrays producer.array := by simp [erase,p.inputDifferent]
  have hq' : producer.queue (erase array s) = some qi := by simpa [WindowPipeline.Stage.queue,ha] using hq
  have same := p.correct s ready sized x y
  simp only [StreamFusion.Plan.eval,hq',bind,Option.bind] at same
  obtain ⟨n,hn⟩ := (correct (array:=array) (input:=arrayInput ((erase array s).arrays producer.array))
    (x:=x) (y:=y) p.producerCode.code consumer.code (erase array s) qi).finite
  have heval : eval array p.producerCode.code consumer.code
      (arrayInput ((erase array s).arrays producer.array)) x y (erase array s) qi =
      ((do consumer.source x y (← producer.source x y s))).map (erase array) := same
  exact ⟨qi,n,hq',by rw [← heval]; exact hn⟩

end IRComparison.StreamFusionControl
