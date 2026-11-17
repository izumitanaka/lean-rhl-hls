import IRComparison.Core.Execution
import IRComparison.Memory.SymbolicProducerLoop
import IRComparison.Memory.SymbolicWindowControl
import IRComparison.Memory.StreamProducerControl
namespace IRComparison.SymbolicProducerControl
open SymbolicWindowLoop SymbolicProducerLoop

inductive Config where
  | start (state : State)
  | loading (remaining ordinal : Nat) (state : State) (output : List Int) (loader : FIFOReadControl.Config)
  | ready (remaining ordinal : Nat) (values output : List Int) (state : State)
  | body (remaining ordinal : Nat) (values : List Int) (control : StreamProducerControl.Config)
  | stopped (result : Option (State × List Int))

def step (code : SymbolicProducerLoop.Code) (input : Input) (x y : Int) : Config → Config
  | .stopped r => .stopped r
  | .start s => if code.count = 0 then .stopped (some (s,[])) else
      .loading code.count 0 s [] (.loading (SymbolicWindowControl.instantiate code.start code.initial) [] [] [])
  | .loading _ _ _ _ (.stopped none) => .stopped none
  | .loading n k s qo (.stopped (some (vs,_))) => .ready n k vs qo s
  | .loading n k s qo l@(.loading ..) => .loading n k s qo (FIFOReadControl.step input l)
  | .ready 0 _ _ qo s => .stopped (some (s,qo))
  | .ready (n+1) k vs qo s => .body n k vs (.running [(code.body,vs)] s qo)
  | .body _ _ _ (.stopped none) => .stopped none
  | .body 0 _ _ (.stopped (some result)) => .stopped (some result)
  | .body (n+1) k vs (.stopped (some (s,qo))) =>
      .loading (n+1) (k+1) s qo (.loading (SymbolicWindowControl.instantiate (index code.start code.stride (k+1)) code.refill) vs [] [])
  | .body n k vs c@(.running ..) => .body n k vs (StreamProducerControl.step (index code.start code.stride k) x y c)

abbrev Reaches (code : SymbolicProducerLoop.Code) (input : Input) (x y : Int) : Config → Config → Prop :=
  Execution.Reaches (step code input x y)

theorem lift_load (h : FIFOReadControl.Reaches input a b) :
    Reaches code input x y (.loading n k s qo a) (.loading n k s qo b) := by
  apply Execution.Reaches.map h (fun a => Config.loading n k s qo a)
  intro a
  cases a <;> first | exact .next (.refl _) | exact .refl _

theorem lift_body (h : StreamProducerControl.Reaches (index code.start code.stride k) x y a b) :
    Reaches code input x y (.body n k vs a) (.body n k vs b) := by
  apply Execution.Reaches.map h (fun a => Config.body n k vs a)
  intro a
  cases a <;> first | exact .next (.refl _) | exact .refl _

def loadEnd (r : Option (List Int)) (n k : Nat) (s : State) (qo : List Int) : Config :=
  match r with | none => .stopped none | some vs => .ready n k vs qo s

theorem load_correct (ls : List SymbolicWindowSchedule.Load) (i : Int) (old qo : List Int) :
    Reaches code input x y (.loading n k s qo (.loading (SymbolicWindowControl.instantiate i ls) old [] []))
      (loadEnd (SymbolicWindowSchedule.execute input i old ls) n k s qo) := by
  have h := FIFOReadControl.correct (input:=input) (SymbolicWindowControl.instantiate i ls) old [] []
  simp only [SymbolicWindowControl.instantiate_correct,List.nil_append,Option.map_map,Function.comp_def] at h
  apply (lift_load h).trans
  cases SymbolicWindowSchedule.execute input i old ls <;> exact .next (.refl _)

theorem ready_correct (code : SymbolicProducerLoop.Code) (n k : Nat) (vs qo : List Int) (s : State) :
    Reaches code input x y (.ready n k vs qo s) (.stopped (code.loop input x y n k vs s qo)) := by
  induction n generalizing k vs qo s with
  | zero => exact .next (.refl _)
  | succ n ih =>
    apply Execution.Reaches.next
    have hb := StreamProducerControl.correct (i:=index code.start code.stride k) (x:=x) (y:=y) code.body s qo vs []
    have finished : StreamProducerControl.Reaches (index code.start code.stride k) x y (.running [(code.body,vs)] s qo)
        (.stopped (code.body.eval (index code.start code.stride k) x y s qo vs)) := by
      apply hb.trans
      cases code.body.eval (index code.start code.stride k) x y s qo vs with
      | none => exact .refl _
      | some pair => obtain ⟨t,qs⟩ := pair; exact .next (.refl _)
    apply (lift_body finished).trans
    rw [SymbolicProducerLoop.Code.loop]
    cases he : code.body.eval (index code.start code.stride k) x y s qo vs with
    | none => exact .next (.refl _)
    | some pair =>
      obtain ⟨t,qs⟩ := pair
      cases n with
      | zero => exact .next (.refl _)
      | succ m =>
        apply Execution.Reaches.next
        apply (load_correct code.refill (index code.start code.stride (k+1)) vs qs).trans
        cases hl : SymbolicWindowSchedule.execute input (index code.start code.stride (k+1)) vs code.refill with
        | none => exact .refl _
        | some next => exact ih (k+1) next qs t

theorem correct (code : SymbolicProducerLoop.Code) (s : State) :
    Reaches code input x y (.start s) (.stopped (code.eval input x y s)) := by
  cases hc : code.count with
  | zero =>
    apply Execution.Reaches.next
    simpa [step,SymbolicProducerLoop.Code.eval,hc] using (Execution.Reaches.refl (Config.stopped (some (s,[]))))
  | succ n =>
    apply Execution.Reaches.next
    simp only [step,hc,Nat.succ_ne_zero,↓reduceIte,SymbolicProducerLoop.Code.eval]
    apply (load_correct code.initial code.start [] []).trans
    cases hl : SymbolicWindowSchedule.execute input code.start [] code.initial with
    | none => exact .refl _
    | some vs => exact ready_correct code (n+1) 0 vs [] s

def run (code : SymbolicProducerLoop.Code) (input : Input) (x y : Int) : Nat → Config → Config :=
  Execution.run (step code input x y)

end IRComparison.SymbolicProducerControl
