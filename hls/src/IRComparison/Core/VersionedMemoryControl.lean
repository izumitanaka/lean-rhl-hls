import IRComparison.Core.VersionedMemoryMachine
import IRComparison.Core.FIFOReadControl
import IRComparison.Core.VersionedPlacementControl

namespace IRComparison.VersionedMemoryControl
open VersionedMemoryMachine

def instantiate (i : Int) (ls : List SymbolicWindowSchedule.Load) : List WindowFIFO.Load :=
  ls.map (fun l => match l with | .memory a => .memory (a.eval i) | .saved n => .saved n)

theorem instantiate_correct (ls : List SymbolicWindowSchedule.Load) :
    WindowFIFO.execute input old (instantiate i ls) q =
      (SymbolicWindowSchedule.execute input i old ls).map (fun vs => (vs,q)) := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    simp only [instantiate] at ih
    cases l with
    | memory a =>
      cases hv : input (a.eval i) <;> cases ht : SymbolicWindowSchedule.execute input i old ls <;>
        simp [instantiate,WindowFIFO.execute,WindowFIFO.Load.eval,SymbolicWindowSchedule.execute,SymbolicWindowSchedule.Load.eval,ih,hv,ht]
    | saved n =>
      cases hv : old[n]? <;> cases ht : SymbolicWindowSchedule.execute input i old ls <;>
        simp [instantiate,WindowFIFO.execute,WindowFIFO.Load.eval,SymbolicWindowSchedule.execute,SymbolicWindowSchedule.Load.eval,ih,hv,ht]

open VersionedLoop (index)

inductive Config where
  | start (state : State)
  | loading (remaining ordinal : Nat) (state : State) (loader : FIFOReadControl.Config)
  | ready (remaining ordinal : Nat) (values : List Int) (state : State)
  | body (remaining ordinal : Nat) (values : List Int) (control : VersionedPlacementControl.Config)
  | stopped (result : Option State)

def step (code : Code) (input : Input) (x y : Int) : Config → Config
  | .stopped r => .stopped r
  | .start s => if code.count = 0 then .stopped (some s) else
      .loading code.count 0 s (.loading (instantiate code.start code.initial) [] [] [])
  | .loading _ _ _ (.stopped none) => .stopped none
  | .loading n k s (.stopped (some (vs,_))) => .ready n k vs s
  | .loading n k s l@(.loading ..) => .loading n k s (FIFOReadControl.step input l)
  | .ready 0 _ _ s => .stopped (some s)
  | .ready (n+1) k vs s => .body n k vs (.start code.body s vs)
  | .body _ _ _ (.stopped none) => .stopped none
  | .body 0 _ _ (.stopped (some s)) => .stopped (some s)
  | .body (n+1) k vs (.stopped (some s)) =>
      .loading (n+1) (k+1) s (.loading (instantiate (index code.start code.stride (k+1)) code.refill) vs [] [])
  | .body n k vs c@(.start ..) => .body n k vs (VersionedPlacementControl.step (index code.start code.stride k) x y c)
  | .body n k vs c@(.inPlace ..) => .body n k vs (VersionedPlacementControl.step (index code.start code.stride k) x y c)
  | .body n k vs c@(.snapshots ..) => .body n k vs (VersionedPlacementControl.step (index code.start code.stride k) x y c)

inductive Reaches (code : Code) (input : Input) (x y : Int) : Config → Config → Prop where
  | refl (a) : Reaches code input x y a a
  | next : Reaches code input x y (step code input x y a) b → Reaches code input x y a b

theorem Reaches.trans (h : Reaches code input x y a b) (g : Reaches code input x y b c) : Reaches code input x y a c := by
  induction h with
  | refl => exact g
  | next _ ih => exact .next (ih g)

theorem lift_load (h : FIFOReadControl.Reaches input a b) :
    Reaches code input x y (.loading n k s a) (.loading n k s b) := by
  induction h with
  | refl => exact .refl _
  | @next a b h ih => cases a with
    | loading => exact .next ih
    | stopped => simpa [FIFOReadControl.step] using ih

theorem lift_body (h : VersionedPlacementControl.Reaches (index code.start code.stride k) x y a b) :
    Reaches code input x y (.body n k vs a) (.body n k vs b) := by
  induction h with
  | refl => exact .refl _
  | @next a b h ih => cases a with
    | start | inPlace | snapshots => exact .next ih
    | stopped => simpa [VersionedPlacementControl.step] using ih

def loadEnd (r : Option (List Int)) (n k : Nat) (s : State) : Config :=
  match r with | none => .stopped none | some vs => .ready n k vs s

theorem load_correct (ls : List SymbolicWindowSchedule.Load) (i : Int) (old : List Int) :
    Reaches code input x y (.loading n k s (.loading (instantiate i ls) old [] []))
      (loadEnd (SymbolicWindowSchedule.execute input i old ls) n k s) := by
  have h := FIFOReadControl.correct (input:=input) (instantiate i ls) old [] []
  simp only [instantiate_correct,List.nil_append,Option.map_map,Function.comp_def] at h
  apply (lift_load h).trans
  cases SymbolicWindowSchedule.execute input i old ls <;> exact .next (.refl _)

theorem ready_correct (code : Code) (n k : Nat) (vs : List Int) (s : State) :
    Reaches code input x y (.ready n k vs s) (.stopped (code.loop input x y n k vs s)) := by
  induction n generalizing k vs s with
  | zero => exact .next (.refl _)
  | succ n ih =>
    apply Reaches.next
    have ended := VersionedPlacementControl.correct (i:=index code.start code.stride k) (x:=x) (y:=y) code.body s vs
    apply (lift_body ended).trans
    rw [Code.loop]
    cases he : code.body.eval (index code.start code.stride k) x y s vs with
    | none => exact .next (.refl _)
    | some t =>
      cases n with
      | zero => exact .next (.refl _)
      | succ m =>
        apply Reaches.next
        apply (load_correct code.refill (index code.start code.stride (k+1)) vs).trans
        cases hl : SymbolicWindowSchedule.execute input (index code.start code.stride (k+1)) vs code.refill with
        | none => exact .refl _
        | some next => exact ih (k+1) next t

theorem correct (code : Code) (s : State) :
    Reaches code input x y (.start s) (.stopped (code.eval input x y s)) := by
  cases hc : code.count with
  | zero =>
    apply Reaches.next
    simpa [step,Code.eval,hc] using (Reaches.refl (.stopped (some s)))
  | succ n =>
    apply Reaches.next
    simp only [step,hc,Nat.succ_ne_zero,↓reduceIte,Code.eval]
    apply (load_correct code.initial code.start []).trans
    cases hl : SymbolicWindowSchedule.execute input code.start [] code.initial with
    | none => exact .refl _
    | some vs => exact ready_correct code (n+1) 0 vs s

def run (code : Code) (input : Input) (x y : Int) : Nat → Config → Config
  | 0,c => c
  | n+1,c => run code input x y n (step code input x y c)

theorem Reaches.finite (h : Reaches code input x y a b) : ∃ n, run code input x y n a = b := by
  induction h with
  | refl => exact ⟨0,rfl⟩
  | next _ ih => obtain ⟨n,hn⟩ := ih; exact ⟨n+1,hn⟩

end IRComparison.VersionedMemoryControl
