import IRComparison.Hybrid.HybridCompactDuplex
import IRComparison.Hybrid.HybridSymbolicWindowControl
import IRComparison.Hybrid.HybridCommandControl

namespace IRComparison.HybridCompactDuplexControl
open HybridSymbolicLoop HybridCompactDuplex

inductive Config where
  | start (state : State) (inputQueue : List Int)
  | loading (remaining ordinal : Nat) (state : State) (output : List Int) (loader : FIFOReadControl.Config)
  | ready (remaining ordinal : Nat) (values inputQueue output : List Int) (state : State)
  | body (remaining ordinal : Nat) (values inputQueue : List Int) (control : HybridCommandControl.Config)
  | stopped (result : Option (State × List Int × List Int))

def step (code : HybridCompactDuplex.Code) (x y : Int) : Config → Config
  | .stopped r => .stopped r
  | .start s qi => if code.count = 0 then .stopped (some (s,qi,[])) else
      .loading code.count 0 s [] (.loading (CompactRouting.instantiate code.start code.initial) [] [] qi)
  | .loading _ _ _ _ (.stopped none) => .stopped none
  | .loading n k s qo (.stopped (some (vs,qi))) => .ready n k vs qi qo s
  | .loading n k s qo l@(.loading ..) => .loading n k s qo (FIFOReadControl.step (fun _ => none) l)
  | .ready 0 _ _ qi qo s => .stopped (some (s,qi,qo))
  | .ready (n+1) k vs qi qo s => .body n k vs qi (.running [(code.body,vs)] s qo)
  | .body _ _ _ _ (.stopped none) => .stopped none
  | .body 0 _ _ qi (.stopped (some (s,qo))) => .stopped (some (s,qi,qo))
  | .body (n+1) k vs qi (.stopped (some (s,qo))) =>
      .loading (n+1) (k+1) s qo (.loading (CompactRouting.instantiate (index code.start code.stride (k+1)) code.refill) vs [] qi)
  | .body n k vs qi c@(.running ..) => .body n k vs qi (HybridCommandControl.step (index code.start code.stride k) x y c)

inductive Reaches (code : HybridCompactDuplex.Code) (x y : Int) : Config → Config → Prop where
  | refl (a) : Reaches code x y a a
  | next : Reaches code x y (step code x y a) b → Reaches code x y a b

theorem Reaches.trans (h : Reaches code x y a b) (g : Reaches code x y b c) : Reaches code x y a c := by
  induction h with
  | refl => exact g
  | next _ ih => exact .next (ih g)

theorem lift_load (h : FIFOReadControl.Reaches (fun _ => none) a b) :
    Reaches code x y (.loading n k s qo a) (.loading n k s qo b) := by
  induction h with
  | refl => exact .refl _
  | @next a b h ih => cases a with
    | loading => exact .next ih
    | stopped => simpa [FIFOReadControl.step] using ih

theorem lift_body (h : HybridCommandControl.Reaches (index code.start code.stride k) x y a b) :
    Reaches code x y (.body n k vs qi a) (.body n k vs qi b) := by
  induction h with
  | refl => exact .refl _
  | @next a b h ih => cases a with
    | running => exact .next ih
    | stopped => simpa [HybridCommandControl.step] using ih

def loadEnd (r : Option (List Int × List Int)) (n k : Nat) (s : State) (qo : List Int) : Config :=
  match r with | none => .stopped none | some (vs,qi) => .ready n k vs qi qo s

theorem load_correct (ls : List CompactRouting.Load) (i : Int) (old qi qo : List Int) :
    Reaches code x y (.loading n k s qo (.loading (CompactRouting.instantiate i ls) old [] qi))
      (loadEnd (WindowFIFO.execute (fun _ => none) old (CompactRouting.instantiate i ls) qi) n k s qo) := by
  have h := FIFOReadControl.correct (input:=fun _ => none) (CompactRouting.instantiate i ls) old [] qi
  simp only [List.nil_append,Option.map_id_fun] at h
  apply (lift_load h).trans
  cases WindowFIFO.execute (fun _ => none) old (CompactRouting.instantiate i ls) qi with
  | none => exact .next (.refl _)
  | some pair => obtain ⟨vs,qs⟩ := pair; exact .next (.refl _)

theorem ready_correct (code : HybridCompactDuplex.Code) (n k : Nat) (vs qi qo : List Int) (s : State) :
    Reaches code x y (.ready n k vs qi qo s) (.stopped (code.loop x y n k vs s qi qo)) := by
  induction n generalizing k vs qi qo s with
  | zero => exact .next (.refl _)
  | succ n ih =>
    apply Reaches.next
    have hb := HybridCommandControl.correct (i:=index code.start code.stride k) (x:=x) (y:=y) code.body s qo vs []
    have finished : HybridCommandControl.Reaches (index code.start code.stride k) x y (.running [(code.body,vs)] s qo)
        (.stopped (code.body.eval (index code.start code.stride k) x y s qo vs)) := by
      apply hb.trans
      cases code.body.eval (index code.start code.stride k) x y s qo vs with
      | none => exact .refl _
      | some pair => obtain ⟨t,qs⟩ := pair; exact .next (.refl _)
    apply (lift_body finished).trans
    rw [HybridCompactDuplex.Code.loop]
    cases he : code.body.eval (index code.start code.stride k) x y s qo vs with
    | none => exact .next (.refl _)
    | some pair =>
      obtain ⟨t,qs⟩ := pair
      cases n with
      | zero => exact .next (.refl _)
      | succ m =>
        apply Reaches.next
        apply (load_correct code.refill (index code.start code.stride (k+1)) vs qi qs).trans
        cases hl : WindowFIFO.execute (fun _ => none) vs (CompactRouting.instantiate (index code.start code.stride (k+1)) code.refill) qi with
        | none => exact .refl _
        | some pair => obtain ⟨next,rest⟩ := pair; exact ih (k+1) next rest qs t

def evalFull (code : HybridCompactDuplex.Code) (x y : Int) (s : State) (qi : List Int) : Option (State × List Int × List Int) :=
  match code.count with
  | 0 => some (s,qi,[])
  | n+1 => do
    let (vs,rest) ← WindowFIFO.execute (fun _ => none) [] (CompactRouting.instantiate code.start code.initial) qi
    code.loop x y (n+1) 0 vs s rest []

theorem correct (code : HybridCompactDuplex.Code) (s : State) (qi : List Int) :
    Reaches code x y (.start s qi) (.stopped (evalFull code x y s qi)) := by
  cases hc : code.count with
  | zero =>
    apply Reaches.next
    simpa [step,evalFull,hc] using (Reaches.refl (.stopped (some (s,qi,[]))))
  | succ n =>
    apply Reaches.next
    simp only [step,hc,Nat.succ_ne_zero,↓reduceIte,evalFull]
    apply (load_correct code.initial code.start [] qi []).trans
    cases hl : WindowFIFO.execute (fun _ => none) [] (CompactRouting.instantiate code.start code.initial) qi with
    | none => exact .refl _
    | some pair => obtain ⟨vs,rest⟩ := pair; exact ready_correct code (n+1) 0 vs rest [] s

theorem evalFull_correct (code : HybridCompactDuplex.Code) :
    (evalFull code x y s qi).map (fun (t,_,qo) => (t,qo)) = code.eval x y s qi := by
  cases hc : code.count with
  | zero => simp [evalFull,HybridCompactDuplex.Code.eval,hc]
  | succ n =>
    simp only [evalFull,HybridCompactDuplex.Code.eval,hc]
    cases WindowFIFO.execute (fun _ => none) [] (CompactRouting.instantiate code.start code.initial) qi <;> rfl

def run (code : HybridCompactDuplex.Code) (x y : Int) : Nat → Config → Config
  | 0,c => c
  | n+1,c => run code x y n (step code x y c)

theorem Reaches.finite (h : Reaches code x y a b) : ∃ n, run code x y n a = b := by
  induction h with
  | refl => exact ⟨0,rfl⟩
  | next _ ih => obtain ⟨n,hn⟩ := ih; exact ⟨n+1,hn⟩

end IRComparison.HybridCompactDuplexControl
