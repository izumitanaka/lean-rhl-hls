import IRComparison.Hybrid.HybridCompactFIFO
import IRComparison.Core.FIFOReadControl
import IRComparison.Hybrid.HybridCommandControl

namespace IRComparison.HybridCompactFIFOControl
open HybridCompactFIFO HybridSymbolicLoop

inductive Config where
  | start (state : State) (queue : List Int)
  | loading (remaining ordinal : Nat) (state : State) (loader : FIFOReadControl.Config)
  | ready (remaining ordinal : Nat) (values queue : List Int) (state : State)
  | body (remaining ordinal : Nat) (values queue : List Int) (control : HybridCommandControl.Config)
  | stopped (result : Option (State × List Int))

def step (code : HybridCompactFIFO.Code) (x y : Int) : Config → Config
  | .stopped r => .stopped r
  | .start s q => if code.count = 0 then .stopped (some (s,q)) else
      .loading code.count 0 s (.loading (CompactRouting.instantiate code.start code.initial) [] [] q)
  | .loading _ _ _ (.stopped none) => .stopped none
  | .loading n k s (.stopped (some (vs,q))) => .ready n k vs q s
  | .loading n k s l@(.loading ..) => .loading n k s (FIFOReadControl.step (fun _ => none) l)
  | .ready 0 _ _ q s => .stopped (some (s,q))
  | .ready (n+1) k vs q s => .body n k vs q (.running [(code.body.target,vs)] s [])
  | .body _ _ _ _ (.stopped none) => .stopped none
  | .body 0 _ _ q (.stopped (some (s,_))) => .stopped (some (s,q))
  | .body (n+1) k vs q (.stopped (some (s,_))) =>
      .loading (n+1) (k+1) s (.loading (CompactRouting.instantiate (index code.start code.stride (k+1)) code.refill) vs [] q)
  | .body n k vs q c@(.running ..) => .body n k vs q (HybridCommandControl.step (index code.start code.stride k) x y c)

inductive Reaches (code : HybridCompactFIFO.Code) (x y : Int) : Config → Config → Prop where
  | refl (a) : Reaches code x y a a
  | next : Reaches code x y (step code x y a) b → Reaches code x y a b

theorem Reaches.trans (h : Reaches code x y a b) (g : Reaches code x y b c) : Reaches code x y a c := by
  induction h with
  | refl => exact g
  | next _ ih => exact .next (ih g)

theorem lift_load (h : FIFOReadControl.Reaches (fun _ => none) a b) :
    Reaches code x y (.loading n k s a) (.loading n k s b) := by
  induction h with
  | refl => exact .refl _
  | @next a b h ih => cases a with
    | loading => exact .next ih
    | stopped => simpa [FIFOReadControl.step] using ih

theorem lift_body (h : HybridCommandControl.Reaches (index code.start code.stride k) x y a b) :
    Reaches code x y (.body n k vs q a) (.body n k vs q b) := by
  induction h with
  | refl => exact .refl _
  | @next a b h ih => cases a with
    | running => exact .next ih
    | stopped => simpa [HybridCommandControl.step] using ih

def loadEnd (r : Option (List Int × List Int)) (n k : Nat) (s : State) : Config :=
  match r with | none => .stopped none | some (vs,q) => .ready n k vs q s

theorem load_correct (ls : List CompactRouting.Load) (i : Int) (old q : List Int) :
    Reaches code x y (.loading n k s (.loading (CompactRouting.instantiate i ls) old [] q))
      (loadEnd (WindowFIFO.execute (fun _ => none) old (CompactRouting.instantiate i ls) q) n k s) := by
  have h := FIFOReadControl.correct (input:=fun _ => none) (CompactRouting.instantiate i ls) old [] q
  simp only [List.nil_append] at h
  apply (lift_load h).trans
  cases WindowFIFO.execute (fun _ => none) old (CompactRouting.instantiate i ls) q with
  | none => exact .next (.refl _)
  | some pair => obtain ⟨vs,qs⟩ := pair; exact .next (.refl _)

theorem ready_correct (code : HybridCompactFIFO.Code) (n k : Nat) (vs q : List Int) (s : State) :
    Reaches code x y (.ready n k vs q s) (.stopped (code.loop x y n k vs s q)) := by
  induction n generalizing k vs q s with
  | zero => exact .next (.refl _)
  | succ n ih =>
    apply Reaches.next
    have finished := HybridCommandControl.correct (i:=index code.start code.stride k) (x:=x) (y:=y)
      code.body.target s [] vs []
    have ended : HybridCommandControl.Reaches (index code.start code.stride k) x y
        (.running [(code.body.target,vs)] s [])
        (.stopped ((code.body.eval (index code.start code.stride k) x y s vs).map (fun t => (t,[])))) := by
      rw [HybridIR.MemoryCmd.target_correct] at finished
      apply finished.trans
      cases code.body.eval (index code.start code.stride k) x y s vs with
      | none => exact .refl _
      | some t => exact .next (.refl _)
    apply (lift_body ended).trans
    rw [HybridCompactFIFO.Code.loop]
    cases he : code.body.eval (index code.start code.stride k) x y s vs with
    | none => exact .next (.refl _)
    | some t =>
      cases n with
      | zero => exact .next (.refl _)
      | succ m =>
        apply Reaches.next
        apply (load_correct code.refill (index code.start code.stride (k+1)) vs q).trans
        cases hl : WindowFIFO.execute (fun _ => none) vs (CompactRouting.instantiate (index code.start code.stride (k+1)) code.refill) q with
        | none => exact .refl _
        | some pair => obtain ⟨next,qs⟩ := pair; exact ih (k+1) next qs t

theorem correct (code : HybridCompactFIFO.Code) (s : State) (q : List Int) :
    Reaches code x y (.start s q) (.stopped (code.eval x y s q)) := by
  cases hc : code.count with
  | zero =>
    apply Reaches.next
    simpa [step,HybridCompactFIFO.Code.eval,hc] using (Reaches.refl (.stopped (some (s,q))))
  | succ n =>
    apply Reaches.next
    simp only [step,hc,Nat.succ_ne_zero,↓reduceIte,HybridCompactFIFO.Code.eval]
    apply (load_correct code.initial code.start [] q).trans
    cases hl : WindowFIFO.execute (fun _ => none) [] (CompactRouting.instantiate code.start code.initial) q with
    | none => exact .refl _
    | some pair => obtain ⟨vs,qs⟩ := pair; exact ready_correct code (n+1) 0 vs qs s

def run (code : HybridCompactFIFO.Code) (x y : Int) : Nat → Config → Config
  | 0,c => c
  | n+1,c => run code x y n (step code x y c)

theorem Reaches.finite (h : Reaches code x y a b) : ∃ n, run code x y n a = b := by
  induction h with
  | refl => exact ⟨0,rfl⟩
  | next _ ih => obtain ⟨n,hn⟩ := ih; exact ⟨n+1,hn⟩

theorem plan_finishes (p : HybridCompactFIFO.Plan memory producer) (s : State) (q : List Int)
    (hq : CommunicationIR.Corresponds input producer.entries q) :
    ∃ n r, run p.code x y n (.start s q) = .stopped r ∧ r.map Prod.fst = memory.eval input x y s := by
  obtain ⟨n,hn⟩ := (correct (x:=x) (y:=y) p.code s q).finite
  exact ⟨n,_,hn,p.correct s q hq⟩

end IRComparison.HybridCompactFIFOControl
