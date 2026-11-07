import IRComparison.Core.VersionedFIFO
import IRComparison.Core.VersionedPlacement

namespace IRComparison.VersionedFIFOMachine
open CompactRouting AffineAddress VersionedLoop

structure Code where
  start : Int
  stride : Int
  count : Nat
  initial : List CompactRouting.Load
  refill : List CompactRouting.Load
  body : VersionedPlacement.Code

def Code.loop (c : Code) (x y : Int) : Nat → Nat → List Int → State → List Int → Option (State × List Int)
  | 0,_,_,s,q => some (s,q)
  | n+1,k,old,s,q => do
    let t ← c.body.eval (index c.start c.stride k) x y s old
    match n with
    | 0 => some (t,q)
    | m+1 =>
      let (vs,qs) ← WindowFIFO.execute (fun _ => none) old
        (instantiate (index c.start c.stride (k+1)) c.refill) q
      c.loop x y (m+1) (k+1) vs t qs

def Code.eval (c : Code) (x y : Int) (s : State) (q : List Int) : Option (State × List Int) :=
  match c.count with
  | 0 => some (s,q)
  | n+1 => do
    let (vs,qs) ← WindowFIFO.execute (fun _ => none) [] (instantiate c.start c.initial) q
    c.loop x y (n+1) 0 vs s qs

def allocate (c : VersionedFIFO.Code) : Code :=
  ⟨c.start,c.stride,c.count,c.initial,c.refill,(VersionedPlacement.compile c.body).code⟩

theorem loop_correct (c : VersionedFIFO.Code) (n k : Nat) (old : List Int) (s : State) (q : List Int) :
    (allocate c).loop x y n k old s q = c.loop x y n k old s q := by
  induction n generalizing k old s q with
  | zero => rfl
  | succ n ih =>
    rw [Code.loop,VersionedFIFO.Code.loop]
    dsimp only [allocate]
    rw [VersionedPlacement.Compiled.correct]
    simp only [VersionedWindow.run]
    cases hb : c.body.eval (index c.start c.stride k) x y [s] old with
    | none => rfl
    | some t =>
      cases n with
      | zero => rfl
      | succ m =>
        simp only [bind,Option.bind]
        cases hl : WindowFIFO.execute (fun _ => none) old (instantiate (index c.start c.stride (k+1)) c.refill) q with
        | none => rfl
        | some pair => obtain ⟨vs,qs⟩ := pair; exact ih (k+1) vs t qs

theorem correct (c : VersionedFIFO.Code) : (allocate c).eval x y s q = c.eval x y s q := by
  cases hc : c.count with
  | zero => simp [Code.eval,VersionedFIFO.Code.eval,allocate,hc]
  | succ n =>
    simp only [Code.eval,VersionedFIFO.Code.eval,allocate,hc]
    cases hl : WindowFIFO.execute (fun _ => none) [] (instantiate c.start c.initial) q with
    | none => rfl
    | some pair =>
      obtain ⟨vs,qs⟩ := pair
      simpa only [allocate,hc,bind,Option.bind] using loop_correct (x:=x) (y:=y) c (n+1) 0 vs s qs

end IRComparison.VersionedFIFOMachine
