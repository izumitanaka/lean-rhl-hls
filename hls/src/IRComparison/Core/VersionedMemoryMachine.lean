import IRComparison.Core.VersionedLoop
import IRComparison.Core.VersionedPlacement

namespace IRComparison.VersionedMemoryMachine
open WindowSchedule AffineAddress SymbolicWindowExpr SymbolicWindowSchedule HybridIR

/-- Executable counted loop: one body, one initial prelude, one refill prelude.
    Neither construction nor code size enumerates the source iterations. -/
structure Code where
  start : Int
  stride : Int
  count : Nat
  initial : List SymbolicWindowSchedule.Load
  refill : List SymbolicWindowSchedule.Load
  body : VersionedPlacement.Code

open VersionedLoop (index index_next)

def Code.loop (c : Code) (input : Input) (x y : Int) : Nat → Nat → List Int → State → Option State
  | 0,_,_,s => some s
  | n+1,k,values,s => do
    let t ← c.body.eval (index c.start c.stride k) x y s values
    match n with
    | 0 => some t
    | m+1 => do
      let next ← SymbolicWindowSchedule.execute input (index c.start c.stride (k+1)) values c.refill
      c.loop input x y (m+1) (k+1) next t

def Code.eval (c : Code) (input : Input) (x y : Int) (s : State) : Option State :=
  match c.count with
  | 0 => some s
  | n+1 => do
    let initial ← SymbolicWindowSchedule.execute input c.start [] c.initial
    c.loop input x y (n+1) 0 initial s

def allocate (c : VersionedLoop.Code) : Code :=
  ⟨c.start,c.stride,c.count,c.initial,c.refill,(VersionedPlacement.compile c.body).code⟩

theorem loop_correct (c : VersionedLoop.Code) (n k : Nat) (values : List Int) (s : State) :
    (allocate c).loop input x y n k values s = c.loop input x y n k values s := by
  induction n generalizing k values s with
  | zero => rfl
  | succ n ih =>
    rw [Code.loop,VersionedLoop.Code.loop]
    dsimp only [allocate]
    rw [VersionedPlacement.Compiled.correct]
    simp only [VersionedWindow.run]
    cases hb : c.body.eval (index c.start c.stride k) x y [s] values with
    | none => rfl
    | some t =>
      cases n with
      | zero => rfl
      | succ m =>
        simp only [bind,Option.bind]
        cases hl : SymbolicWindowSchedule.execute input (index c.start c.stride (k+1)) values c.refill with
        | none => rfl
        | some next => exact ih (k+1) next t

theorem correct (c : VersionedLoop.Code) : (allocate c).eval input x y s = c.eval input x y s := by
  cases hc : c.count with
  | zero => simp [Code.eval,VersionedLoop.Code.eval,allocate,hc]
  | succ n =>
    simp only [Code.eval,VersionedLoop.Code.eval,allocate,hc]
    cases hl : SymbolicWindowSchedule.execute input c.start [] c.initial with
    | none => rfl
    | some values => simpa only [allocate,hc,bind,Option.bind] using loop_correct (input:=input) (x:=x) (y:=y) c (n+1) 0 values s

end IRComparison.VersionedMemoryMachine
