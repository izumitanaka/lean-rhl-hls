import IRComparison.Core.VersionedHybrid

namespace IRComparison.VersionedStorage

/-- Imperative storage operations on private snapshot slots. `copy` allocates
    a new current slot; assign/store update that slot, preserving older slots.
    This is logical storage, not a claim about physical RAM copying cost. -/
inductive Code where
  | yield (slot : Nat)
  | capture (slot : Nat) (value : HybridIR.ReadCode) (next : Code)
  | copy (slot : Nat) (next : Code)
  | assign (reg : Nat) (value : HybridIR.ReadCode) (next : Code)
  | store (array : Nat) (address value : HybridIR.ReadCode) (next : Code)
  | branch (slot : Nat) (condition : HybridIR.ReadCode) (yes no : Code)
  | bind (body next : Code)
  | call (slot : Nat) (body next : Code)
  | repeat (slot count : Nat) (body next : Code)
  | forRange (slot : Nat) (count : HybridIR.ReadCode) (body next : Code)
  | forRangeCaptured (slot : Nat) (count : HybridIR.ReadCode) (body next : Code)
  deriving Repr

def Code.eval (i x y : Int) : Code → List State → List Int → Option State
  | .yield v,ss,_ => ss[v]?
  | .capture v e b,ss,ls => do
    let s ← ss[v]?
    let a ← e.eval i x y s ls []
    b.eval i x y ss (a::ls)
  | .copy v b,ss,ls => do
    let s ← ss[v]?
    b.eval i x y (s::ss) ls
  | .assign r e b,s::ss,ls => do
    let v ← e.eval i x y s ls []
    b.eval i x y (s.set r v::ss) ls
  | .assign ..,[],_ => none
  | .store a j e b,s::ss,ls => do
    let t ← s.write a (← j.eval i x y s ls []) (← e.eval i x y s ls [])
    b.eval i x y (t::ss) ls
  | .store ..,[],_ => none
  | .branch v e a b,ss,ls => do
    let s ← ss[v]?
    if (← e.eval i x y s ls []) != 0 then a.eval i x y ss ls else b.eval i x y ss ls
  | .bind b n,ss,ls => do
    let t ← b.eval i x y ss ls
    n.eval i x y (t::ss) ls
  | .call v b n,ss,ls => do
    let s ← ss[v]?
    let t ← b.eval i x y [s] ls
    n.eval i x y (t::ss) ls
  | .repeat v count b n,ss,ls => do
    let s ← ss[v]?
    let t ← (List.range count).foldlM (fun t _ => b.eval i x y [t] ls) s
    n.eval i x y (t::ss) ls
  | .forRange v e b n,ss,ls => do
    let s ← ss[v]?
    let count ← e.eval i x y s ls []
    let t ← (List.range count.toNat).foldlM (fun t k => b.eval i x y [t] (Int.ofNat k::ls)) s
    n.eval i x y (t::ss) ls
  | .forRangeCaptured v e b n,ss,ls => do
    let s ← ss[v]?
    let count ← e.eval i x y s ls []
    let t ← (List.range count.toNat).foldlM (fun t k => b.eval i x y (t::ss) (Int.ofNat k::ls)) s
    n.eval i x y (t::ss) ls

/-- Allocation never identifies different versions. The new slot is explicit
    even when a subsequent liveness pass might prove it unnecessary. -/
def lower : VersionedHybrid.Term → Code
  | .yield v => .yield v
  | .letValue v e b => .capture v e (lower b)
  | .letSet v r e b => .copy v (.assign r e (lower b))
  | .letWrite v a j e b => .copy v (.store a j e (lower b))
  | .bindResult b n => .bind (lower b) (lower n)
  | .letResult v b n => .call v (lower b) (lower n)
  | .branch v e a b => .branch v e (lower a) (lower b)
  | .iterate v count b n => .repeat v count (lower b) (lower n)
  | .forRange v count b n => .forRange v count (lower b) (lower n)
  | .forRangeCaptured v count b n => .forRangeCaptured v count (lower b) (lower n)

theorem lower_correct (p : VersionedHybrid.Term) (i x y : Int) (ss : List State) (ls : List Int) :
    (lower p).eval i x y ss ls = p.eval i x y ss ls := by
  induction p generalizing ss ls with
  | yield => rfl
  | letValue v e b ih => simp [lower,Code.eval,VersionedHybrid.Term.eval,ih]
  | letSet v r e b ih =>
    cases h : ss[v]? <;> simp [lower,Code.eval,VersionedHybrid.Term.eval,h,ih]
  | letWrite v a j e b ih =>
    cases h : ss[v]? <;> simp [lower,Code.eval,VersionedHybrid.Term.eval,h,ih]
  | bindResult b n ihb ihn => simp [lower,Code.eval,VersionedHybrid.Term.eval,ihb,ihn]
  | letResult v b n ihb ihn => simp [lower,Code.eval,VersionedHybrid.Term.eval,ihb,ihn]
  | branch v e a b iha ihb => simp [lower,Code.eval,VersionedHybrid.Term.eval,iha,ihb]
  | iterate v count b n ihb ihn => simp [lower,Code.eval,VersionedHybrid.Term.eval,ihb,ihn]
  | forRange v e b n ihb ihn => simp [lower,Code.eval,VersionedHybrid.Term.eval,ihb,ihn]
  | forRangeCaptured v e b n ihb ihn => simp [lower,Code.eval,VersionedHybrid.Term.eval,ihb,ihn]

end IRComparison.VersionedStorage
