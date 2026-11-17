import IRComparison.Circuit.SharedAnalysis
import IRComparison.Circuit.BitArithmetic

namespace IRComparison.Circuit.Shared

/-- Hardware arithmetic at a single shared node. Caller expression leaves use
existing finite-width lowering; all internal operands are cached references. -/
def Node.bitRaw (wr : Nat → Interval) (s : State) (w : Nat → Int) (cache : Cache) : Node → Option Int
  | .input e => e.bitEval wr s w
  | .binary op a b => do return hardwareBin op (← get cache a) (← get cache b)
  | n => n.eval s w cache

def Node.bitEval (wr : Nat → Interval) (rs : Array Interval)
    (s : State) (w : Nat → Int) (cache : Cache) (n : Node) : Option Int :=
  (n.bitRaw wr s w cache).map (fun v => (BitVec.ofInt (signedWidth (n.range wr rs)) v).toInt)

theorem Node.bitRaw_correct (n : Node) (hb : InputsBound s w wr) :
    n.bitRaw wr s w cache = n.eval s w cache := by
  cases n with
  | input e => exact e.bitEval_correct hb
  | binary op a b =>
    simp only [bitRaw,eval]
    cases get cache a <;> cases get cache b <;> simp [hardwareBin_correct]
  | memory | wrap32 | natIndex | select | seq => rfl

theorem Node.bitEval_correct (n : Node) (hb : InputsBound s w wr)
    (hc : Bounded cache rs) : n.bitEval wr rs s w cache = n.eval s w cache := by
  simp only [bitEval,n.bitRaw_correct hb]
  cases he : n.eval s w cache with
  | none => rfl
  | some v =>
    simp only [Option.map_some]
    rw [signedWidth_preserves (n.range_correct hb hc he)]

structure BitBuild where
  ranges : Array Interval
  cache : Cache

/-- Both range and finite-width evaluation are computed once per node. -/
def bitValues (wr : Nat → Interval) (s : State) (w : Nat → Int) : Graph → BitBuild
  | [] => ⟨#[],#[]⟩
  | n::g =>
    let b := bitValues wr s w g
    ⟨b.ranges.push (n.range wr b.ranges),b.cache.push (n.bitEval wr b.ranges s w b.cache)⟩

theorem bitValues_correct (g : Graph) (hb : InputsBound s w wr) :
    (bitValues wr s w g).ranges = ranges wr g ∧
    (bitValues wr s w g).cache = values s w g := by
  induction g with
  | nil => exact ⟨rfl,rfl⟩
  | cons n g ih =>
    simp only [bitValues,ranges,values,ih.1,ih.2,
      n.bitEval_correct hb (ranges_correct g hb),and_self]

def Program.bitEval (p : Program) (wr : Nat → Interval) (s : State) (w : Nat → Int) :=
  get (bitValues wr s w p.graph).cache p.result

theorem Program.bitEval_correct (p : Program) (hb : InputsBound s w wr) :
    p.bitEval wr s w = p.eval s w := by
  simp only [bitEval,eval,(bitValues_correct p.graph hb).2]

theorem compile_bitEval_correct (r : HybridIR.ReadCode) (hb : InputsBound s w wr)
    (hi : i.eval s w = some iv) (hx : x.eval s w = some xv) (hy : y.eval s w = some yv)
    (hl : Matches s w ls lvs) (ht : Matches s w ts tvs) :
    (compile i x y ls ts r).bitEval wr s w = r.eval iv xv yv s lvs tvs :=
  ((compile i x y ls ts r).bitEval_correct hb).trans (compile_read_correct r hi hx hy hl ht)

end IRComparison.Circuit.Shared
