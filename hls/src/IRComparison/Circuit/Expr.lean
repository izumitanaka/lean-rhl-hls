import IRComparison.Hybrid.HybridValues
import IRComparison.Hybrid.HybridWord

namespace IRComparison.Circuit

inductive Bin where
  | add | sub | mul | div | lt
  deriving Repr, DecidableEq

def Bin.eval : Bin → Int → Int → Int
  | .add => (· + ·)
  | .sub => (· - ·)
  | .mul => (· * ·)
  | .div => (· / ·)
  | .lt => fun a b => if a < b then 1 else 0

/-- Combinational expressions. Reads have no effects; failures become an
explicit validity signal in RTL, not an arbitrary value or an infinite wait. -/
inductive Expr where
  | fail
  | lit (value : Int)
  | wire (slot : Nat)
  | reg (slot : Nat)
  | memory (array : Nat) (index : Expr)
  | bin (op : Bin) (a b : Expr)
  | natIndex (a : Expr)
  | select (condition yes no : Expr)
  /-- Evaluate the first expression for definedness, then return the second.
  This is pure partial sequencing, with no clock or state update. -/
  | seq (first result : Expr)
  deriving Repr, DecidableEq

def Expr.eval (s : IRComparison.State) (wires : Nat → Int) : Expr → Option Int
  | .fail => none
  | .lit n => some n
  | .wire n => some (wires n)
  | .reg n => some (s.regs n)
  | .memory a e => do arrayInput (s.arrays a) (← e.eval s wires)
  | .bin op a b => do return op.eval (← a.eval s wires) (← b.eval s wires)
  | .natIndex a => do return Int.ofNat (← a.eval s wires).toNat
  | .select c a b => do
      if (← c.eval s wires) != 0 then a.eval s wires else b.eval s wires
  | .seq a b => (a.eval s wires).bind fun _ => b.eval s wires

/-- The former bind encoding duplicated the continuation in both branches.
Sequencing preserves every failure, including unused invalid reads. -/
theorem Expr.seq_eq_select (a b : Expr) :
    (Expr.seq a b).eval s w = (Expr.select a b b).eval s w := by
  cases h : a.eval s w <;> simp [eval,h]

def lookup (xs : List Expr) (n : Nat) : Expr := xs[n]?.getD .fail

def value (i x y : Expr) (locals temps : List Expr) : HybridIR.Value → Expr
  | .lit n => .lit n
  | .index => i
  | .left => x
  | .right => y
  | .local n => lookup locals n
  | .temp n => lookup temps n
  | .natIndex v => .natIndex (value i x y locals temps v)
  | .add a b => .bin .add (value i x y locals temps a) (value i x y locals temps b)
  | .sub a b => .bin .sub (value i x y locals temps a) (value i x y locals temps b)
  | .mul a b => .bin .mul (value i x y locals temps a) (value i x y locals temps b)
  | .div a b => .bin .div (value i x y locals temps a) (value i x y locals temps b)

/- Important: bind must still fail when its result is unused. The guarded
version below sequences validity without making it a runtime state effect. -/
def read (i x y : Expr) (locals temps : List Expr) : HybridIR.ReadCode → Expr
  | .pure v => value i x y locals temps v
  | .register r => .reg r
  | .memory a j => .memory a (value i x y locals temps j)
  | .bind first next =>
      let a := read i x y locals temps first
      let b := read i x y locals (a :: temps) next
      .seq a b
  | .branch c yes no => .select (value i x y locals temps c)
      (read i x y locals temps yes) (read i x y locals temps no)

def Matches (s : IRComparison.State) (w : Nat → Int) (es : List Expr) (vs : List Int) : Prop :=
  ∀ n, (lookup es n).eval s w = vs[n]?

theorem matches_cons (h : Matches s w es vs) (he : e.eval s w = some v) :
    Matches s w (e::es) (v::vs) := by
  intro n
  cases n with
  | zero => exact he
  | succ n => exact h n

theorem matches_nil : Matches s w [] [] := by intro n; simp [lookup,Expr.eval]

theorem value_correct (v : HybridIR.Value)
    (hi : i.eval s w = some iv) (hx : x.eval s w = some xv) (hy : y.eval s w = some yv)
    (hl : Matches s w ls lvs) (ht : Matches s w ts tvs) :
    (value i x y ls ts v).eval s w = v.eval iv xv yv lvs tvs := by
  induction v with
  | lit => rfl
  | index => exact hi
  | left => exact hx
  | right => exact hy
  | «local» n => exact hl n
  | temp n => exact ht n
  | natIndex a ih => simp [value,Expr.eval,HybridIR.Value.eval,ih]
  | add a b ha hb | sub a b ha hb | mul a b ha hb | div a b ha hb =>
      simp only [value,Expr.eval,HybridIR.Value.eval,ha,hb,Bin.eval]

theorem read_correct (e : HybridIR.ReadCode)
    (hi : i.eval s w = some iv) (hx : x.eval s w = some xv) (hy : y.eval s w = some yv)
    (hl : Matches s w ls lvs) (ht : Matches s w ts tvs) :
    (read i x y ls ts e).eval s w = e.eval iv xv yv s lvs tvs := by
  induction e generalizing ts tvs with
  | pure v => exact value_correct v hi hx hy hl ht
  | register => rfl
  | memory a j =>
      simp [read,Expr.eval,HybridIR.ReadCode.eval,value_correct j hi hx hy hl ht,arrayInput]
  | bind a b ha hb =>
      simp only [read,Expr.eval,HybridIR.ReadCode.eval,ha ht]
      cases he : a.eval iv xv yv s lvs tvs with
      | none => rfl
      | some v =>
        have hm := matches_cons ht ((ha ht).trans he)
        simp only [bind,Option.bind]
        exact hb hm
  | branch c a b ha hb =>
      simp only [read,Expr.eval,HybridIR.ReadCode.eval,value_correct c hi hx hy hl ht,ha ht,hb ht]

end IRComparison.Circuit
