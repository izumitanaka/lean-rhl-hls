import Std

namespace IRComparison

/-- An immutable array snapshot. Undefined and out-of-bounds reads fail. -/
abbrev Input := Int → Option Int

def arrayInput (xs : Array Int) : Input := fun i =>
  if i < 0 then none else xs[i.toNat]?

/-- Local mutable storage, independent of the immutable input snapshot. -/
structure State where
  regs : Nat → Int
  arrays : Nat → Array Int

def State.set (s : State) (r : Nat) (v : Int) : State :=
  { s with regs := fun k => if k = r then v else s.regs k }

def State.write (s : State) (a : Nat) (i v : Int) : Option State :=
  if i < 0 then none else
  if h : i.toNat < (s.arrays a).size then
    some { s with arrays := fun k =>
      if k = a then (s.arrays a).set i.toNat v h else s.arrays k }
  else none

inductive Expr where
  | lit (n : Int)
  | index | left | right
  | local (slot : Nat)
  | natIndex (value : Expr)
  | reg (r : Nat)
  | add (a b : Expr)
  | sub (a b : Expr)
  | mul (a b : Expr)
  | div (a b : Expr)
  | select (condition yes no : Expr)
  | read (array : Nat) (index : Expr)
  deriving Repr, DecidableEq

def Expr.eval (i x y : Int) (s : State) (expression : Expr) (locals : List Int := []) : Option Int :=
  match expression with
  | .lit n => some n
  | .index => some i
  | .left => some x
  | .right => some y
  | .local n => locals[n]?
  | .natIndex e => do return Int.ofNat (← e.eval i x y s locals).toNat
  | .reg r => some (s.regs r)
  | .add a b => do return (← a.eval i x y s locals) + (← b.eval i x y s locals)
  | .sub a b => do return (← a.eval i x y s locals) - (← b.eval i x y s locals)
  | .mul a b => do return (← a.eval i x y s locals) * (← b.eval i x y s locals)
  | .div a b => do return (← a.eval i x y s locals) / (← b.eval i x y s locals)
  | .select c a b => do
      if (← c.eval i x y s locals) != 0 then a.eval i x y s locals else b.eval i x y s locals
  | .read a e => do
      let j ← e.eval i x y s locals
      if j < 0 then none else (s.arrays a)[j.toNat]?

/-- Arbitrary continuation after the two reads, including failure. -/
abbrev Step (σ : Type) := Int → Int → Int → σ → Option σ

def sourceLoop (input : Input) (step : Step σ) (stride : Int) :
    Nat → Int → σ → Option σ
  | 0, _, s => some s
  | n+1, i, s => do
      let x ← input i
      let y ← input (i + stride)
      let t ← step i x y s
      sourceLoop input step stride n (i + stride) t

/-- A loop with two fixed-offset read bindings. Offsets need not overlap. -/
def readLoop (input : Input) (step : Step σ) (stride leftOffset rightOffset : Int) :
    Nat → Int → σ → Option σ
  | 0, _, s => some s
  | n+1, i, s => do
      let x ← input (i + leftOffset)
      let y ← input (i + rightOffset)
      let t ← step i x y s
      readLoop input step stride leftOffset rightOffset n (i + stride) t

theorem readLoop_overlap (input : Input) (step : Step σ) (stride offset : Int)
    (n : Nat) (i : Int) (s : σ) :
    readLoop input step stride offset (offset + stride) n i s =
      sourceLoop (fun j => input (j + offset)) step stride n i s := by
  induction n generalizing i s with
  | zero => rfl
  | succ n ih =>
      simp only [readLoop, sourceLoop, ih]
      simp [Int.add_comm, Int.add_left_comm]

end IRComparison
