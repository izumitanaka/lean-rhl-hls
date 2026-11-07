import IRComparison.Hybrid.HybridWord

namespace IRComparison.HybridWord
open HybridIR

structure State where
  regs : Nat → Word
  arrays : Nat → Array Word

def State.encode (s : State) : IRComparison.State :=
  ⟨fun r => HybridWord.encode (s.regs r), fun a => (s.arrays a).map HybridWord.encode⟩

/-- Typed word operations at the mixed IR boundary, not a new source language. -/
inductive Expr where
  | lit (v : Word)
  | index | left | right
  | local (slot : Nat)
  | reg (slot : Nat)
  | add (a b : Expr) | sub (a b : Expr) | mul (a b : Expr) | div (a b : Expr)
  | read (array : Nat) (address : Expr)
  | readNat (array offset : Nat)
  | select (condition yes no : Expr)
  deriving Repr

def Expr.neg (e : Expr) : Expr := .sub (.lit 0) e

def Expr.eval (i x y : Word) (s : State) (ls : List Word) : Expr → Option Word
  | .lit v => some v
  | .index => some i
  | .left => some x
  | .right => some y
  | .local n => ls[n]?
  | .reg n => some (s.regs n)
  | .add a b => do return (← a.eval i x y s ls) + (← b.eval i x y s ls)
  | .sub a b => do return (← a.eval i x y s ls) - (← b.eval i x y s ls)
  | .mul a b => do return (← a.eval i x y s ls) * (← b.eval i x y s ls)
  | .div a b => do return (← a.eval i x y s ls) / (← b.eval i x y s ls)
  | .read a j => do (s.arrays a)[(← j.eval i x y s ls).toNat]?
  | .readNat a n => (s.arrays a)[n]?
  | .select c a b => do
    if (← c.eval i x y s ls) != 0 then a.eval i x y s ls else b.eval i x y s ls

def Expr.lower : Expr → ReadCode
  | .lit v => .pure (.lit (encode v))
  | .index => .pure (wrap .index)
  | .left => .pure .left
  | .right => .pure .right
  | .local n => .pure (.local n)
  | .reg n => .register n
  | .add a b => .bind a.lower (.bind b.lower (.pure (HybridWord.add (.temp 1) (.temp 0))))
  | .sub a b => .bind a.lower (.bind b.lower (.pure (HybridWord.sub (.temp 1) (.temp 0))))
  | .mul a b => .bind a.lower (.bind b.lower (.pure (HybridWord.mul (.temp 1) (.temp 0))))
  | .div a b => .bind a.lower (.bind b.lower (.pure (udiv (.temp 1) (.temp 0))))
  | .read a j => .bind j.lower (.memory a (.temp 0))
  | .readNat a n => .memory a (.lit (Int.ofNat n))
  | .select c a b => .bind c.lower (.branch (.temp 0) a.lower b.lower)

theorem encode_eq_zero (w : Word) : encode w = 0 ↔ w = 0 := by
  simp [encode, BitVec.toNat_eq]

/-- General translation theorem, including failing reads and short-circuit branches. -/
theorem Expr.lower_correct_int (e : Expr) (i : Int) (x y : Word) (s : State)
    (ls : List Word) (ts : List Int) :
    e.lower.eval i (encode x) (encode y) s.encode (ls.map encode) ts =
      (e.eval (BitVec.ofInt 32 i) x y s ls).map encode := by
  induction e generalizing ts with
  | lit | left | right | reg => rfl
  | index => simp [lower, ReadCode.eval, wrap_correct, Value.eval, eval]
  | «local» => simp [lower, ReadCode.eval, Value.eval, eval, List.getElem?_map]
  | readNat a n =>
    simp [lower, ReadCode.eval, Value.eval, eval, State.encode,
      Int.not_lt_of_ge (Int.natCast_nonneg _), Array.getElem?_map]
  | add a b ha hb | sub a b ha hb | mul a b ha hb | div a b ha hb =>
    simp only [lower, ReadCode.eval, ha, hb, eval]
    cases a.eval (BitVec.ofInt 32 i) x y s ls <;> cases b.eval (BitVec.ofInt 32 i) x y s ls <;>
      simp [HybridWord.add, HybridWord.sub, HybridWord.mul, udiv, wrap_correct, Value.eval,
        ← encode_add, ← encode_sub, ← encode_mul, encode_udiv]
  | read a j hj =>
    simp only [lower, ReadCode.eval, hj, eval]
    cases j.eval (BitVec.ofInt 32 i) x y s ls <;>
      simp [Value.eval, State.encode, encode, Array.getElem?_map, Int.not_lt_of_ge (Int.natCast_nonneg _)]
  | select c a b hc ha hb =>
    simp only [lower, ReadCode.eval, hc, ha, hb, eval]
    cases c.eval (BitVec.ofInt 32 i) x y s ls <;> simp [Value.eval, encode_eq_zero]
    split <;> rfl

theorem Expr.lower_correct (e : Expr) (i x y : Word) (s : State)
    (ls : List Word) (ts : List Int) :
    e.lower.eval (encode i) (encode x) (encode y) s.encode (ls.map encode) ts =
      (e.eval i x y s ls).map encode := by
  simpa only [decode_encode] using e.lower_correct_int (encode i) x y s ls ts

end IRComparison.HybridWord
