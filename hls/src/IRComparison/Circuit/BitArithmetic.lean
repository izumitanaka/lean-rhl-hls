import IRComparison.Circuit.Width

namespace IRComparison.Circuit

/-- Verilog signed division truncates towards zero. Explicit correction gives
Lean's Euclidean division, including zero divisor. -/
def verilogDivision (a b : Int) : Int :=
  if b = 0 then 0 else
    if a < 0 ∧ a.tmod b ≠ 0 then
      if 0 < b then a.tdiv b - 1 else a.tdiv b + 1
    else a.tdiv b

theorem verilogDivision_correct (a b : Int) : verilogDivision a b = a / b := by
  unfold verilogDivision
  by_cases hz : b = 0
  · simp [hz]
  · rw [if_neg hz,Int.ediv_eq_tdiv]
    by_cases hn : 0 ≤ a
    · simp [hn,show ¬ a < 0 from by omega]
    · by_cases hd : b ∣ a
      · simp [hd,Int.tmod_eq_zero_of_dvd hd]
      · have hm : a.tmod b ≠ 0 := fun h => hd (Int.dvd_of_tmod_eq_zero h)
        simp only [show a < 0 from by omega,↓reduceIte,hn,hd,or_self]
        by_cases hb : 0 < b
        · simp [hm,hb,Int.sign_eq_one_of_pos hb]
        · simp [hm,hb,Int.sign_eq_neg_one_of_neg (by omega : b < 0)]

def hardwareBin : Bin → Int → Int → Int
  | .div => verilogDivision
  | op => op.eval

theorem hardwareBin_correct (op : Bin) : hardwareBin op a b = op.eval a b := by
  cases op <;> try rfl
  exact verilogDivision_correct _ _

/-- Bitvector interpretation at every combinational node, with the widths
chosen by the backend. InvariantSound supplies the sequential invariant; BitMachine composes
this result over arbitrarily many clock cycles. -/
def Expr.bitEval (wr : Nat → Interval) (s : IRComparison.State) (w : Nat → Int) (e : Expr) : Option Int :=
  let raw := match e with
    | .fail => none
    | .lit n => some n
    | .wire n => some (w n)
    | .reg n => some (s.regs n)
    | .memory a j => do arrayInput (s.arrays a) (← j.bitEval wr s w)
    | .natIndex a => do return Int.ofNat (← a.bitEval wr s w).toNat
    | .bin op a b => do return hardwareBin op (← a.bitEval wr s w) (← b.bitEval wr s w)
    | .select c a b => do
        if (← c.bitEval wr s w) != 0 then a.bitEval wr s w else b.bitEval wr s w
    | .seq a b => (a.bitEval wr s w).bind fun _ => b.bitEval wr s w
  raw.map (fun n => (BitVec.ofInt (signedWidth (range wr e)) n).toInt)

theorem Expr.bitEval_correct (e : Expr) (h : InputsBound s w wr) :
    e.bitEval wr s w = e.eval s w := by
  induction e with
  | fail => rfl
  | lit n | wire n | reg n =>
      unfold bitEval
      simp only [Option.map_some]
      congr 1
      exact expression_width_preserves _ h rfl
  | memory a j ih =>
      simp only [bitEval,ih]
      change ((Expr.memory a j).eval s w).map _ = _
      cases he : (Expr.memory a j).eval s w with
      | none => rfl
      | some v => exact congrArg some (expression_width_preserves _ h he)
  | natIndex a ih =>
      simp only [bitEval,ih]
      change ((Expr.natIndex a).eval s w).map _ = _
      cases he : (Expr.natIndex a).eval s w with
      | none => rfl
      | some v => exact congrArg some (expression_width_preserves _ h he)
  | bin op a b ha hb =>
      simp only [bitEval,ha,hb,hardwareBin_correct]
      change ((Expr.bin op a b).eval s w).map _ = _
      cases he : (Expr.bin op a b).eval s w with
      | none => rfl
      | some v => exact congrArg some (expression_width_preserves _ h he)
  | select c a b hc ha hb =>
      simp only [bitEval,hc,ha,hb]
      change ((Expr.select c a b).eval s w).map _ = _
      cases he : (Expr.select c a b).eval s w with
      | none => rfl
      | some v => exact congrArg some (expression_width_preserves _ h he)
  | seq a b ha hb =>
      simp only [bitEval,ha,hb]
      change ((Expr.seq a b).eval s w).map _ = _
      cases he : (Expr.seq a b).eval s w with
      | none => rfl
      | some v => exact congrArg some (expression_width_preserves _ h he)

theorem wrapped_low_bits (h : wrapped? e = some a) :
    e.eval s w = (a.eval s w).map (fun z => ((BitVec.ofInt 32 z).toNat : Int)) := by
  rw [wrapped_correct h]
  congr 1
  funext z
  simpa [HybridWord.encode,HybridWord.modulus] using (HybridWord.encode_ofInt z).symm

end IRComparison.Circuit
