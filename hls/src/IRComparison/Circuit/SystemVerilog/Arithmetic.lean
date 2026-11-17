import IRComparison.Circuit.SystemVerilog.Eval
import IRComparison.Circuit.BitArithmetic

namespace IRComparison.Circuit.SystemVerilog

theorem signed_magnitude (v : BitVec w) : v.toInt.natAbs < 2^w := by
  have lo := BitVec.le_two_mul_toInt (x:=v)
  have hi := BitVec.two_mul_toInt_lt (x:=v)
  have positive : (0:Int) < 2^w := Int.pow_pos (by decide)
  have cast : ((2^w : Nat) : Int) = (2:Int)^w := by simp
  rcases Int.natAbs_eq v.toInt with hp | hn <;> omega

theorem ofInt_signed_preserves (positive : 0 < w) (bound : n.natAbs < 2^(w-1)) :
    (Value.ofInt ⟨w,true⟩ n).integer = n := by
  change (BitVec.ofInt w n).toInt = n
  have cast : ((2^(w-1) : Nat) : Int) = (2:Int)^(w-1) := by simp
  have abs : -(2:Int)^(w-1) < n ∧ n < (2:Int)^(w-1) := by
    rcases Int.natAbs_eq n with hp | hn <;> omega
  exact BitVec.toInt_ofInt_eq_self positive (by omega) abs.2

theorem wide_inputs {a b : Int} (ha : a.natAbs < 2^wa) (hb : b.natAbs < 2^wb) :
    a.natAbs + b.natAbs + 1 < 2^(wa+wb+1) ∧
    (a*b).natAbs < 2^(wa+wb+1) := by
  have pa : 2^wa ≤ 2^(wa+wb) := Nat.pow_le_pow_right (by decide) (by omega)
  have pb : 2^wb ≤ 2^(wa+wb) := Nat.pow_le_pow_right (by decide) (by omega)
  have pp : 0 < 2^(wa+wb) := Nat.two_pow_pos _
  have mul : a.natAbs*b.natAbs < 2^wa*2^wb := Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.le_of_lt ha))
    (Nat.mul_lt_mul_of_pos_left hb (Nat.two_pow_pos _))
  rw [← Nat.pow_add] at mul
  simp only [Nat.pow_succ,Int.natAbs_mul]
  constructor <;> omega

theorem arithmetic_magnitude {a b : Int} (ha : a.natAbs < 2^wa) (hb : b.natAbs < 2^wb)
    (result : arithmetic op a b = some v) : v.natAbs < 2^(wa+wb+1) := by
  have bounds := wide_inputs ha hb
  have large : 1 < 2^(wa+wb+1) := by
    have := Nat.two_pow_pos (wa+wb)
    simp only [Nat.pow_succ]
    omega
  cases op with
  | add => cases result; exact Nat.lt_of_le_of_lt (Int.natAbs_add_le a b) (by omega)
  | sub => cases result; exact Nat.lt_of_le_of_lt (Int.natAbs_sub_le a b) (by omega)
  | mul => cases result; exact bounds.2
  | div =>
    simp only [arithmetic] at result
    split at result
    · cases result
    · cases result
      exact Nat.lt_of_le_of_lt (Int.natAbs_tdiv_le_natAbs a b) (by omega)
  | mod =>
    simp only [arithmetic] at result
    split at result
    · cases result
    · cases result
      rw [Int.natAbs_tmod]
      exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by omega)
  | lt | ge | eq | ne | and =>
    simp only [arithmetic] at result
    split at result <;> cases result <;> simp_all [Nat.two_pow_pos]

/-- The working width used by the real emitter is sufficient for native
arithmetic on both operand words, including multiplication and the signed
minimum divided by -1. No test-vector premise is involved. -/
theorem arithmetic_working_width (a : BitVec wa) (b : BitVec wb)
    (result : arithmetic op a.toInt b.toInt = some v) :
    (Value.ofInt ⟨wa+wb+2,true⟩ v).integer = v := by
  apply ofInt_signed_preserves (by omega)
  simpa using arithmetic_magnitude (signed_magnitude a) (signed_magnitude b) result

end IRComparison.Circuit.SystemVerilog
