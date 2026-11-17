import IRComparison.Circuit.SystemVerilog.ExpressionSound

namespace IRComparison.Circuit.SystemVerilog

/-- Bounds for the extra unit used to correct native truncating division.
The original operand widths, rather than the larger working words, give
room for both corrections, even for minimum-signed / -1. -/
theorem division_corrections_fit (a : BitVec wa) (b : BitVec wb) :
    (BitVec.ofInt (wa+wb+2) (a.toInt.tdiv b.toInt - 1)).toInt = a.toInt.tdiv b.toInt - 1 ∧
    (BitVec.ofInt (wa+wb+2) (a.toInt.tdiv b.toInt + 1)).toInt = a.toInt.tdiv b.toInt + 1 := by
  have bound := (wide_inputs (signed_magnitude a) (signed_magnitude b)).1
  have quotient := Int.natAbs_tdiv_le_natAbs a.toInt b.toInt
  have subBound := Int.natAbs_sub_le (a.toInt.tdiv b.toInt) 1
  have addBound := Int.natAbs_add_le (a.toInt.tdiv b.toInt) 1
  constructor <;> apply ofInt_signed_preserves (by omega) <;>
    simp only [show wa+wb+2-1 = wa+wb+1 by omega,Int.natAbs_one] at * <;> omega

/-- The actual nested SystemVerilog division AST implements Lean's Euclidean
division on every operand bit pattern, including a zero divisor. Guards are
proved with lazy branch evaluation, so no undefined native division is used. -/
theorem division_meaning (a : BitVec wa) (b : BitVec wb)
    (left : SignedMeaning env x (wa+wb+2) a.toInt)
    (right : SignedMeaning env y (wa+wb+2) b.toInt) :
    SignedMeaning env (division x y) (wa+wb+2) (a.toInt / b.toInt) := by
  let w := wa+wb+2
  have w2 : 2 ≤ w := by omega
  have zero := SignedMeaning.integer (env:=env) 0
  have one := SignedMeaning.integer (env:=env) 1
  change SignedMeaning env (.integer 0) 2 0 at zero
  change SignedMeaning env (.integer 1) 2 1 at one
  have qt : (Expr.binary .div x y).type env = ⟨w,true⟩ := by
    simp [Expr.type,left.typed,right.typed,Operator.comparison,IntegralType.join,w]
  have minusType : (Expr.binary .sub (.binary .div x y) (.integer 1)).type env = ⟨w,true⟩ := by
    change (Expr.type env (.binary .div x y)).join (Expr.type env (.integer 1)) = _
    rw [qt,one.typed]
    simp [IntegralType.join,Nat.max_eq_left w2]
  have plusType : (Expr.binary .add (.binary .div x y) (.integer 1)).type env = ⟨w,true⟩ := by
    change (Expr.type env (.binary .div x y)).join (Expr.type env (.integer 1)) = _
    rw [qt,one.typed]
    simp [IntegralType.join,Nat.max_eq_left w2]
  have innerType : (Expr.select (.binary .lt (.integer 0) y)
      (.binary .sub (.binary .div x y) (.integer 1))
      (.binary .add (.binary .div x y) (.integer 1))).type env = ⟨w,true⟩ := by
    change (Expr.type env _).join (Expr.type env _) = _
    rw [minusType,plusType]
    simp [IntegralType.join]
  have bodyType : (Expr.select
      (.binary .and (.binary .lt x (.integer 0)) (.binary .ne (.binary .mod x y) (.integer 0)))
      (.select (.binary .lt (.integer 0) y)
        (.binary .sub (.binary .div x y) (.integer 1))
        (.binary .add (.binary .div x y) (.integer 1)))
      (.binary .div x y)).type env = ⟨w,true⟩ := by
    change (Expr.type env _).join (Expr.type env _) = _
    rw [innerType,qt]
    simp [IntegralType.join]
  have zeroTest := right.comparison zero (op:=.eq) rfl
    (result:=decide (b.toInt = 0)) (by simp [arithmetic])
  unfold division
  by_cases isZero : b.toInt = 0
  · have result := SignedMeaning.select_true zeroTest (by simp [isZero]) zero bodyType
    simpa [isZero,Nat.max_eq_right w2,w] using result
  · have qCompute : arithmetic .div a.toInt b.toInt = some (a.toInt.tdiv b.toInt) := by simp [arithmetic,isZero]
    have rCompute : arithmetic .mod a.toInt b.toInt = some (a.toInt.tmod b.toInt) := by simp [arithmetic,isZero]
    have quotient := left.binary right (op:=.div) rfl (by decide) qCompute (arithmetic_working_width a b qCompute)
    have remainder := left.binary right (op:=.mod) rfl (by decide) rCompute (arithmetic_working_width a b rCompute)
    have correctionFits := division_corrections_fit a b
    have minus := quotient.binary_join one (op:=.sub) rfl (by decide) rfl
      (by simpa [Nat.max_eq_left w2,w] using correctionFits.1)
    have plus := quotient.binary_join one (op:=.add) rfl (by decide) rfl
      (by simpa [Nat.max_eq_left w2,w] using correctionFits.2)
    have minus' : SignedMeaning env (.binary .sub (.binary .div x y) (.integer 1)) w
        (a.toInt.tdiv b.toInt-1) := by simpa [Nat.max_eq_left w2,w] using minus
    have plus' : SignedMeaning env (.binary .add (.binary .div x y) (.integer 1)) w
        (a.toInt.tdiv b.toInt+1) := by simpa [Nat.max_eq_left w2,w] using plus
    have positiveTest := zero.comparison right (op:=.lt) rfl
      (result:=decide (0 < b.toInt)) (by simp [arithmetic])
    have corrected := SignedMeaning.select_bool positiveTest minusType plusType
      (fun _ => minus') (fun _ => plus')
    simp only [Nat.max_self,decide_eq_true_eq] at corrected
    have signTest := left.comparison zero (op:=.lt) rfl
      (result:=decide (a.toInt < 0)) (by simp [arithmetic])
    have remainderTest := remainder.comparison zero (op:=.ne) rfl
      (result:=decide (a.toInt.tmod b.toInt ≠ 0)) (by simp [arithmetic])
    have correctionTest := and_self signTest (fun _ => remainderTest)
    have body := SignedMeaning.select_bool correctionTest innerType qt
      (fun _ => corrected) (fun _ => quotient)
    have result := SignedMeaning.select_false zeroTest (by simp [isZero]) zero.typed body
    simpa only [Nat.max_self,Nat.max_eq_right w2,Bool.and_eq_true,decide_eq_true_eq,
      ← verilogDivision_correct,verilogDivision,if_neg isZero] using result

end IRComparison.Circuit.SystemVerilog
