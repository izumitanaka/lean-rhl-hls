import IRComparison.Hybrid.HybridWord

namespace IRComparison.HybridWord

/-- Number of iterations of an exclusive signed range. A zero step gives an
empty range; HLS's static input contract requires a positive or negative step. -/
def rangeCount (start stop stride : Int) : Nat :=
  if 0 < stride then ((stop-start).toNat + stride.toNat - 1) / stride.toNat
  else if stride < 0 then ((start-stop).toNat + (-stride).toNat - 1) / (-stride).toNat
  else 0

/-- Ordinary executable Lean range. The range arithmetic is mathematical Int;
indices passed to the BV32 body use the same conversion as existing kernels. -/
def range (start stop stride : Int) : List Word :=
  (List.range (rangeCount start stop stride)).map
    (fun (k : Nat) => BitVec.ofInt 32 (start + (k : Int) * stride))

private theorem ceil_member (distance step k : Nat) (positive : 0 < step) :
    k < (distance + step - 1) / step ↔ k * step < distance := by
  rw [Nat.lt_div_iff_mul_lt positive]
  have h : distance + step - 1 - (step - 1) = distance := by omega
  rw [h]

theorem rangeCount_positive (positive : 0 < stride) :
    k < rangeCount start stop stride ↔ start + (k : Int) * stride < stop := by
  rw [rangeCount,if_pos positive,ceil_member _ _ _ (by omega)]
  have hs : (stride.toNat : Int) = stride := by omega
  have hmul : ((k * stride.toNat : Nat) : Int) = (k : Int) * stride := by
    simp only [Int.natCast_mul,hs]
  omega

theorem rangeCount_negative (negative : stride < 0) :
    k < rangeCount start stop stride ↔ stop < start + (k : Int) * stride := by
  rw [rangeCount,if_neg (by omega),if_pos negative,ceil_member _ _ _ (by omega)]
  have hs : ((-stride).toNat : Int) = -stride := by omega
  have hmul : ((k * (-stride).toNat : Nat) : Int) = -((k : Int) * stride) := by
    simp only [Int.natCast_mul,hs,Int.mul_neg]
  omega

theorem range_length : (range start stop stride).length = rangeCount start stop stride := by
  simp [range]

end IRComparison.HybridWord
