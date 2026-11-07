import IRComparison.Circuit.Emit

namespace IRComparison.Circuit

def Interval.Contains (r : Interval) (v : Int) : Prop := r.lo ≤ v ∧ v ≤ r.hi
def Interval.magnitude (r : Interval) : Nat := max r.lo.natAbs r.hi.natAbs

theorem Interval.abs_bound {r : Interval} {v : Int} (h : r.Contains v) : v.natAbs ≤ r.magnitude := by
  have hlo := Int.le_natAbs (a := -r.lo)
  have hhi := Int.le_natAbs (a := r.hi)
  simp only [Int.natAbs_neg] at hlo
  unfold Contains at h
  unfold magnitude
  rcases Int.natAbs_eq v with hp | hn <;> omega

theorem abs_range {v : Int} {n : Nat} (h : v.natAbs ≤ n) : -(n:Int) ≤ v ∧ v ≤ (n:Int) := by
  have h1 := Int.le_natAbs (a:=v)
  have h2 := Int.le_natAbs (a:= -v)
  simp only [Int.natAbs_neg] at h2
  omega

theorem bits_fits (n : Nat) : n < 2 ^ bits n := by
  have h := Nat.lt_log2_self (n:=n)
  have he : bits n = n.log2+1 := by simp [bits]
  simpa [he] using h

theorem signedWidth_preserves (h : r.Contains v) :
    (BitVec.ofInt (signedWidth r) v).toInt = v := by
  have hb := bits_fits r.magnitude
  have ha := abs_range (r.abs_bound h)
  have hc : (r.magnitude : Int) < (2:Int)^bits r.magnitude := by
    have hc' : (r.magnitude : Int) < ((2^bits r.magnitude : Nat) : Int) := by omega
    simpa only [Int.natCast_pow] using hc'
  apply BitVec.toInt_ofInt_eq_self (by unfold signedWidth; omega)
  · simpa only [signedWidth,Nat.add_sub_cancel,Interval.magnitude] using
      (show -(2:Int)^bits r.magnitude ≤ v from by omega)
  · simpa only [signedWidth,Nat.add_sub_cancel,Interval.magnitude] using
      (show v < (2:Int)^bits r.magnitude from by omega)

theorem wrapped_correct (h : wrapped? e = some a) :
    e.eval s w = (a.eval s w).map (fun v => v % 4294967296) := by
  unfold wrapped? at h
  split at h
  · split at h
    · rename_i eq
      simp only [beq_iff_eq] at eq
      subst eq
      cases h
      simp only [Expr.eval,Bin.eval]
      cases he : a.eval s w with
      | none => rfl
      | some v =>
        simp only [bind,Option.bind,Option.map_some]
        congr 1
        have hm := Int.emod_add_ediv_mul v 4294967296
        omega
    · cases h
  · cases h

theorem binRange_correct (op : Bin) (ha : u.Contains a) (hb : v.Contains b) :
    (binRange op u v).Contains (op.eval a b) := by
  cases op with
  | add | sub => simp only [binRange,Bin.eval,Interval.Contains] at *; omega
  | lt => simp only [binRange,Bin.eval,Interval.Contains]; split <;> omega
  | mul =>
      have h := Nat.mul_le_mul (u.abs_bound ha) (v.abs_bound hb)
      rw [← Int.natAbs_mul] at h
      exact abs_range h
  | div =>
      simp only [binRange]
      split
      · rename_i h
        have h' : 0 ≤ u.lo ∧ 0 ≤ v.lo := by simpa using h
        have hnon : 0 ≤ a := Int.le_trans h'.1 ha.1
        have hbnon : 0 ≤ b := Int.le_trans h'.2 hb.1
        have hn := Int.ediv_nonneg hnon hbnon
        have he := Int.ediv_le_self b hnon
        simp only [Interval.Contains,Bin.eval]
        have := ha.2
        omega
      · apply abs_range
        exact Nat.le_trans (Int.natAbs_ediv_le_natAbs a b) (Nat.le_trans (u.abs_bound ha) (Nat.le_succ _))

structure InputsBound (s : IRComparison.State) (w : Nat → Int) (wr : Nat → Interval) : Prop where
  wires : ∀ n, (wr n).Contains (w n)
  regs : ∀ n, wordRange.Contains (s.regs n)
  memory : ∀ a j v, arrayInput (s.arrays a) j = some v → wordRange.Contains v

theorem range_correct (e : Expr) (hb : InputsBound s w wr) (he : e.eval s w = some v) :
    (range wr e).Contains v := by
  induction e generalizing v with
  | fail => cases he
  | lit n => cases he; simp [range,wrapped?,Interval.Contains]
  | wire n => cases he; exact hb.wires n
  | reg n => cases he; exact hb.regs n
  | memory a j ih =>
      simp only [Expr.eval] at he
      cases hj : j.eval s w with
      | none => simp [hj] at he
      | some k =>
          simp only [hj,bind,Option.bind] at he
          exact hb.memory a k v he
  | natIndex a ih =>
      simp only [Expr.eval] at he
      cases hx : a.eval s w with
      | none => simp [hx] at he
      | some x =>
          simp only [hx,bind,Option.bind] at he
          have he' : Int.ofNat x.toNat = v := Option.some.inj he
          change (x.toNat : Int) = v at he'
          have ha := ih hx
          change max 0 (range wr a).lo ≤ v ∧ v ≤ max 0 (range wr a).hi
          unfold Interval.Contains at ha
          by_cases hn : 0 ≤ x
          · have := Int.toNat_of_nonneg hn; omega
          · have := Int.toNat_of_nonpos (by omega : x ≤ 0); omega
  | seq a b ha hb' =>
      cases hx : a.eval s w with
      | none => simp [Expr.eval,hx] at he
      | some x =>
          simp only [Expr.eval,hx,Option.bind_some] at he
          exact hb' he
  | select c a b hc ha hb' =>
      simp only [Expr.eval] at he
      cases hx : c.eval s w with
      | none => simp [hx] at he
      | some x =>
          simp only [hx,bind,Option.bind] at he
          simp only [range,wrapped?,Option.isSome_none,Bool.false_eq_true,↓reduceIte,union,Interval.Contains]
          split at he
          · have := ha he; unfold Interval.Contains at this; omega
          · have := hb' he; unfold Interval.Contains at this; omega
  | bin op a b ha hb' =>
      cases hw : wrapped? (.bin op a b) with
      | some inner =>
          rw [wrapped_correct hw] at he
          cases hi : inner.eval s w with
          | none => simp [hi] at he
          | some z =>
              simp only [hi,Option.map_some,Option.some.injEq] at he
              rw [range,hw]
              simp only [Option.isSome_some,↓reduceIte,wordRange,Interval.Contains]
              have h0 := Int.emod_nonneg z (by decide : (4294967296:Int) ≠ 0)
              have h1 := Int.emod_lt_of_pos z (by decide : (0:Int) < 4294967296)
              omega
      | none =>
          simp only [Expr.eval] at he
          cases hx : a.eval s w with
          | none => simp [hx] at he
          | some x =>
            cases hy : b.eval s w with
            | none => simp [hx,hy] at he
            | some y =>
              simp only [hx,hy,bind,Option.bind] at he
              have he' : op.eval x y = v := Option.some.inj he
              subst v
              rw [range,hw]
              exact binRange_correct op (ha hx) (hb' hy)

theorem expression_width_preserves (e : Expr) (hb : InputsBound s w wr)
    (he : e.eval s w = some v) :
    (BitVec.ofInt (signedWidth (range wr e)) v).toInt = v :=
  signedWidth_preserves (range_correct e hb he)

end IRComparison.Circuit
