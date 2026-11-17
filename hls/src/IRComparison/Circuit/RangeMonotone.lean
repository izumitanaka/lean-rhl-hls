import IRComparison.Circuit.WidenProgress
import IRComparison.Circuit.StorageShape

namespace IRComparison.Circuit

/-- A real interval, as opposed to an infeasible branch frame. -/
def Interval.Nonempty (r : Interval) : Prop := r.lo ≤ r.hi

variable {a b u v : Interval} {frame top : Frame} {wr small big : Nat → Interval}

theorem Interval.magnitude_mono (inside : a.Inside b) (nonempty : a.Nonempty) :
    a.magnitude ≤ b.magnitude := by
  have left : b.Contains a.lo := ⟨inside.1,Int.le_trans nonempty inside.2⟩
  have right : b.Contains a.hi := ⟨Int.le_trans inside.1 nonempty,inside.2⟩
  have hl := b.abs_bound left
  have hr := b.abs_bound right
  unfold magnitude at *
  omega

theorem binRange_nonempty (op : Bin) (a : u.Nonempty) (b : v.Nonempty) :
    (binRange op u v).Nonempty := by
  cases op with
  | add | sub => dsimp [binRange,Interval.Nonempty] at *; omega
  | mul =>
    have positive : 0 ≤ Int.ofNat (u.magnitude*v.magnitude) := Int.natCast_nonneg _
    change -Int.ofNat (u.magnitude*v.magnitude) ≤ Int.ofNat (u.magnitude*v.magnitude)
    omega
  | div =>
    simp only [binRange]
    split <;> simp only [Interval.Nonempty,Int.ofNat_eq_natCast] <;> omega
  | lt => change (0:Int) ≤ 1; decide

theorem binRange_mono (op : Bin) (ua : u.Inside a) (vb : v.Inside b)
    (un : u.Nonempty) (vn : v.Nonempty) :
    (binRange op u v).Inside (binRange op a b) := by
  have um := Interval.magnitude_mono ua un
  have vm := Interval.magnitude_mono vb vn
  cases op with
  | add | sub => dsimp [binRange,Interval.Inside] at *; constructor <;> omega
  | lt => exact ⟨Int.le_refl _,Int.le_refl _⟩
  | mul =>
    have product := Nat.mul_le_mul um vm
    change -(Int.ofNat (a.magnitude*b.magnitude)) ≤ -(Int.ofNat (u.magnitude*v.magnitude)) ∧
      Int.ofNat (u.magnitude*v.magnitude) ≤ Int.ofNat (a.magnitude*b.magnitude)
    simp only [Int.ofNat_eq_natCast]
    constructor <;> omega
  | div =>
    have endpoint := a.abs_bound (show a.Contains u.hi from ⟨Int.le_trans ua.1 un,ua.2⟩)
    have endpointInt := Int.le_natAbs (a := u.hi)
    dsimp [binRange,Interval.Inside]
    unfold Interval.Inside at ua vb
    unfold Interval.magnitude at um vm endpoint
    repeat' split
    all_goals simp only [Bool.and_eq_true,decide_eq_true_eq] at *
    all_goals (try dsimp only)
    all_goals try simp only [Int.ofNat_eq_natCast]
    all_goals constructor <;> omega

theorem range_nonempty (wires : ∀ n, (wr n).Nonempty) (e : Expr) : (range wr e).Nonempty := by
  induction e with
  | fail | lit => simp [range,wrapped?,Interval.Nonempty]
  | wire n => exact wires n
  | reg | memory | wrap32 => exact (by change (0:Int) ≤ 4294967295; decide)
  | natIndex a ih => change max 0 (range wr a).lo ≤ max 0 (range wr a).hi; unfold Interval.Nonempty at ih; omega
  | seq a b ha hb => exact hb
  | select c a b hc ha hb =>
    change min (range wr a).lo (range wr b).lo ≤ max (range wr a).hi (range wr b).hi
    unfold Interval.Nonempty at *
    omega
  | bin op a b ha hb =>
    by_cases wrapped : (wrapped? (.bin op a b)).isSome = true
    · simp only [range,wrapped,↓reduceIte]; exact (by change (0:Int) ≤ 4294967295; decide)
    · simp only [range,wrapped]
      exact binRange_nonempty op ha hb

/-- Refining reachable frames cannot enlarge an expression range. This is
used for captured values whose holding widths were chosen before refinement. -/
theorem range_mono (inside : ∀ n, (small n).Inside (big n))
    (nonempty : ∀ n, (small n).Nonempty) (e : Expr) :
    (range small e).Inside (range big e) := by
  induction e with
  | fail | lit | reg | memory | wrap32 => exact ⟨Int.le_refl _,Int.le_refl _⟩
  | wire n => exact inside n
  | seq a b ha hb => exact hb
  | natIndex a ih =>
    change max 0 (range big a).lo ≤ max 0 (range small a).lo ∧
      max 0 (range small a).hi ≤ max 0 (range big a).hi
    unfold Interval.Inside at ih
    constructor <;> omega
  | select c a b hc ha hb =>
    change min (range big a).lo (range big b).lo ≤ min (range small a).lo (range small b).lo ∧
      max (range small a).hi (range small b).hi ≤ max (range big a).hi (range big b).hi
    unfold Interval.Inside at ha hb
    constructor <;> omega
  | bin op a b ha hb =>
    by_cases wrapped : (wrapped? (.bin op a b)).isSome = true
    · simp only [range,wrapped,↓reduceIte]; exact ⟨Int.le_refl _,Int.le_refl _⟩
    · simp only [range,wrapped]
      exact binRange_mono op ha hb (range_nonempty nonempty a) (range_nonempty nonempty b)

/-- Adding fresh holding registers cannot change the range chosen for an
expression that refers only to the previous declarations. -/
theorem Expr.range_agrees (e : Expr) (scope : e.inStorage shape)
    (same : ∀ n, n < shape.wires.size → small n = big n) : range small e = range big e := by
  induction e with
  | fail | lit | reg | memory | wrap32 => rfl
  | wire n => exact same n scope
  | seq a b ha hb => exact hb scope.2
  | natIndex a ih => change _ = _; simp only [range,wrapped?,Option.isSome_none,Bool.false_eq_true,↓reduceIte,ih scope]
  | select c a b hc ha hb =>
    change union (range small a) (range small b) = union (range big a) (range big b)
    rw [ha scope.2.1,hb scope.2.2]
  | bin op a b ha hb =>
    by_cases wrapped : (wrapped? (.bin op a b)).isSome = true
    · simp only [range,wrapped,↓reduceIte]
    · simp only [range,wrapped,ha scope.1,hb scope.2]

theorem Frame.get_nonempty (h : frame.empty = false) (n : Nat) : (frame.get n).Nonempty := by
  cases found : frame[n]? with
  | none => simp [Frame.get,found,zeroRange,Interval.Nonempty]
  | some r =>
    have mem := List.mem_of_getElem? found
    have all : ∀ r ∈ frame, ¬ r.hi < r.lo := by simpa [Frame.empty,List.any_eq_false] using h
    simpa [Frame.get,found,Interval.Nonempty] using (Int.le_of_not_gt (all r mem))

theorem Frame.range_inside (fits : frame.within top = true) (nonempty : frame.empty = false) (e : Expr) :
    (range frame.get e).Inside (range top.get e) :=
  range_mono (Frame.within_get fits) (Frame.get_nonempty nonempty) e

/-- A holding-register allocation made from the global expression range
remains sufficient in every nonempty refined frame. -/
theorem transfer_wire_inside (fits : frame.within top = true)
    (valid : k < frame.length) (allocated : (range top.get e).Inside (top.get k)) (next : Nat) :
    ∃ edges, transfer frame (.wire k e next) = .ok edges ∧
      ∀ edge ∈ edges, edge.2.within top = true := by
  by_cases empty : frame.empty = true
  · exact ⟨[],by simp [transfer,empty,pure,Except.pure],by simp⟩
  · have smaller := Frame.range_inside fits (Bool.eq_false_iff.mpr empty) e
    have within : (range frame.get e).Inside (top.get k) :=
      ⟨Int.le_trans allocated.1 smaller.1,Int.le_trans smaller.2 allocated.2⟩
    refine ⟨[(next,frame.set k (range frame.get e))],?_,?_⟩
    · simp [transfer,empty,valid,pure,Except.pure,bind,Except.bind]
    · intro edge member
      rcases List.mem_singleton.mp member with rfl
      exact Frame.set_within fits within

end IRComparison.Circuit
