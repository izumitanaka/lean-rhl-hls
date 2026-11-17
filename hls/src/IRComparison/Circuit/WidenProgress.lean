import IRComparison.Circuit.Invariant

/-! Finite progress of threshold widening while frames stay within the declared
wire ranges. This does not assume that arbitrary source lowering has that property. -/
namespace IRComparison.Circuit

/-- Remaining threshold changes: one for the lower endpoint, two for the upper. -/
def Interval.widenBudget (top old : Interval) : Nat :=
  (if top.lo < old.lo then 1 else 0) +
  (if old.hi < top.hi-1 then 2 else if old.hi < top.hi then 1 else 0)

def Interval.Inside (r top : Interval) : Prop := top.lo ≤ r.lo ∧ r.hi ≤ top.hi

def Interval.widen (top old incoming : Interval) : Interval :=
  let joined := union old incoming
  ⟨if joined.lo < old.lo then min top.lo joined.lo else old.lo,
    if old.hi < joined.hi then
      if joined.hi ≤ top.hi-1 then max joined.hi (top.hi-1) else max joined.hi top.hi
    else old.hi⟩

section IntervalFacts
variable {top old incoming : Interval}

theorem Interval.widenBudget_le (top old : Interval) : top.widenBudget old ≤ 3 := by
  unfold widenBudget
  repeat' split
  all_goals omega

theorem Interval.widen_inside (oldFits : old.Inside top) (incomingFits : incoming.Inside top) :
    (top.widen old incoming).Inside top := by
  rcases oldFits with ⟨ol,oh⟩
  rcases incomingFits with ⟨il,ih⟩
  dsimp [widen,Inside,union]
  repeat' split
  all_goals constructor <;> omega

theorem Interval.widen_contains_old (top old incoming : Interval) :
    old.Inside (top.widen old incoming) := by
  dsimp [widen,Inside,union]
  repeat' split
  all_goals constructor <;> omega

theorem Interval.widen_contains_incoming (top old incoming : Interval) :
    incoming.Inside (top.widen old incoming) := by
  dsimp [widen,Inside,union]
  repeat' split
  all_goals constructor <;> omega

/-- The predecessor threshold preserves the strict upper bound needed by a
loop increment, even after predecessors are joined. -/
theorem Interval.widen_below (oldBound : old.hi < top.hi) (incomingBound : incoming.hi < top.hi) :
    (top.widen old incoming).hi < top.hi := by
  dsimp [widen,union]
  repeat' split
  all_goals omega

theorem Interval.widenBudget_mono (oldFits : old.Inside top) (incomingFits : incoming.Inside top) :
    top.widenBudget (top.widen old incoming) ≤ top.widenBudget old := by
  rcases oldFits with ⟨ol,oh⟩
  rcases incomingFits with ⟨il,ih⟩
  dsimp [widenBudget,widen,union]
  repeat' split
  all_goals omega

/-- Every actual change consumes at least one of the three endpoint thresholds. -/
theorem Interval.widenBudget_lt (oldFits : old.Inside top) (incomingFits : incoming.Inside top)
    (changed : ¬ incoming.Inside old) :
    top.widenBudget (top.widen old incoming) < top.widenBudget old := by
  rcases oldFits with ⟨ol,oh⟩
  rcases incomingFits with ⟨il,ih⟩
  unfold Inside at changed
  dsimp [widenBudget,widen,union]
  repeat' split
  all_goals omega

end IntervalFacts

def Frame.widenBudget : Frame → Frame → Nat
  | top::tops,old::olds => top.widenBudget old + widenBudget tops olds
  | _,_ => 0

theorem Frame.widenBudget_le (tops olds : Frame) : tops.widenBudget olds ≤ 3*tops.length := by
  induction tops generalizing olds with
  | nil => simp [widenBudget]
  | cons top tops ih =>
    cases olds with
    | nil => simp [widenBudget]
    | cons old olds =>
      have first := top.widenBudget_le old
      have rest := ih olds
      simp only [widenBudget,List.length_cons]
      omega

theorem Frame.within_cons : within (r::rs) (t::ts) = true ↔ r.Inside t ∧ within rs ts = true := by
  simp [within,Interval.Inside]

theorem Frame.within_length (h : within xs ys = true) : xs.length = ys.length := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [within]
  | cons x xs ih => cases ys with
    | nil => simp [within] at h
    | cons y ys =>
      have rest := ih (within_cons.mp h).2
      simp [rest]

theorem Frame.within_refl (frame : Frame) : within frame frame = true := by
  induction frame with
  | nil => rfl
  | cons r rs ih => exact within_cons.mpr ⟨⟨Int.le_refl _,Int.le_refl _⟩,ih⟩

theorem Frame.within_trans (ab : within a b = true) (bc : within b c = true) :
    within a c = true := by
  induction a generalizing b c with
  | nil => cases b <;> cases c <;> simp_all [within]
  | cons a as ih =>
    cases b with
    | nil => cases ab
    | cons b bs =>
      cases c with
      | nil => cases bc
      | cons c cs =>
        have h := within_cons.mp ab
        have k := within_cons.mp bc
        exact within_cons.mpr ⟨⟨Int.le_trans k.1.1 h.1.1,Int.le_trans h.1.2 k.1.2⟩,ih h.2 k.2⟩

theorem Frame.within_get (fits : within a b = true) (n : Nat) :
    (a.get n).Inside (b.get n) := by
  induction a generalizing b n with
  | nil =>
    cases b with
    | nil => exact ⟨Int.le_refl _,Int.le_refl _⟩
    | cons => cases fits
  | cons r rs ih =>
    cases b with
    | nil => cases fits
    | cons s ss =>
      cases n with
      | zero => exact (within_cons.mp fits).1
      | succ n => exact ih (within_cons.mp fits).2 n

theorem Frame.set_within {value : Interval} (fits : within frame top = true) (valueFits : value.Inside (top.get n)) :
    within (frame.set n value) top = true := by
  induction frame generalizing top n with
  | nil => cases top <;> simp_all [within]
  | cons r rs ih =>
    cases top with
    | nil => cases fits
    | cons t ts =>
      have h := within_cons.mp fits
      cases n with
      | zero => exact within_cons.mpr ⟨valueFits,h.2⟩
      | succ n => exact within_cons.mpr ⟨h.1,ih h.2 valueFits⟩

theorem Frame.refine_within (frame : Frame) (condition : Expr) (yes : Bool) :
    within (frame.refine condition yes) frame = true := by
  unfold refine
  split
  · apply set_within (within_refl frame)
    cases yes <;> simp only [Bool.false_eq_true,↓reduceIte,Interval.Inside]
    all_goals constructor <;> omega
  · exact within_refl frame

theorem Frame.widen_merge_cons :
    widen (top::tops) (old::olds) (merge (old::olds) (incoming::rest)) =
      top.widen old incoming :: widen tops olds (merge olds rest) := rfl

theorem Frame.widen_get (oldFits : within olds tops = true) (incomingFits : within incoming tops = true)
    (n : Nat) :
    (widen tops olds (merge olds incoming)).get n = (tops.get n).widen (olds.get n) (incoming.get n) := by
  induction tops generalizing olds incoming n with
  | nil =>
    cases olds <;> cases incoming <;> simp_all [within,widen,merge,get,zeroRange,Interval.widen,union]
  | cons top tops ih =>
    cases olds with
    | nil => cases oldFits
    | cons old olds =>
      cases incoming with
      | nil => cases incomingFits
      | cons next rest =>
        cases n with
        | zero => rfl
        | succ n => exact ih (within_cons.mp oldFits).2 (within_cons.mp incomingFits).2 n

theorem Frame.widen_get_below (oldFits : within olds tops = true) (incomingFits : within incoming tops = true)
    (oldBound : (olds.get n).hi < (tops.get n).hi) (incomingBound : (incoming.get n).hi < (tops.get n).hi) :
    ((widen tops olds (merge olds incoming)).get n).hi < (tops.get n).hi := by
  rw [widen_get oldFits incomingFits]
  exact Interval.widen_below oldBound incomingBound

/-- The executable widening remains within the declared frame and covers both
predecessor frames. -/
theorem Frame.widen_merge_inside (oldFits : within olds tops = true) (incomingFits : within incoming tops = true) :
    within (widen tops olds (merge olds incoming)) tops = true ∧
    within olds (widen tops olds (merge olds incoming)) = true ∧
    within incoming (widen tops olds (merge olds incoming)) = true := by
  induction tops generalizing olds incoming with
  | nil =>
    cases olds <;> cases incoming <;> simp_all [within,widen,merge]
  | cons top tops ih =>
    cases olds with
    | nil => simp [within] at oldFits
    | cons old olds =>
      cases incoming with
      | nil => simp [within] at incomingFits
      | cons input rest =>
        have oldH := within_cons.mp oldFits
        have inH := within_cons.mp incomingFits
        have tails := ih oldH.2 inH.2
        rw [widen_merge_cons]
        exact ⟨within_cons.mpr ⟨Interval.widen_inside oldH.1 inH.1,tails.1⟩,
          within_cons.mpr ⟨Interval.widen_contains_old ..,tails.2.1⟩,
          within_cons.mpr ⟨Interval.widen_contains_incoming ..,tails.2.2⟩⟩

theorem Frame.widenBudget_mono (oldFits : within olds tops = true) (incomingFits : within incoming tops = true) :
    tops.widenBudget (widen tops olds (merge olds incoming)) ≤ tops.widenBudget olds := by
  induction tops generalizing olds incoming with
  | nil => simp [widenBudget]
  | cons top tops ih =>
    cases olds with
    | nil => simp [within] at oldFits
    | cons old olds =>
      cases incoming with
      | nil => simp [within] at incomingFits
      | cons input rest =>
        have oldH := within_cons.mp oldFits
        have inH := within_cons.mp incomingFits
        have first := Interval.widenBudget_mono oldH.1 inH.1
        have tails := ih oldH.2 inH.2
        simp only [widen_merge_cons,widenBudget]
        omega

theorem Frame.widenBudget_lt (oldFits : within olds tops = true) (incomingFits : within incoming tops = true)
    (changed : within incoming olds = false) :
    tops.widenBudget (widen tops olds (merge olds incoming)) < tops.widenBudget olds := by
  induction tops generalizing olds incoming with
  | nil =>
    cases olds <;> cases incoming <;> simp_all [within]
  | cons top tops ih =>
    cases olds with
    | nil => simp [within] at oldFits
    | cons old olds =>
      cases incoming with
      | nil => simp [within] at incomingFits
      | cons input rest =>
        have oldH := within_cons.mp oldFits
        have inH := within_cons.mp incomingFits
        simp only [widen_merge_cons,widenBudget]
        by_cases same : input.Inside old
        · have tailChanged : within rest olds = false := by
            simpa [within,Interval.Inside,same.1,same.2] using changed
          have first := Interval.widenBudget_mono oldH.1 inH.1
          have tails := ih oldH.2 inH.2 tailChanged
          omega
        · have first := Interval.widenBudget_lt oldH.1 inH.1 same
          have tails := Frame.widenBudget_mono oldH.2 inH.2
          omega

namespace InferenceProgress

def entryBudget (top : Frame) : Option Frame → Nat
  | none => 3*top.length+1
  | some frame => top.widenBudget frame

def tableBudget (top : Frame) (table : InvariantTable) : Nat :=
  (table.toList.map (entryBudget top)).sum

def Fits (top : Frame) (table : InvariantTable) : Prop :=
  ∀ (pc : Nat) (frame : Frame), table[pc]?.join = some frame → Frame.within frame top = true

private theorem sum_set_lt {old replacement : α} (cost : α → Nat) (xs : List α) (found : xs[i]? = some old)
    (decreased : cost replacement < cost old) :
    ((xs.set i replacement).map cost).sum < (xs.map cost).sum := by
  induction xs generalizing i with
  | nil => simp at found
  | cons a xs ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at found
      subst a
      simpa using Nat.add_lt_add_right decreased (List.map cost xs).sum
    | succ n =>
      have tail := ih (by simpa using found)
      simpa using Nat.add_lt_add_left tail (cost a)

theorem tableBudget_le (top : Frame) (table : InvariantTable) :
    tableBudget top table ≤ table.size * (3*top.length+1) := by
  have bound (entries : List (Option Frame)) :
      (entries.map (entryBudget top)).sum ≤ entries.length * (3*top.length+1) := by
    induction entries with
    | nil => simp
    | cons entry rest ih =>
      have first : entryBudget top entry ≤ 3*top.length+1 := by
        cases entry with
        | none => exact Nat.le_refl _
        | some frame => have := Frame.widenBudget_le top frame; dsimp [entryBudget]; omega
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
  simpa [tableBudget] using bound table.toList

private theorem set_budget_lt {old replacement : Option Frame} (top : Frame) (table : InvariantTable)
    (found : table[pc]? = some old) (decreased : entryBudget top replacement < entryBudget top old) :
    tableBudget top (table.set! pc replacement) < tableBudget top table := by
  unfold tableBudget
  rw [Array.set!_eq_setIfInBounds,Array.toList_setIfInBounds]
  exact sum_set_lt (entryBudget top) table.toList (by simpa using found) decreased

theorem joinIncoming_size (top : Frame) (table : InvariantTable) (pc : Nat) (incoming : Frame) :
    (joinIncoming top table pc incoming).1.size = table.size := by
  unfold joinIncoming
  split
  · simp
  · split <;> simp

/-- The exact update used by both executable interval analyzers strictly
reduces the remaining budget whenever it enqueues a successor. -/
theorem joinIncoming_progress (fits : Fits top table) (pcValid : pc < table.size)
    (incomingFits : Frame.within incoming top = true) :
    let updated := joinIncoming top table pc incoming
    if updated.2 then tableBudget top updated.1 < tableBudget top table
    else updated.1 = table := by
  cases found : table[pc]? with
  | none => simp [Array.getElem?_eq_getElem pcValid] at found
  | some entry =>
    cases entry with
    | none =>
      simp only [joinIncoming,found,Option.join_some,↓reduceIte]
      apply set_budget_lt top table found
      have bound := Frame.widenBudget_le top incoming
      change top.widenBudget incoming < 3*top.length+1
      omega
    | some old =>
      have oldFits := fits pc old (by simp [found])
      simp only [joinIncoming,found,Option.join_some]
      split
      · rfl
      · rename_i changed
        apply set_budget_lt top table found
        exact Frame.widenBudget_lt oldFits incomingFits (by simpa using changed)

/-- Starting a new successor frame, or widening an old one, also preserves the
bounded-table invariant used by the progress argument. -/
theorem joinIncoming_fits (fits : Fits top table) (incomingFits : Frame.within incoming top = true) :
    Fits top (joinIncoming top table pc incoming).1 := by
  have update (value : Frame) (inside : Frame.within value top = true) :
      Fits top (table.set! pc (some value)) := by
    intro other frame found
    by_cases equal : pc = other
    · subst other
      by_cases valid : pc < table.size
      · simp [valid] at found
        subst frame
        exact inside
      · simp [valid] at found
    · apply fits other frame
      simpa [Array.getElem?_setIfInBounds,equal] using found
  unfold joinIncoming
  split
  · exact update incoming incomingFits
  · rename_i old found
    split
    · exact fits
    · exact update _ (Frame.widen_merge_inside (fits pc old found) incomingFits).1

end InferenceProgress

end IRComparison.Circuit
