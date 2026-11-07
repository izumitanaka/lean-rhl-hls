import PaperCore.OrdinalCursorSMT

namespace PaperCore.LoopClock
open AccessAnalysis

/-- A proved finite affine clock used only by VC generation. Negative strides
    are allowed. Failure to find this clock does not reject the source loop. -/
structure Clock (start stop step : Int) (after : Affine) where
  delta : Int
  trips : Int
  nonzero : delta ≠ 0
  nonnegative : 0 ≤ trips
  increment : ∀ k, after.eval k + step = k+delta
  endpoint : stop = start+trips*delta

def select (start stop step : Int) (after : Affine) : Option (Clock start stop step after) :=
  if linear : after.scale = 1 then
    let delta := after.offset+step
    if nonzero : delta ≠ 0 then
      let trips := (stop-start)/delta
      if nonnegative : 0 ≤ trips then
        if endpoint : stop = start+trips*delta then
          some ⟨delta,trips,nonzero,nonnegative,
            by intro k; simp [Affine.eval,linear,delta,Int.add_assoc],endpoint⟩
        else none
      else none
    else none
  else none

theorem matches_at_end (clock : Clock start stop step after)
    (holds : OrdinalCursorSMT.shape params arrays layout start clock.delta clock.trips stop indices) :
    BodyCursorSMT.MatchesOn (fun a => a ∈ arrays) params clock.trips layout indices := by
  obtain ⟨t,counter,range⟩ := holds
  have product : t*clock.delta = clock.trips*clock.delta := by have endpoint := clock.endpoint; omega
  have same := Int.eq_of_mul_eq_mul_right clock.nonzero product
  subst t
  exact range.2.2

#print axioms matches_at_end
end PaperCore.LoopClock
