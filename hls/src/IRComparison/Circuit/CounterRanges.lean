import IRComparison.Circuit.RangeMonotone
import IRComparison.Circuit.Scope

/-! Range obligations of the counter loop emitted by `counterLoop`.
Administrative counters remain integers; no BV32 trip-count restriction. -/
namespace IRComparison.Circuit

variable {frame top : Frame} {k : Nat} {limit : Expr}

/-- At the taken loop guard the counter is below the upper bound of the
captured limit. The relation survives joining and threshold widening. -/
theorem Frame.refine_counter_below (valid : k < frame.length) :
    ((frame.refine (.bin .lt (.wire k) limit) true).get k).hi < (range frame.get limit).hi := by
  simp [Frame.refine,Frame.get,List.getElem?_set_self valid]
  omega

/-- Increment is within the allocated counter range after the guard refines
it. This works for an arbitrary limit expression and arbitrary integer bounds. -/
theorem Frame.refine_increment_inside (fits : Frame.within frame top = true)
    (valid : k < frame.length) (limitFits : (range frame.get limit).hi ≤ (top.get k).hi) :
    (range (frame.refine (.bin .lt (.wire k) limit) true).get
      (.bin .add (.wire k) (.lit 1))).Inside (top.get k) := by
  have old := Frame.within_get fits k
  simp only [range,wrapped?,Option.isSome_none,Bool.false_eq_true,↓reduceIte,binRange]
  simp only [Frame.refine,↓reduceIte,Frame.get,List.getElem?_set_self valid,Option.getD_some]
  dsimp [Interval.Inside,Frame.get] at *
  constructor <;> omega

/-- A body may contain arbitrary data operations and nested control, provided
its transfer preserves the active counter bound. An unconditional assumption
that all declared-range frames can be incremented would be incorrect. -/
theorem Frame.increment_inside (fits : Frame.within frame top = true)
    (strict : (frame.get k).hi < (top.get k).hi) :
    (range frame.get (.bin .add (.wire k) (.lit 1))).Inside (top.get k) := by
  have old := Frame.within_get fits k
  change (⟨(frame.get k).lo+1,(frame.get k).hi+1⟩ : Interval).Inside (top.get k)
  dsimp only [Interval.Inside] at *
  constructor <;> omega

/-- The executable increment transfer succeeds and preserves all declared
wire bounds under the point-specific guard bound. -/
theorem transfer_counter_increment (fits : Frame.within frame top = true)
    (valid : k < frame.length) (strict : (frame.get k).hi < (top.get k).hi) (next : Nat) :
    ∃ edges, transfer frame (.wire k (.bin .add (.wire k) (.lit 1)) next) = .ok edges ∧
      ∀ edge ∈ edges, Frame.within edge.2 top = true := by
  by_cases empty : frame.empty = true
  · exact ⟨[],by simp [transfer,empty,pure,Except.pure],by simp⟩
  · refine ⟨[(next,frame.set k (range frame.get (.bin .add (.wire k) (.lit 1))))],?_,?_⟩
    · simp [transfer,empty,valid,pure,Except.pure,bind,Except.bind]
    · intro edge member
      rcases List.mem_singleton.mp member with rfl
      exact Frame.set_within fits (Frame.increment_inside fits strict)

/-- Fresh temporaries used by a loop body cannot change an older loop counter
in the abstract interpreter either. This reuses the compiler's existing scope
condition rather than imposing an additional source-language restriction. -/
def Action.keepsWire (k : Nat) : Action → Prop
  | .wire slot _ | .receive _ slot => slot ≠ k
  | _ => True

theorem Action.transfer_preserves_wire {next : Nat} (action : Action)
    (unchanged : action.keepsWire k)
    (success : transfer frame (action.node next) = .ok edges) (member : edge ∈ edges) :
    edge.2.get k = frame.get k := by
  by_cases empty : frame.empty = true
  · simp [transfer,empty,pure,Except.pure] at success
    subst edges
    simp at member
  · cases action with
    | wire slot e | receive q slot =>
      have different : slot ≠ k := unchanged
      simp only [Action.node,transfer,empty,Bool.false_eq_true,↓reduceIte] at success
      split at success <;> simp only [pure,Except.pure,bind,Except.bind] at success
      · cases success
        rcases List.mem_singleton.mp member with rfl
        simp [Frame.get,List.getElem?_set_ne different]
      · contradiction
    | assign r e | store a j e | send q e =>
      simp only [Action.node,transfer,empty,Bool.false_eq_true,↓reduceIte] at success
      split at success <;> simp only [pure,Except.pure,bind,Except.bind] at success
      · cases success
        rcases List.mem_singleton.mp member with rfl
        rfl
      · contradiction
    | snapshot dst src | erase a | clear q =>
      simp only [Action.node,transfer,empty,Bool.false_eq_true,↓reduceIte,pure,Except.pure,bind,Except.bind] at success
      cases success
      rcases List.mem_singleton.mp member with rfl
      rfl

theorem Action.transfer_preserves_below {next : Nat} (action : Action) (scope : action.above base)
    (success : transfer frame (action.node next) = .ok edges) (member : edge ∈ edges)
    (old : k < base) : edge.2.get k = frame.get k := by
  apply action.transfer_preserves_wire ?_ success member
  cases action <;> try trivial
  all_goals dsimp [Action.keepsWire]; change base ≤ _ at scope; omega

end IRComparison.Circuit
