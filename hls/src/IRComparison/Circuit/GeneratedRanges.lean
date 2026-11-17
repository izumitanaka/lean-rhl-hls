import IRComparison.Circuit.ScheduleRanges
import IRComparison.Circuit.CommandFrame
import IRComparison.Circuit.ChannelFrame

namespace IRComparison.Circuit

namespace RangeAssertion

def withCounters (a : RangeAssertion top) (active : List Nat) : RangeAssertion top where
  holds f := a.holds f ∧ (counters top active).holds f
  widen old incoming ho hi fo fi :=
    ⟨a.widen old incoming ho.1 hi.1 fo fi,(counters top active).widen old incoming ho.2 hi.2 fo fi⟩

end RangeAssertion

/-- Captures and data actions preserve older loop counters. The annotations
are threaded through arbitrary nested branches and loops, not just examples. -/
theorem ScheduleRange.withCounters (proof : ScheduleRange top pre code post)
    (scope : ChannelLower.frame bank base code) (older : ∀ k ∈ active, ChannelLower.Protected bank base k) :
    ScheduleRange top (pre.withCounters active) code (post.withCounters active) := by
  induction proof with
  | skip weaken => exact .skip (fun f h fits => ⟨weaken f h.1 fits,h.2⟩)
  | @step pre post action safe =>
    apply ScheduleRange.step
    intro frame hp fits
    obtain ⟨edges,he,hs⟩ := safe frame hp.1 fits
    refine ⟨edges,he,?_⟩
    intro edge member nonempty
    obtain ⟨position,fit,holds⟩ := hs edge member nonempty
    refine ⟨position,fit,holds,?_⟩
    intro k hk
    have unchanged : action.keepsWire k := by
      cases action <;> try trivial
      all_goals exact Ne.symm (scope k (older k hk))
    rw [action.transfer_preserves_wire (k:=k) unchanged he member]
    exact hp.2 k hk
  | seq _ _ a b => exact .seq (a scope.1) (b scope.2)
  | @branch yesPre a post noPre b pre e yesGuard noGuard _ _ ia ib =>
    exact ScheduleRange.branch (yesPre:=yesPre.withCounters active) (noPre:=noPre.withCounters active) (fun f h fits nonempty => ⟨yesGuard f h.1 fits nonempty,RangeAssertion.refine_counters h.2⟩)
      (fun f h fits nonempty => ⟨noGuard f h.1 fits nonempty,RangeAssertion.refine_counters h.2⟩)
      (ia scope.1) (ib scope.2)
  | @loop bodyPre body invariant e post yesGuard noGuard _ ih =>
    exact ScheduleRange.loop (bodyPre:=bodyPre.withCounters active) (fun f h fits nonempty => ⟨yesGuard f h.1 fits nonempty,RangeAssertion.refine_counters h.2⟩)
      (fun f h fits nonempty => ⟨noGuard f h.1 fits nonempty,RangeAssertion.refine_counters h.2⟩) (ih scope)

/-- Abstract transfer of an action has only its declared successor. -/
theorem Action.transfer_target {next : Nat} (action : Action)
    (success : transfer frame (action.node next) = .ok edges) (member : edge ∈ edges) : edge.1 = next := by
  by_cases empty : frame.empty = true
  · simp [transfer,empty,pure,Except.pure] at success
    subst edges
    simp at member
  · cases action <;> simp only [Action.node,transfer,empty,Bool.false_eq_true,↓reduceIte] at success
    all_goals try split at success
    all_goals simp only [pure,Except.pure,bind,Except.bind] at success
    all_goals first | contradiction | (cases success; cases List.mem_singleton.mp member; rfl)

abbrev RangeSafe (top : Frame) (code : Schedule) : Prop :=
  ScheduleRange top (.unrestricted top) code (.unrestricted top)

/-- A successful one-step range transfer is sufficient for a simple action;
no invocation of the graph's inference or checker appears in this premise. -/
theorem RangeSafe.step (safe : ∀ f, f.within top = true →
    ∃ edges, transfer f (action.node 0) = .ok edges ∧ ∀ edge ∈ edges, edge.2.within top = true) :
    RangeSafe top (.step action) := by
  apply ScheduleRange.step
  intro f _ fits
  obtain ⟨edges,he,hs⟩ := safe f fits
  exact ⟨edges,he,fun edge member _ => ⟨action.transfer_target he member,hs edge member,trivial⟩⟩

theorem RangeSafe.skip : RangeSafe top .skip := ScheduleRange.skip (by intros; trivial)
theorem RangeSafe.seq (a : RangeSafe top first) (b : RangeSafe top second) :
    RangeSafe top (.seq first second) := ScheduleRange.seq a b

theorem RangeSafe.branch (a : RangeSafe top first) (b : RangeSafe top second) :
    RangeSafe top (.branch e first second) := ScheduleRange.branch (yesPre:=.unrestricted top) (noPre:=.unrestricted top) (by intros; trivial) (by intros; trivial) a b

theorem WordRanges.Word.refined {top frame : Frame} (word : Word top.get e) (fits : frame.within top = true)
    (nonempty : frame.empty = false) : Word frame.get e := by
  have smaller := Frame.range_inside fits nonempty e
  have outer := WordRanges.bounds word
  simp only [WordRanges.Word,isWord,Bool.and_eq_true,decide_eq_true_eq]
  constructor <;> unfold Interval.Inside at smaller <;> omega

theorem RangeSafe.data (word : match action with
    | .assign _ e | .store _ _ e | .send _ e => WordRanges.Word top.get e
    | .snapshot .. | .clear .. | .erase .. => True
    | _ => False) : RangeSafe top (.step action) := by
  apply RangeSafe.step
  intro frame fits
  by_cases empty : frame.empty = true
  · exact ⟨[],by simp [transfer,empty,pure,Except.pure],by simp⟩
  · refine ⟨[(0,frame)],?_,by intro edge member; cases List.mem_singleton.mp member; exact fits⟩
    cases action with
    | wire | receive => contradiction
    | assign | store | send =>
      have small := word.refined fits (Bool.eq_false_iff.mpr empty)
      change isWord _ = true at small
      simp [Action.node,transfer,empty,small,pure,Except.pure,bind,Except.bind]
    | snapshot | clear | erase => simp [Action.node,transfer,empty,pure,Except.pure,bind,Except.bind]

theorem RangeSafe.wire (valid : k < top.length)
    (allocated : (range top.get e).Inside (top.get k)) : RangeSafe top (.step (.wire k e)) := by
  apply RangeSafe.step
  intro frame fits
  apply transfer_wire_inside fits (by have := Frame.within_length fits; omega) allocated

theorem RangeSafe.receive (valid : k < top.length) (allocated : wordRange.Inside (top.get k)) :
    RangeSafe top (.step (.receive q k)) := by
  apply RangeSafe.step
  intro frame fits
  by_cases empty : frame.empty = true
  · exact ⟨[],by simp [Action.node,transfer,empty,pure,Except.pure],by simp⟩
  · have validFrame : k < frame.length := by have := Frame.within_length fits; omega
    refine ⟨[(0,frame.set k wordRange)],?_,?_⟩
    · simp [Action.node,transfer,empty,validFrame,pure,Except.pure,bind,Except.bind]
    · intro edge member
      cases List.mem_singleton.mp member
      exact Frame.set_within fits allocated

theorem RangeSafe.capture {b final : Build} (scope : RangeScoped b.wires.size e)
    (kept : WireAllocation.Extends (b.addWire (b.exprRange e)) final) :
    RangeSafe final.wires.toList (.step (.wire b.wires.size e)) :=
  .wire (WireAllocation.fresh_valid kept) (capture_range scope kept)

/-- The compiler's rolled counter loop satisfies the range rules for arbitrary
trip counts, provided its body does not overwrite the fresh administrative
counter. This is a structural property of all generated bodies. -/
theorem RangeSafe.counterLoop (bodySafe : RangeSafe top body)
    (bodyScope : ChannelLower.frame bank (k+1) body) (outside : k < bank.base ∨ bank.stop ≤ k)
    (valid : k < top.length)
    (zero : (top.get k).Contains 0)
    (limitFits : (range top.get limit).hi ≤ (top.get k).hi) :
    RangeSafe top (counterLoop k limit body) := by
  apply ScheduleRange.seq
  · apply RangeSafe.step
    intro frame fits
    apply transfer_wire_inside fits
    · have := Frame.within_length fits; omega
    · exact zero
  · apply ScheduleRange.loop (bodyPre := (RangeAssertion.unrestricted top).withCounters [k])
    · intro frame _ fits nonempty
      refine ⟨trivial,?_⟩
      intro j member
      cases List.mem_singleton.mp member
      have small := Frame.range_inside fits nonempty limit
      have bound := Frame.refine_counter_below (limit:=limit)
        (show k < frame.length from by have := Frame.within_length fits; omega)
      exact Int.lt_of_lt_of_le bound (Int.le_trans small.2 limitFits)
    · intros; trivial
    · apply ScheduleRange.seq (bodySafe.withCounters bodyScope (by intro j hj; cases List.mem_singleton.mp hj; exact ⟨by omega,outside⟩))
      apply ScheduleRange.step
      intro frame hp fits
      obtain ⟨edges,he,hs⟩ := transfer_counter_increment fits
        (show k < frame.length from by have := Frame.within_length fits; omega) (hp.2 k (by simp)) 0
      exact ⟨edges,he,fun edge member _ => ⟨(Action.wire k _).transfer_target he member,hs edge member,trivial⟩⟩

theorem CommandWordRanges.Context.frameRead {b : Build}
    (ctx : CommandWordRanges.Context b slots types) (hi : RangeScoped b.wires.size i)
    (typed : HybridIR.WordRead types (fun _ => False) e) :
    WordRanges.Word (Frame.get b.wires.toList)
      (Circuit.read i (.wire 0) (.wire 1) (slots.map Expr.wire) [] e) := by
  have word := ctx.read (i:=i) typed
  unfold WordRanges.Word at *
  rw [(RangeScoped.context_read ctx hi e).frame_range] at word
  exact word

/-- Constant-count loops use exactly the range allocated by `fresh`. -/
theorem RangeSafe.repeat {b final : Build} (n : Nat)
    (kept : WireAllocation.Extends (b.addWire ⟨0,n⟩) final)
    (bodySafe : RangeSafe final.wires.toList body)
    (bodyScope : ChannelLower.frame bank (b.wires.size+1) body)
    (bankBefore : bank.stop ≤ b.wires.size) :
    RangeSafe final.wires.toList (Circuit.counterLoop b.wires.size (.lit n) body) := by
  apply RangeSafe.counterLoop bodySafe bodyScope (Or.inr bankBefore) (WireAllocation.fresh_valid kept)
  · rw [WireAllocation.fresh_bound kept]
    simp [Interval.Contains]
  · rw [WireAllocation.fresh_bound kept]
    change (n:Int) ≤ max 0 n
    omega

/-- Bounds and counter captures are allocated by the actual builder. Both
ranges agree because the bound refers only to earlier declarations. -/
theorem RangeSafe.capturedLoop {b final : Build}
    (scope : RangeScoped b.wires.size e)
    (kept : WireAllocation.Extends
      ((b.addWire (b.exprRange e)).addWire ((b.addWire (b.exprRange e)).exprRange e)) final)
    (bodySafe : RangeSafe final.wires.toList body)
    (bodyScope : ChannelLower.frame bank (b.wires.size+2) body)
    (bankBefore : bank.stop ≤ b.wires.size) :
    RangeSafe final.wires.toList (.seq (.step (.wire b.wires.size e))
      (Circuit.counterLoop (b.wires.size+1) (.wire b.wires.size) body)) := by
  let b1 := b.addWire (b.exprRange e)
  have nKept := (CommandWordRanges.addWire_prefix b1 (b1.exprRange e)).trans kept
  have same : b.exprRange e = b1.exprRange e := scope.exprRange_extend (CommandWordRanges.addWire_prefix b _)
  apply RangeSafe.seq (RangeSafe.capture scope nKept)
  have size1 : b1.wires.size = b.wires.size+1 := by simp [b1,Build.addWire]
  have kValid : b.wires.size+1 < final.wires.toList.length := by simpa only [Build.addWire,Array.size_push,Array.length_toList] using WireAllocation.fresh_valid kept
  have kr : Frame.get final.wires.toList (b.wires.size+1) = ⟨min 0 (b1.exprRange e).lo,max 0 (b1.exprRange e).hi⟩ := by
    rw [← size1]
    exact WireAllocation.fresh_bound kept
  apply RangeSafe.counterLoop bodySafe (by simpa [Nat.add_assoc] using bodyScope)
    (Or.inr (by omega)) kValid
  · rw [kr]; exact ⟨Int.min_le_left _ _,Int.le_max_left _ _⟩
  · change (Frame.get final.wires.toList b.wires.size).hi ≤ _
    rw [WireAllocation.fresh_bound nKept,kr,same]
    exact Int.le_refl _

end IRComparison.Circuit
