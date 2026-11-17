import IRComparison.Circuit.CaptureRanges
import IRComparison.Circuit.CounterRanges
import IRComparison.Circuit.InferenceTotal

namespace IRComparison.Circuit

/-- Assertions for the interval interpreter, closed under its actual widening.
These are proof annotations, not run-time state or a new program IR. -/
structure RangeAssertion (top : Frame) where
  holds : Frame → Prop
  widen : ∀ old incoming, holds old → holds incoming →
    old.within top = true → incoming.within top = true →
    holds (Frame.widen top old (old.merge incoming))

namespace RangeAssertion

def unrestricted (top : Frame) : RangeAssertion top := ⟨fun _ => True,by intros; trivial⟩

def counters (top : Frame) (active : List Nat) : RangeAssertion top where
  holds frame := ∀ k ∈ active, (frame.get k).hi < (top.get k).hi
  widen := by
    intro old incoming ho hi oldFits incomingFits k member
    exact Frame.widen_get_below oldFits incomingFits (ho k member) (hi k member)

theorem refine_counters (h : (counters top active).holds frame) :
    (counters top active).holds (frame.refine e yes) := by
  intro k member
  have shrunk := Frame.within_get (Frame.refine_within frame e yes) k
  have strict := h k member
  exact Int.lt_of_le_of_lt shrunk.2 strict

end RangeAssertion

/-- One action preserves declaration bounds and its outgoing assertion.
The sentinel successor 0 is replaced when the existing assembler lays out
the command. No analysis-success assumption occurs in this judgment. -/
def ActionRange (top : Frame) (pre post : RangeAssertion top) (a : Action) : Prop :=
  ∀ frame, pre.holds frame → frame.within top = true →
    ∃ edges, transfer frame (a.node 0) = .ok edges ∧
      ∀ edge ∈ edges, edge.2.empty = false →
        edge.1 = 0 ∧ edge.2.within top = true ∧ post.holds edge.2

/-- Structural pre/post rules for generated control. Loop bodies return to
their invariant; true/false guards have separate entry assertions. -/
inductive ScheduleRange (top : Frame) : RangeAssertion top → Schedule → RangeAssertion top → Prop where
  | skip (weaken : ∀ frame, pre.holds frame → frame.within top = true → post.holds frame) :
      ScheduleRange top pre .skip post
  | step (safe : ActionRange top pre post action) : ScheduleRange top pre (.step action) post
  | seq : ScheduleRange top pre a middle → ScheduleRange top middle b post →
      ScheduleRange top pre (.seq a b) post
  | branch (yesGuard : ∀ f, pre.holds f → f.within top = true → f.empty = false → yesPre.holds (f.refine e true))
      (noGuard : ∀ f, pre.holds f → f.within top = true → f.empty = false → noPre.holds (f.refine e false)) :
      ScheduleRange top yesPre a post → ScheduleRange top noPre b post →
      ScheduleRange top pre (.branch e a b) post
  | loop (yesGuard : ∀ f, invariant.holds f → f.within top = true → f.empty = false → bodyPre.holds (f.refine e true))
      (noGuard : ∀ f, invariant.holds f → f.within top = true → f.empty = false → post.holds (f.refine e false)) :
      ScheduleRange top bodyPre body invariant → ScheduleRange top invariant (.loop e body) post

/-- Rename only the outgoing control edge of an action's abstract transfer. -/
theorem Action.transfer_next (a : Action) (frame : Frame) (next : Nat) :
    transfer frame (a.node next) =
      (transfer frame (a.node 0)).map (List.map (fun edge => (next,edge.2))) := by
  by_cases empty : frame.empty = true
  · simp [transfer,empty,Except.map,pure,Except.pure]
  · cases a <;> simp only [Action.node,transfer,empty,Bool.false_eq_true,↓reduceIte]
    all_goals try split
    all_goals rfl

theorem ActionRange.next (safe : ActionRange top pre post a) (next : Nat)
    (hpre : pre.holds frame) (fits : frame.within top = true) :
    ∃ edges, transfer frame (a.node next) = .ok edges ∧
      ∀ edge ∈ edges, edge.2.empty = false →
        edge.1 = next ∧ edge.2.within top = true ∧ post.holds edge.2 := by
  obtain ⟨edges,he,hs⟩ := safe frame hpre fits
  refine ⟨edges.map (fun edge => (next,edge.2)),?_,?_⟩
  · rw [Action.transfer_next,he]; rfl
  · intro edge member nonempty
    obtain ⟨old,hm,rfl⟩ := List.mem_map.mp member
    exact ⟨rfl,(hs old hm nonempty).2⟩

/-- A local edge either reaches the continuation or another instruction of
the very same laid-out block. Assertions are indexed by instruction offset. -/
def RangeEdge (top : Frame) (annotations : Nat → RangeAssertion top)
    (length base next : Nat) (post : RangeAssertion top) (edge : Nat × Frame) : Prop :=
  edge.2.within top = true ∧
    ((edge.1 = next ∧ post.holds edge.2) ∨
      ∃ k, k < length ∧ edge.1 = base+k ∧ (annotations k).holds edge.2)

structure LayoutRanges (top : Frame) (nodes : List Node) (base next : Nat)
    (pre post : RangeAssertion top) where
  annotations : Nat → RangeAssertion top
  entry : annotations 0 = pre
  transfer : ∀ k node, nodes[k]? = some node → ∀ frame,
    (annotations k).holds frame → frame.within top = true →
      ∃ edges, Circuit.transfer frame node = .ok edges ∧
        ∀ edge ∈ edges, edge.2.empty = false → RangeEdge top annotations nodes.length base next post edge

theorem Schedule.size_pos (s : Schedule) : 0 < s.size := by
  induction s <;> simp_all [Schedule.size] <;> omega

namespace LayoutRanges
variable {next : Nat}

theorem skip (weaken : ∀ frame, pre.holds frame → frame.within top = true → post.holds frame)
    (base next : Nat) : Nonempty (LayoutRanges top [.jump next] base next pre post) := by
  refine ⟨⟨fun _ => pre,rfl,?_⟩⟩
  intro k node found frame hp fits
  cases k with
  | succ k => simp at found
  | zero =>
    cases found
    by_cases empty : frame.empty = true
    · exact ⟨[],by simp [Circuit.transfer,empty,pure,Except.pure,bind,Except.bind],by simp⟩
    · refine ⟨[(next,frame)],by simp [Circuit.transfer,empty,pure,Except.pure,bind,Except.bind],?_⟩
      intro edge member _
      rcases List.mem_singleton.mp member with rfl
      exact ⟨fits,Or.inl ⟨rfl,weaken frame hp fits⟩⟩

theorem step (safe : ActionRange top pre post action) (base next : Nat) :
    Nonempty (LayoutRanges top [action.node next] base next pre post) := by
  refine ⟨⟨fun _ => pre,rfl,?_⟩⟩
  intro k node found frame hp fits
  cases k with
  | succ k => simp at found
  | zero =>
    cases found
    obtain ⟨edges,he,hs⟩ := safe.next next hp fits
    exact ⟨edges,he,fun edge member nonempty =>
      ⟨(hs edge member nonempty).2.1,Or.inl ⟨(hs edge member nonempty).1,(hs edge member nonempty).2.2⟩⟩⟩

theorem seq (a : LayoutRanges top first base (base+first.length) pre middle)
    (b : LayoutRanges top second (base+first.length) next middle post)
    (positive : 0 < first.length) (positiveSecond : 0 < second.length) :
    Nonempty (LayoutRanges top (first++second) base next pre post) := by
  let ann := fun k => if k < first.length then a.annotations k else b.annotations (k-first.length)
  refine ⟨⟨ann,by simpa [ann,positive] using a.entry,?_⟩⟩
  intro k node found frame hp fits
  by_cases left : k < first.length
  · have hf : first[k]? = some node := by simpa [List.getElem?_append,left] using found
    have ha : (a.annotations k).holds frame := by simpa [ann,left] using hp
    obtain ⟨edges,he,hs⟩ := a.transfer k node hf frame ha fits
    refine ⟨edges,he,?_⟩
    intro edge member nonempty
    obtain ⟨fit,outside | ⟨j,hj,position,holds⟩⟩ := hs edge member nonempty
    · refine ⟨fit,Or.inr ⟨first.length,?_,outside.1,?_⟩⟩
      · simp; omega
      · simpa [ann,b.entry] using outside.2
    · exact ⟨fit,Or.inr ⟨j,by simp; omega,position,by simpa [ann,hj] using holds⟩⟩
  · have hf : second[k-first.length]? = some node := by simpa [List.getElem?_append,left] using found
    have hb : (b.annotations (k-first.length)).holds frame := by simpa [ann,left] using hp
    obtain ⟨edges,he,hs⟩ := b.transfer _ node hf frame hb fits
    refine ⟨edges,he,?_⟩
    intro edge member nonempty
    obtain ⟨fit,outside | ⟨j,hj,position,holds⟩⟩ := hs edge member nonempty
    · exact ⟨fit,Or.inl outside⟩
    · refine ⟨fit,Or.inr ⟨first.length+j,by simp; omega,by omega,?_⟩⟩
      simpa [ann,show ¬ first.length+j < first.length from by omega] using holds

theorem branch (a : LayoutRanges top first (base+1) next yesPre post)
    (b : LayoutRanges top second (base+1+first.length) next noPre post)
    (firstPositive : 0 < first.length) (secondPositive : 0 < second.length)
    (yesGuard : ∀ f, pre.holds f → f.within top = true → f.empty = false → yesPre.holds (f.refine e true))
    (noGuard : ∀ f, pre.holds f → f.within top = true → f.empty = false → noPre.holds (f.refine e false)) :
    Nonempty (LayoutRanges top (.branch e (base+1) (base+1+first.length)::(first++second)) base next pre post) := by
  let ann : Nat → RangeAssertion top
    | 0 => pre
    | k+1 => if k < first.length then a.annotations k else b.annotations (k-first.length)
  refine ⟨⟨ann,rfl,?_⟩⟩
  intro k node found frame hp fits
  cases k with
  | zero =>
    cases found
    by_cases empty : frame.empty = true
    · exact ⟨[],by simp [Circuit.transfer,empty,pure,Except.pure,bind,Except.bind],by simp⟩
    · refine ⟨[(base+1,frame.refine e true),(base+1+first.length,frame.refine e false)],
        by simp [Circuit.transfer,empty,pure,Except.pure,bind,Except.bind],?_⟩
      intro edge member _
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl
      · refine ⟨Frame.within_trans (Frame.refine_within frame e true) fits,Or.inr ⟨1,by simp; omega,rfl,?_⟩⟩
        simpa [ann,firstPositive,a.entry] using yesGuard frame hp fits (Bool.eq_false_iff.mpr empty)
      · refine ⟨Frame.within_trans (Frame.refine_within frame e false) fits,
          Or.inr ⟨first.length+1,by simp; omega,by omega,?_⟩⟩
        simpa [ann,b.entry] using noGuard frame hp fits (Bool.eq_false_iff.mpr empty)
  | succ k =>
    simp only [List.getElem?_cons_succ] at found
    by_cases left : k < first.length
    · have hf : first[k]? = some node := by simpa [List.getElem?_append,left] using found
      have ha : (a.annotations k).holds frame := by simpa [ann,left] using hp
      obtain ⟨edges,he,hs⟩ := a.transfer k node hf frame ha fits
      refine ⟨edges,he,?_⟩
      intro edge member nonempty
      obtain ⟨fit,outside | ⟨j,hj,position,holds⟩⟩ := hs edge member nonempty
      · exact ⟨fit,Or.inl outside⟩
      · exact ⟨fit,Or.inr ⟨j+1,by simp; omega,by omega,by simpa [ann,hj] using holds⟩⟩
    · have hf : second[k-first.length]? = some node := by simpa [List.getElem?_append,left] using found
      have hb : (b.annotations (k-first.length)).holds frame := by simpa [ann,left] using hp
      obtain ⟨edges,he,hs⟩ := b.transfer _ node hf frame hb fits
      refine ⟨edges,he,?_⟩
      intro edge member nonempty
      obtain ⟨fit,outside | ⟨j,hj,position,holds⟩⟩ := hs edge member nonempty
      · exact ⟨fit,Or.inl outside⟩
      · refine ⟨fit,Or.inr ⟨first.length+j+1,by simp; omega,by omega,?_⟩⟩
        simpa [ann,show ¬ first.length+j < first.length from by omega] using holds

theorem loop (body : LayoutRanges top nodes (base+1) base bodyPre invariant)
    (positive : 0 < nodes.length)
    (yesGuard : ∀ f, invariant.holds f → f.within top = true → f.empty = false → bodyPre.holds (f.refine e true))
    (noGuard : ∀ f, invariant.holds f → f.within top = true → f.empty = false → post.holds (f.refine e false)) :
    Nonempty (LayoutRanges top (.branch e (base+1) next::nodes) base next invariant post) := by
  let ann : Nat → RangeAssertion top
    | 0 => invariant
    | k+1 => body.annotations k
  refine ⟨⟨ann,rfl,?_⟩⟩
  intro k node found frame hp fits
  cases k with
  | zero =>
    cases found
    by_cases empty : frame.empty = true
    · exact ⟨[],by simp [Circuit.transfer,empty,pure,Except.pure,bind,Except.bind],by simp⟩
    · refine ⟨[(base+1,frame.refine e true),(next,frame.refine e false)],
        by simp [Circuit.transfer,empty,pure,Except.pure,bind,Except.bind],?_⟩
      intro edge member _
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl
      · refine ⟨Frame.within_trans (Frame.refine_within frame e true) fits,Or.inr ⟨1,by simp; omega,rfl,?_⟩⟩
        simpa [ann,body.entry] using yesGuard frame hp fits (Bool.eq_false_iff.mpr empty)
      · exact ⟨Frame.within_trans (Frame.refine_within frame e false) fits,Or.inl ⟨rfl,noGuard frame hp fits (Bool.eq_false_iff.mpr empty)⟩⟩
  | succ k =>
    obtain ⟨edges,he,hs⟩ := body.transfer k node found frame hp fits
    refine ⟨edges,he,?_⟩
    intro edge member nonempty
    obtain ⟨fit,outside | ⟨j,hj,position,holds⟩⟩ := hs edge member nonempty
    · exact ⟨fit,Or.inr ⟨0,by simp,by simpa using outside.1,outside.2⟩⟩
    · exact ⟨fit,Or.inr ⟨j+1,by simp; omega,by omega,holds⟩⟩

end LayoutRanges

/-- Structural reasoning survives the actual address layout, including back
edges and arbitrarily nested control. No loop trip count is enumerated. -/
theorem ScheduleRange.layout (proof : ScheduleRange top pre code post) (base next : Nat) :
    Nonempty (LayoutRanges top (code.layout base next) base next pre post) := by
  induction proof generalizing base next with
  | skip weaken => exact LayoutRanges.skip weaken base next
  | step safe => exact LayoutRanges.step safe base next
  | @seq pre a middle b post ha hb ia ib =>
    obtain ⟨left⟩ := ia base (base+a.size)
    obtain ⟨right⟩ := ib (base+a.size) next
    simpa only [Schedule.layout,Schedule.layout_length] using
      LayoutRanges.seq (by simpa only [Schedule.layout_length] using left)
        (by simpa only [Schedule.layout_length] using right)
        (by simpa only [Schedule.layout_length] using a.size_pos)
        (by simpa only [Schedule.layout_length] using b.size_pos)
  | @branch yesPre a post noPre b pre e yesGuard noGuard ha hb ia ib =>
    obtain ⟨left⟩ := ia (base+1) next
    obtain ⟨right⟩ := ib (base+1+a.size) next
    simpa only [Schedule.layout,Schedule.layout_length] using
      LayoutRanges.branch left (by simpa only [Schedule.layout_length] using right)
        (by simpa only [Schedule.layout_length] using a.size_pos)
        (by simpa only [Schedule.layout_length] using b.size_pos) yesGuard noGuard
  | @loop bodyPre body invariant e post yesGuard noGuard hb ih =>
    obtain ⟨child⟩ := ih (base+1) base
    exact LayoutRanges.loop child (by simpa only [Schedule.layout_length] using body.size_pos) yesGuard noGuard

/-- Install the structural annotations at the actual machine addresses. Address
zero is the halt continuation, not a synthetic extra program phase. -/
def LayoutRanges.machineAssertion
    (h : LayoutRanges top nodes 1 0 pre post) : Nat → RangeAssertion top
  | 0 => post
  | k+1 => h.annotations k

theorem LayoutRanges.closed (h : LayoutRanges top nodes 1 0 pre post) :
    InferenceProgress.TransferClosed top (Node.halt::nodes).toArray.size
      (fun pc f => (h.machineAssertion pc).holds f)
      (fun pc f => Circuit.transfer f (Node.halt::nodes).toArray[pc]!) := by
  constructor
  · intro pc frame valid hp fits
    cases pc with
    | zero =>
      exact ⟨[],by simp [Circuit.transfer,pure,Except.pure,bind,Except.bind],by simp⟩
    | succ k =>
      have inBody : k < nodes.length := by simpa using valid
      have found : nodes[k]? = some nodes[k] := List.getElem?_eq_getElem inBody
      obtain ⟨edges,he,hs⟩ := h.transfer k nodes[k] found frame hp fits
      refine ⟨edges,?_,?_⟩
      · simpa [getElem!_pos,valid,found] using he
      · intro edge member nonempty
        obtain ⟨fit,outside | ⟨j,hj,position,holds⟩⟩ := hs edge member nonempty
        · refine ⟨by simp [outside.1],fit,?_⟩
          simpa [outside.1,machineAssertion] using outside.2
        · refine ⟨by simp; omega,fit,?_⟩
          simpa [position,Nat.add_comm,machineAssertion] using holds
  · intro pc old incoming ho hi fo fi
    exact (h.machineAssertion pc).widen old incoming ho hi fo fi

/-- The existing interval inference and its independent checker both succeed
for any assembled schedule satisfying the structural range rules. This is a
termination/success theorem for the executable analysis, not an assumed VC. -/
theorem ScheduleRange.inferInvariant {a : Artifact} {pre post : RangeAssertion a.wires.toList}
    (proof : ScheduleRange a.wires.toList pre code post)
    (machine : a.machine = code.assemble capacities)
    (initialFits : (initialFrame a).within a.wires.toList = true)
    (initialPre : pre.holds (initialFrame a)) :
    ∃ table, Circuit.inferInvariant a = .ok table ∧ validInvariant a table = true := by
  obtain ⟨layout⟩ := proof.layout 1 0
  apply inferInvariant_complete (allowed := fun pc f => (layout.machineAssertion pc).holds f)
  · simpa only [machine,Schedule.assemble] using layout.closed
  · simpa [machine,Schedule.assemble,Schedule.layout_length] using code.size_pos
  · exact initialFits
  · simpa [machine,Schedule.assemble,LayoutRanges.machineAssertion,layout.entry] using initialPre

end IRComparison.Circuit
