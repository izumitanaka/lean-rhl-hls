import IRComparison.Circuit.WidenProgress

namespace IRComparison.Circuit.InferenceProgress

/-- A point-specific property of reachable analysis frames. In particular,
loop increments can require a stricter counter bound than the loop header. -/
def Frames (allowed : Nat → Frame → Prop) (table : InvariantTable) : Prop :=
  ∀ pc frame, table[pc]?.join = some frame → allowed pc frame

def Known (table : InvariantTable) (work : List Nat) : Prop :=
  ∀ pc ∈ work, ∃ frame, table[pc]?.join = some frame

/-- Invariant needed of transfer and widening, independent of inference fuel
or success. It can be instantiated with program-point counter invariants. -/
structure TransferClosed (top : Frame) (size : Nat) (allowed : Nat → Frame → Prop)
    (step : Nat → Frame → Except String (List (Nat × Frame))) : Prop where
  transfer : ∀ pc frame, pc < size → allowed pc frame → Frame.within frame top = true →
    ∃ edges, step pc frame = .ok edges ∧ ∀ edge ∈ edges, edge.2.empty = false →
      edge.1 < size ∧ Frame.within edge.2 top = true ∧ allowed edge.1 edge.2
  widen : ∀ pc old incoming, allowed pc old → allowed pc incoming →
    Frame.within old top = true → Frame.within incoming top = true →
    allowed pc (Frame.widen top old (old.merge incoming))

private theorem set_frames (holds : Frames allowed table) (new : allowed pc frame) :
    Frames allowed (table.set! pc (some frame)) := by
  intro other f found
  by_cases equal : pc = other
  · subst other
    by_cases valid : pc < table.size
    · simp [valid] at found
      subst f
      exact new
    · simp [valid] at found
  · apply holds other f
    simpa [Array.getElem?_setIfInBounds,equal] using found

private theorem set_known (known : Known table work) (valid : pc < table.size) :
    Known (table.set! pc (some frame)) (pc::work) := by
  intro other member
  by_cases equal : pc = other
  · subst other
    exact ⟨frame,by simp [valid]⟩
  · have member' : other ∈ work := by simpa [Ne.symm equal] using member
    obtain ⟨old,found⟩ := known other member'
    exact ⟨old,by simpa [Array.getElem?_setIfInBounds,equal] using found⟩

/-- Existing frames are retained or enlarged, never discarded. -/
def Extends (before after : InvariantTable) : Prop :=
  ∀ (pc : Nat) (old : Frame), before[pc]?.join = some old →
    ∃ new, after[pc]?.join = some new ∧ Frame.within old new = true

theorem Extends.refl (table : InvariantTable) : Extends table table :=
  fun _ old found => ⟨old,found,Frame.within_refl old⟩

theorem Extends.trans (ab : Extends a b) (bc : Extends b c) : Extends a c := by
  intro pc old found
  obtain ⟨middle,mid,first⟩ := ab pc old found
  obtain ⟨last,fin,second⟩ := bc pc middle mid
  exact ⟨last,fin,Frame.within_trans first second⟩

theorem Extends.edge {edge : Nat × Frame} (growth : Extends before after) (h : validEdge before edge = true) :
    validEdge after edge = true := by
  by_cases empty : edge.2.empty = true
  · simp [validEdge,empty]
  · cases found : before[edge.1]?.join with
    | none => simp [validEdge,empty,found] at h
    | some old =>
      have inside : edge.2.within old = true := by simpa [validEdge,empty,found] using h
      obtain ⟨new,eq,bigger⟩ := growth edge.1 old found
      simpa [validEdge,empty,eq] using Frame.within_trans inside bigger

private theorem join_extends (fits : Fits top table) (incomingFits : incoming.within top = true)
    (valid : pc < table.size) : Extends table (joinIncoming top table pc incoming).1 := by
  intro other old found
  by_cases same : pc = other
  · subst other
    have oldFits := fits pc old found
    by_cases contained : incoming.within old = true
    · exact ⟨old,by simp [joinIncoming,found,contained],Frame.within_refl old⟩
    · exact ⟨_,by simp only [joinIncoming,found,if_neg contained]; simp [valid],
        (Frame.widen_merge_inside oldFits incomingFits).2.1⟩
  · unfold joinIncoming
    split
    · exact ⟨old,by simpa [Array.getElem?_setIfInBounds,same] using found,Frame.within_refl old⟩
    · split
      · exact ⟨old,found,Frame.within_refl old⟩
      · exact ⟨old,by simpa [Array.getElem?_setIfInBounds,same] using found,Frame.within_refl old⟩

private theorem join_edge (fits : Fits top table) (incomingFits : incoming.within top = true)
    (valid : pc < table.size) : validEdge (joinIncoming top table pc incoming).1 (pc,incoming) = true := by
  cases found : table[pc]?.join with
  | none =>
    simp only [joinIncoming,found]
    simp [valid,validEdge,Frame.within_refl]
  | some old =>
    by_cases contained : incoming.within old = true
    · simp [joinIncoming,found,contained,validEdge]
    · have cover := (Frame.widen_merge_inside (fits pc old found) incomingFits).2.2
      simp only [joinIncoming,found,if_neg contained]
      simp [valid,validEdge,cover]

private theorem join_unchanged
    (absent : other ∉ (if (joinIncoming top table pc incoming).2 then pc::work else work)) :
    (joinIncoming top table pc incoming).1[other]?.join = table[other]?.join := by
  cases found : table[pc]?.join with
  | none =>
    simp only [joinIncoming,found] at absent ⊢
    have ne : pc ≠ other := by
      intro eq
      exact absent (by simp [eq])
    simp [ne]
  | some old =>
    by_cases contained : incoming.within old = true
    · simp only [joinIncoming,found,if_pos contained]
    · simp only [joinIncoming,found,if_neg contained] at absent ⊢
      have ne : pc ≠ other := by
        intro eq
        exact absent (by simp [eq])
      simp [ne]

/-- Adding successors does not increase table budget plus pending work. -/
theorem enqueue_complete (closed : TransferClosed top size allowed step)
    (fits : Fits top table) (holds : Frames allowed table) (known : Known table work)
    (sized : table.size = size)
    (edgesSafe : ∀ edge ∈ edges, edge.2.empty = false →
      edge.1 < size ∧ Frame.within edge.2 top = true ∧ allowed edge.1 edge.2) :
    ∃ updated, enqueueEdges top edges table work = .ok updated ∧
      Fits top updated.1 ∧ Frames allowed updated.1 ∧ Known updated.1 updated.2 ∧
      updated.1.size = size ∧
      tableBudget top updated.1 + updated.2.length ≤ tableBudget top table + work.length ∧
      Extends table updated.1 ∧ (∀ edge ∈ edges, validEdge updated.1 edge = true) ∧
      (∀ pc, pc ∉ updated.2 → updated.1[pc]?.join = table[pc]?.join) ∧
      (∀ pc ∈ work, pc ∈ updated.2) := by
  induction edges generalizing table work with
  | nil => exact ⟨(table,work),rfl,fits,holds,known,sized,Nat.le_refl _,Extends.refl _,
      by simp,fun _ _ => rfl,fun _ h => h⟩
  | cons edge edges ih =>
    obtain ⟨pc,incoming⟩ := edge
    by_cases empty : incoming.empty = true
    · obtain ⟨updated,run,f,h,k,z,b,g,v,u,keep⟩ := ih fits holds known sized (fun e mem => edgesSafe e (by simp [mem]))
      refine ⟨updated,by simpa [enqueueEdges,empty] using run,f,h,k,z,b,g,?_,u,keep⟩
      intro edge member
      rcases List.mem_cons.mp member with rfl | member
      · simp [validEdge,empty]
      · exact v edge member
    · have nonempty : incoming.empty = false := Bool.eq_false_iff.mpr empty
      obtain ⟨valid,incomingFits,incomingAllowed⟩ := edgesSafe (pc,incoming) (by simp) nonempty
      have pcValid : pc < table.size := by omega
      let next := joinIncoming top table pc incoming
      let pending := if next.2 then pc::work else work
      have nextFits : Fits top next.1 := joinIncoming_fits fits incomingFits
      have nextSize : next.1.size = size := (joinIncoming_size top table pc incoming).trans sized
      have nextHolds : Frames allowed next.1 := by
        dsimp [next,joinIncoming]
        split
        · exact set_frames holds incomingAllowed
        · rename_i old found
          split
          · exact holds
          · exact set_frames holds (closed.widen pc old incoming (holds pc old found)
              incomingAllowed (fits pc old found) incomingFits)
      have nextKnown : Known next.1 pending := by
        cases found : table[pc]?.join with
        | none => simpa [pending,next,joinIncoming,found] using
            (set_known (frame := incoming) known pcValid)
        | some old =>
          by_cases same : incoming.within old = true
          · simpa [pending,next,joinIncoming,found,same] using known
          · simpa [pending,next,joinIncoming,found,same] using
              (set_known (frame := Frame.widen top old (old.merge incoming)) known pcValid)
      have measure : tableBudget top next.1 + pending.length ≤ tableBudget top table + work.length := by
        have progress := joinIncoming_progress fits pcValid incomingFits
        change (if next.2 then tableBudget top next.1 < tableBudget top table else next.1 = table) at progress
        dsimp [pending]
        split
        · rename_i changed
          simp only [changed,↓reduceIte] at progress
          simp only [List.length_cons]
          omega
        · rename_i unchanged
          simp only [unchanged] at progress
          rw [progress]
          exact Nat.le_refl _
      have keepNext : ∀ p ∈ work, p ∈ pending := by
        intro p member
        dsimp [pending]
        split <;> simp [member]
      obtain ⟨updated,run,newFits,newHolds,newKnown,newSize,budget,growth,validEdges,unchanged,keep⟩ :=
        ih nextFits nextHolds nextKnown nextSize (fun e mem => edgesSafe e (by simp [mem]))
      refine ⟨updated,?_,newFits,newHolds,newKnown,newSize,by omega,
        (join_extends fits incomingFits pcValid).trans growth,?_,?_,fun p mem => keep p (keepNext p mem)⟩
      · simpa only [enqueueEdges,nonempty,Bool.false_eq_true,↓reduceIte,
          show ¬ pc ≥ table.size by omega] using run
      · intro edge member
        rcases List.mem_cons.mp member with rfl | member
        · exact growth.edge (join_edge fits incomingFits pcValid)
        · exact validEdges edge member
      · intro p absent
        have notPending : p ∉ pending := fun mem => absent (keep p mem)
        exact (unchanged p absent).trans (join_unchanged notPending)

/-- Only pending nodes may need their outgoing edges recomputed. -/
def Settled (step : Nat → Frame → Except String (List (Nat × Frame)))
    (table : InvariantTable) (work : List Nat) : Prop :=
  ∀ pc, pc ∉ work → ∀ frame, table[pc]?.join = some frame →
    ∃ edges, step pc frame = .ok edges ∧ ∀ edge ∈ edges, validEdge table edge = true

/-- The actual inference engine succeeds when transfer preserves its declared
and point-specific invariants, with a budget derived from table dimensions. -/
theorem inferWorklist_complete (closed : TransferClosed top size allowed step)
    (fits : Fits top table) (holds : Frames allowed table) (known : Known table work)
    (settled : Settled step table work)
    (sized : table.size = size) (budget : tableBudget top table + work.length ≤ fuel) :
    ∃ result, inferWorklist top step fuel table work = .ok result ∧
      Fits top result ∧ Frames allowed result ∧ result.size = size ∧
      Extends table result ∧ Settled step result [] := by
  induction fuel generalizing table work with
  | zero =>
    cases work with
    | nil => exact ⟨table,rfl,fits,holds,sized,Extends.refl _,settled⟩
    | cons pc work => simp only [List.length_cons] at budget; omega
  | succ fuel ih =>
    cases work with
    | nil => exact ⟨table,rfl,fits,holds,sized,Extends.refl _,settled⟩
    | cons pc work =>
      obtain ⟨frame,found⟩ := known pc (by simp)
      have valid : pc < size := by
        by_cases valid : pc < size
        · exact valid
        · have none : table[pc]? = none := Array.getElem?_eq_none (by omega)
          simp [none] at found
      obtain ⟨edges,transfer,edgesSafe⟩ := closed.transfer pc frame valid (holds pc frame found) (fits pc frame found)
      obtain ⟨updated,enqueued,newFits,newHolds,newKnown,newSize,progress,growth,edgesValid,unchanged,keep⟩ := enqueue_complete (work := work) closed fits holds
        (fun n member => known n (by simp [member])) sized edgesSafe
      have remaining : tableBudget top updated.1 + updated.2.length ≤ fuel := by
        simp only [List.length_cons] at budget
        omega
      have newSettled : Settled step updated.1 updated.2 := by
        intro other absent f atFrame
        have oldFrame : table[other]?.join = some f := by rw [← unchanged other absent]; exact atFrame
        by_cases same : other = pc
        · subst other
          have eq : f = frame := Option.some.inj (oldFrame.symm.trans found)
          subst f
          exact ⟨edges,transfer,edgesValid⟩
        · have absentOld : other ∉ pc::work := by
            intro member
            rcases List.mem_cons.mp member with equal | member
            · exact same equal
            · exact absent (keep other member)
          obtain ⟨out,evaluated,valid⟩ := settled other absentOld f oldFrame
          exact ⟨out,evaluated,fun e mem => growth.edge (valid e mem)⟩
      obtain ⟨result,run,resultFits,resultFrames,resultSize,resultGrowth,resultSettled⟩ :=
        ih newFits newHolds newKnown newSettled newSize remaining
      refine ⟨result,?_,resultFits,resultFrames,resultSize,growth.trans resultGrowth,resultSettled⟩
      simpa [inferWorklist,found,transfer,enqueued,bind,Except.bind] using run

/-- The existing factor 32 exceeds the derived worklist bound; it is not an
unproved arbitrary termination allowance for frames satisfying the invariant. -/
theorem standard_budget (top : Frame) (table : InvariantTable) :
    tableBudget top table + 1 ≤ 32 * (table.size+1) * (top.length+1) := by
  have bound := tableBudget_le top table
  have arithmetic : table.size * (3*top.length+1) + 1 ≤ 32 * (table.size+1) * (top.length+1) := by
    calc
      _ ≤ (table.size+1) * (3*top.length+1) := by simp only [Nat.add_mul,Nat.one_mul]; omega
      _ ≤ (table.size+1) * (32*(top.length+1)) := Nat.mul_le_mul_left _ (by omega)
      _ = _ := by simp [Nat.mul_comm,Nat.mul_left_comm]
  omega

/-- Start the executable engine from its actual singleton worklist. -/
theorem initialized_complete (closed : TransferClosed top size allowed step)
    (entryValid : entry < size) (initialFits : Frame.within initial top = true)
    (initialAllowed : allowed entry initial) :
    ∃ result, inferWorklist top step (32*(size+1)*(top.length+1))
      ((Array.replicate size none).set! entry (some initial)) [entry] = .ok result ∧
      Fits top result ∧ Frames allowed result ∧ result.size = size ∧
      (∃ entryFrame, result[entry]?.join = some entryFrame ∧ initial.within entryFrame = true) ∧
      Settled step result [] := by
  let table : InvariantTable := (Array.replicate size none).set! entry (some initial)
  have known : Known table [entry] := by
    intro pc member
    simp only [List.mem_singleton] at member
    subst pc
    exact ⟨initial,by simp [table,entryValid]⟩
  have shape (pc : Nat) (frame : Frame) (found : table[pc]?.join = some frame) :
      pc = entry ∧ frame = initial := by
    by_cases same : pc = entry
    · subst pc
      have eq : initial = frame := by simpa [table,entryValid] using found
      exact ⟨rfl,eq.symm⟩
    · by_cases valid : pc < size
      · simp [table,Ne.symm same,valid] at found
      · simp [table,show size ≤ pc by omega] at found
  have fits : Fits top table := by
    intro pc frame found
    obtain ⟨_,rfl⟩ := shape pc frame found
    exact initialFits
  have holds : Frames allowed table := by
    intro pc frame found
    obtain ⟨rfl,rfl⟩ := shape pc frame found
    exact initialAllowed
  have settled : Settled step table [entry] := by
    intro pc absent frame found
    obtain ⟨eq,_⟩ := shape pc frame found
    exact False.elim (absent (by simp [eq]))
  obtain ⟨result,run,resultFits,resultHolds,resultSize,growth,checked⟩ :=
    inferWorklist_complete closed fits holds known settled (by simp [table])
      (show tableBudget top table + [entry].length ≤ 32*(size+1)*(top.length+1) by
        simpa [table] using standard_budget top table)
  exact ⟨result,run,resultFits,resultHolds,resultSize,
    growth entry initial (by simp [table,entryValid]),checked⟩

end IRComparison.Circuit.InferenceProgress

namespace IRComparison.Circuit

/-- Sequential graphs use the same complete inference engine and independent
checker as structured graphs. No successful-check premise is required. -/
theorem inferInvariant_complete
    (closed : InferenceProgress.TransferClosed a.wires.toList a.machine.nodes.size allowed
      (fun pc f => transfer f a.machine.nodes[pc]!))
    (entry : a.machine.entry < a.machine.nodes.size)
    (initialFits : (initialFrame a).within a.wires.toList = true)
    (initialAllowed : allowed a.machine.entry (initialFrame a)) :
    ∃ table, inferInvariant a = .ok table ∧ validInvariant a table = true := by
  obtain ⟨table,run,fits,_,sized,entryFrame,settled⟩ :=
    InferenceProgress.initialized_complete closed entry initialFits initialAllowed
  have valid : validInvariant a table = true := by
    simp only [validInvariant,Bool.and_eq_true,beq_iff_eq]
    refine ⟨⟨sized,?_⟩,List.all_eq_true.mpr ?_⟩
    · obtain ⟨frame,found,inside⟩ := entryFrame
      simpa [found] using inside
    · intro pc member
      have pcValid := List.mem_range.mp member
      cases found : table[pc]?.join with
      | none => simp [validNode,found]
      | some frame =>
        have inside := fits pc frame found
        have length : frame.length = a.wires.size := by simpa using Frame.within_length inside
        have nodeFound : a.machine.nodes[pc]? = some a.machine.nodes[pc] := Array.getElem?_eq_getElem pcValid
        obtain ⟨edges,evaluated,edgesValid⟩ := settled pc (by simp) frame found
        have moved : transfer frame a.machine.nodes[pc] = .ok edges := by simpa [getElem!_pos,pcValid] using evaluated
        simp only [validNode,found,length,BEq.rfl,inside,Bool.or_true,Bool.true_and,nodeFound,moved]
        exact List.all_eq_true.mpr edgesValid
  refine ⟨table,?_,valid⟩
  have run' : inferWorklist a.wires.toList (fun pc f => transfer f a.machine.nodes[pc]!)
      (32*(a.machine.nodes.size+1)*(a.wires.size+1))
      ((Array.replicate a.machine.nodes.size none).set! a.machine.entry (some (initialFrame a)))
      [a.machine.entry] = .ok table := by simpa using run
  simp only [inferInvariant,run',checkInvariant,valid,bind,Except.bind,pure,Except.pure,↓reduceIte]

end IRComparison.Circuit
