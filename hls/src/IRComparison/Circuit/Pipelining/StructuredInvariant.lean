import IRComparison.Circuit.Pipelining.StructuredRTL
import IRComparison.Circuit.InferenceTotal

namespace IRComparison.Circuit.Pipelining

variable {α : Type} [ExpressionEvaluation α] [ExpressionDependencies α] [ExpressionRange α]
variable {g : ClockGraph α} {as : List (Action α)}

/-- Propagate the existing interval transfer along the sequential meaning of
an ordered-safe clock. Guards still refine frames on individual graph edges. -/
def transferActions : Frame → List (Action α) → Except String Frame
  | f,[] => .ok f
  | f,a::as => do
    if f.empty then return f
    let edges ← transfer f (a.node 0)
    match edges with
    | [(_,after)] => transferActions after as
    | _ => throw "unexpected action transfer edges"

theorem transferActions_sound (hc : transferActions f as = .ok after)
    (hb : WidthBound f p) (he : evalList (Action.eval cap) as p = some q) : WidthBound after q := by
  induction as generalizing f after p with
  | nil => cases hc; cases he; exact hb
  | cons a as ih =>
    have nonempty := Frame.not_empty hb.wires
    simp only [transferActions,nonempty,Bool.false_eq_true,ite_false] at hc
    cases ht : transfer f (a.node 0) with
    | error why => simp [ht,bind,Except.bind,pure,Except.pure] at hc
    | ok edges =>
      simp only [ht,bind,Except.bind,pure,Except.pure] at hc
      split at hc
      · rename_i pc next
        cases ha : a.eval cap p with
        | none => simp [evalList,ha] at he
        | some r =>
          have ex : execute cap (a.node 0) (p.at 0) = some (r.at 0) := by rw [Action.execute_eq,ha]; rfl
          have hs := transfer_sound (a.node 0) hb ht ex
          rcases hs with done | ⟨ff,member,bound⟩
          · cases done
          · simp only [List.mem_singleton,Prod.mk.injEq] at member
            rcases member with ⟨_,rfl⟩
            exact ih hc bound (by simpa [evalList,ha] using he)
      · contradiction

def ClockNode.transfer (f : Frame) : ClockNode α → Except String (List (Nat × Frame))
  | .batch as next => do
      unless decide (BundleSafe as) do throw "unsafe ordered clock"
      return [(next,← transferActions f as)]
  | .branch e yes no => Circuit.transfer f (.branch e yes no)
  | .jump next => Circuit.transfer f (.jump next)
  | .halt => Circuit.transfer f .halt

theorem ClockNode.transfer_sound (n : ClockNode α) (hb : RuntimeBound f r)
    (hc : n.transfer f = .ok edges) (live : r.done = false) :
    (n.eval cap r).done = true ∨ ∃ after, ((n.eval cap r).pc,after) ∈ edges ∧ RuntimeBound after (n.eval cap r) := by
  cases n with
  | batch as next =>
    simp only [ClockNode.transfer] at hc
    split at hc <;> simp only [bind,Except.bind,pure,Except.pure] at hc
    · rename_i safe
      cases ht : transferActions f as <;> simp [ht] at hc
      rename_i after
      subst edges
      cases he : clock cap as r.payload with
      | none => exact Or.inl (by simp [ClockNode.eval,he])
      | some q =>
        have eval : evalList (Action.eval cap) as r.payload = some q := by
          rw [← clock_correct as (of_decide_eq_true safe)]; exact he
        have num := transferActions_sound ht (show WidthBound f r.payload from ⟨hb.data,hb.wires,hb.queues⟩) eval
        simp only [ClockNode.eval,he]
        exact Or.inr ⟨after,by simp,⟨num.data,num.wires,num.queues⟩⟩
    · contradiction
  | branch e yes no =>
    cases he : ExpressionEvaluation.eval e r.data r.wires with
    | none => exact Or.inl (by simp [ClockNode.eval,he])
    | some v =>
      have ex : execute cap (.branch e yes no) r = some (ClockNode.eval cap (.branch e yes no) r) := by simp [execute,ClockNode.eval,he]
      exact Circuit.transfer_sound (.branch e yes no) hb hc ex
  | jump next => exact Circuit.transfer_sound (capacity := cap) (.jump next) hb hc rfl
  | halt => exact Or.inl rfl

def validClockNode (a : Artifact) (g : ClockGraph α) (table : InvariantTable) (pc : Nat) : Bool :=
  match table[pc]?.join with
  | none => true
  | some frame =>
    frame.length == a.wires.size && (frame.empty || frame.within a.wires.toList) &&
    match g.nodes[pc]? with
    | none => false
    | some n => match n.transfer frame with
      | .error _ => false
      | .ok edges => edges.all (validEdge table)

def validClockInvariant (a : Artifact) (g : ClockGraph α) (table : InvariantTable) : Bool :=
  table.size == g.nodes.size &&
  (match table[1]?.join with
   | none => false
   | some entry => (initialFrame a).within entry) &&
  (List.range g.nodes.size).all (validClockNode a g table)

def inferClockInvariant (a : Artifact) (g : ClockGraph α) : Except String InvariantTable := do
  let table : InvariantTable := (Array.replicate g.nodes.size none).set! 1 (some (initialFrame a))
  inferWorklist a.wires.toList (fun pc f => do
    let some node := g.nodes[pc]? | throw "invalid structured node"
    node.transfer f) (32 * (g.nodes.size+1) * (a.wires.size+1)) table [1]

/-- Point-specific transfer and widening obligations imply success of both
the executable inference and its independent inductiveness checker. -/
theorem inferClockInvariant_complete
    (closed : InferenceProgress.TransferClosed a.wires.toList g.nodes.size allowed
      (fun pc f => do
        let some node := g.nodes[pc]? | throw "invalid structured node"
        node.transfer f))
    (entry : 1 < g.nodes.size)
    (initialFits : Frame.within (initialFrame a) a.wires.toList = true)
    (initialAllowed : allowed 1 (initialFrame a)) :
    ∃ table, inferClockInvariant a g = .ok table ∧
      InferenceProgress.Fits a.wires.toList table ∧
      InferenceProgress.Frames allowed table ∧ table.size = g.nodes.size ∧
      validClockInvariant a g table = true := by
  obtain ⟨table,run,fits,holds,sized,entryFrame,settled⟩ :=
    InferenceProgress.initialized_complete closed entry initialFits initialAllowed
  refine ⟨table,by simpa [inferClockInvariant] using run,fits,holds,sized,?_⟩
  simp only [validClockInvariant,Bool.and_eq_true,beq_iff_eq]
  refine ⟨⟨sized,?_⟩,List.all_eq_true.mpr ?_⟩
  · obtain ⟨frame,found,inside⟩ := entryFrame
    simpa [found] using inside
  · intro pc member
    have valid := List.mem_range.mp member
    cases found : table[pc]?.join with
    | none => simp [validClockNode,found]
    | some frame =>
      have inside := fits pc frame found
      have length : frame.length = a.wires.size := by
        simpa using Frame.within_length inside
      have nodeFound : g.nodes[pc]? = some g.nodes[pc] := Array.getElem?_eq_getElem valid
      obtain ⟨edges,evaluated,edgesValid⟩ := settled pc (by simp) frame found
      have transfer : g.nodes[pc].transfer frame = .ok edges := by
        simpa [nodeFound] using evaluated
      simp only [validClockNode,found,length,BEq.rfl,inside,Bool.or_true,Bool.true_and,
        nodeFound,transfer]
      exact List.all_eq_true.mpr edgesValid

/-- The worklist is only a proposal. The caller separately checks every
entry and edge with validClockInvariant before accepting the graph. -/
theorem validClockInvariant_size (h : validClockInvariant a g table = true) : table.size = g.nodes.size := by
  simp only [validClockInvariant,Bool.and_eq_true,beq_iff_eq] at h
  exact h.1.1

theorem validClockInvariant_node (h : validClockInvariant a g table = true) (hp : pc < g.nodes.size) :
    validClockNode a g table pc = true := by
  simp only [validClockInvariant,Bool.and_eq_true,List.all_eq_true] at h
  exact h.2 pc (List.mem_range.mpr hp)

theorem clock_tick_table (h : validClockInvariant a g table = true) (hr : TableBound table r) :
    TableBound table (g.tick r) := by
  by_cases hd : r.done = true
  · simpa [ClockGraph.tick,hd] using hr
  · rcases hr with done | ⟨f,hf,hb⟩
    · contradiction
    have hp : r.pc < table.size := by
      by_cases hp : r.pc < table.size
      · exact hp
      have hn := Array.getElem?_eq_none (xs:=table) (by omega : table.size ≤ r.pc)
      simp [hn] at hf
    have hn := validClockInvariant_node h (by rw [← validClockInvariant_size h]; exact hp)
    simp only [validClockNode,hf] at hn
    cases hc : g.nodes[r.pc]? with
    | none => simp [hc] at hn
    | some node =>
      cases ht : node.transfer f with
      | error why => simp [hc,ht] at hn
      | ok edges =>
        have hall : edges.all (validEdge table) = true := by
          simp only [hc,ht,Bool.and_eq_true] at hn
          exact hn.2
        have step : g.tick r = node.eval g.capacity r := by simp [ClockGraph.tick,hd,hc]
        rw [step]
        rcases node.transfer_sound hb ht (Bool.eq_false_iff.mpr hd) with done | ⟨after,member,bound⟩
        · exact Or.inl done
        · have edge := List.all_eq_true.mp hall _ member
          simp only [validEdge,Frame.not_empty bound.wires,Bool.false_or] at edge
          cases htarget : table[(node.eval g.capacity r).pc]?.join with
          | none => simp [htarget] at edge
          | some target => exact Or.inr ⟨target,htarget,bound.within (by simpa [htarget] using edge)⟩

theorem clock_table_global (h : validClockInvariant a g table = true) (hr : TableBound table r)
    (hd : r.done = false) : RuntimeBound a.wires.toList r := by
  rcases hr with done | ⟨f,hf,hb⟩
  · simp [hd] at done
  have hp : r.pc < table.size := by
    by_cases hp : r.pc < table.size
    · exact hp
    have hn := Array.getElem?_eq_none (xs:=table) (by omega : table.size ≤ r.pc)
    simp [hn] at hf
  have hn := validClockInvariant_node h (by rw [← validClockInvariant_size h]; exact hp)
  simp only [validClockNode,hf,Bool.and_eq_true,Frame.not_empty hb.wires,Bool.false_or] at hn
  exact hb.within hn.1.2

theorem clock_initial_table (h : validClockInvariant a g table = true) (hsize : 2 ≤ a.wires.size)
    (s : HybridWord.State) (x y : HybridWord.Word) : TableBound table ((wordPayload s x y).at 1) := by
  have he : (match table[1]?.join with
    | none => false | some entry => (initialFrame a).within entry) = true := by
      simp only [validClockInvariant,Bool.and_eq_true] at h
      exact h.1.2
  cases ht : table[1]?.join with
  | none => simp [ht] at he
  | some f =>
    have hb := initial_frame_bound a hsize s x y
    exact Or.inr ⟨f,ht,(show RuntimeBound (initialFrame a) ((wordPayload s x y).at 1) from
      ⟨hb.data,hb.wires,hb.queues⟩).within (by simpa [ht] using he)⟩

end IRComparison.Circuit.Pipelining
