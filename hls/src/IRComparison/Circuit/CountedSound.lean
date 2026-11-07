import IRComparison.Circuit.CountedRound
import IRComparison.Circuit.IndexedCounter
import IRComparison.Circuit.BlocksSound

namespace IRComparison.Circuit

def boundedCounted (capacity input : Nat) (start stride : Int) (count : Nat)
    (initial refill : List Load) (body : HybridIR.Cmd) (x y : Int)
    (s : State) (qi qo : List Int) : Option (State × List Int × List Int) :=
  ((List.range' 0 count).foldlM
    (fun state j => countedStep capacity input start stride x y initial refill body j state)
    (s,[],qi,qo)).map (fun (t,_,rest,out) => (t,rest,out))

theorem CountedLayout.view_setWire (c : CountedLayout) (h : ∀ n ∈ c.held, c.counter < n) :
    c.view initialSize refillSize qi qo j (p.setWire c.counter v) =
      c.view initialSize refillSize qi qo j p := by
  simp only [CountedLayout.view,roundView,Payload.setWire]
  congr 2
  apply List.map_congr_left
  intro n hn
  have mem : n ∈ c.held := by
    unfold CountedLayout.saved at hn
    split at hn
    · contradiction
    · exact List.mem_of_mem_take hn
  simp [show n ≠ c.counter from by have := h n mem; omega]

/-- Compact loops execute with a fixed finite bank: the saved-window view may
change length, but the counter never overwrites a saved value. -/
theorem CountedParts.loop_correct (h : CountedParts c start stride initial refill body input qi qo)
    {count : Nat} (distinct : qi ≠ qo) (p : Payload) (hx : p.wires 0 = x) (hy : p.wires 1 = y) :
    ∃ r, (counterLoop c.counter (.lit count) (c.round refill.length)).Eval cap p r ∧
      r.map (observeBlock qi qo) =
        boundedCounted (cap qo) input start stride count initial refill body x y p.data (p.queues qi) (p.queues qo) := by
  let view := c.view initial.length refill.length qi qo
  let P := fun (_ : Nat) (q : Payload) => q.wires 0 = x ∧ q.wires 1 = y
  have counterPositive := h.inputs
  have initP : P 0 (p.setWire c.counter 0) := by
    simp [P,Payload.setWire,show 0 ≠ c.counter from by omega,show 1 ≠ c.counter from by omega,hx,hy]
  have increment : ∀ j q v, P j q → P j (q.setWire c.counter v) := by
    intro j q v hq
    simpa [P,Payload.setWire,show 0 ≠ c.counter from by omega,show 1 ≠ c.counter from by omega] using hq
  have bodyCorrect : ∀ (j : Nat) q, j < count → P j q → q.wires c.counter = (j:Int) →
      ∃ r, (c.round refill.length).Eval cap q r ∧
        r.map (view (j+1)) = countedStep (cap qo) input start stride x y initial refill body j (view j q) ∧
        ∀ t, r = some t → P (j+1) t ∧ t.wires c.counter = (j:Int) := by
    intro j q _ hp hk
    obtain ⟨r,hr,ho⟩ := h.round_correct distinct q j hk hp.1 hp.2
    refine ⟨r,hr,ho,?_⟩
    intro t ht
    have stable := (c.round refill.length).preserves_below hr h.round_frame ht
    exact ⟨⟨(stable 0 (by omega)).symm.trans hp.1,(stable 1 (by omega)).symm.trans hp.2⟩,
      (stable c.counter (by omega)).symm.trans hk⟩
  obtain ⟨r,hr,ho,_⟩ := counter_iterations_indexed
    (view:=view) (P:=P) (f:=countedStep (cap qo) input start stride x y initial refill body)
    (fun _ _ _ => c.view_setWire h.heldAbove) increment bodyCorrect count 0 (by omega)
    (p.setWire c.counter 0) initP (by simp [Payload.setWire])
  refine ⟨r,.seq (setWire_eval rfl) hr,?_⟩
  have projected := congrArg (Option.map (fun (t,_,rest,out) => (t,rest,out))) ho
  simpa [Option.map_map,Function.comp_def,view,CountedLayout.view,CountedLayout.saved,
    roundView,observeBlock,Payload.setWire,boundedCounted] using projected

/-- General theorem for the actual compact-loop lowering function, including
zero iterations, arbitrary strides and changing window sizes. Finite send
capacity is still explicit in the source-side bounded evaluator. -/
theorem counted_correct (start stride : Int) (count : Nat) (initial refill : List Load)
    (body : HybridIR.Cmd) (input qi qo : Nat) (b : Build) (p : Payload)
    (inputs : 2 ≤ b.wires.size) (distinct : qi ≠ qo) (hx : p.wires 0 = x) (hy : p.wires 1 = y) :
    ∃ r, ((counted start stride count initial refill body input qi qo).run b).1.Eval cap p r ∧
      r.map (observeBlock qi qo) =
        boundedCounted (cap qo) input start stride count initial refill body x y p.data (p.queues qi) (p.queues qo) := by
  by_cases zero : count = 0
  · subst count
    exact ⟨some p,.skip,rfl⟩
  · have parts := prepareCounted_parts start stride count initial refill body input qi qo b inputs
    have result := parts.loop_correct (count:=count) (cap:=cap) distinct p hx hy
    simpa [counted,zero,StateT.run,bind,StateT.bind,pure,StateT.pure] using result

end IRComparison.Circuit
