import IRComparison.Circuit.LoadsSound
namespace IRComparison.Circuit

def Load.at (index : Int) : Load → WindowFIFO.Load
  | .memory a => .memory (a.eval index)
  | .saved n => .saved n
  | .take n => .take (n.eval index).toNat

theorem linear_correct (a : AffineAddress.Linear) (h : i.eval s w = some v) :
    (linear i a).eval s w = some (a.eval v) := by
  simp [linear,Expr.eval,h,Bin.eval,AffineAddress.Linear.eval]

theorem compactLoadOne_frame (b : Build) (input qi slot : Nat) (i : Expr) (old : List Expr) (l : Load)
    (hb : low ≤ b.wires.size) (hs : low ≤ slot) :
    b.wires.size ≤ ((compactLoadOne i input qi old slot l).run b).2.wires.size ∧
    ((compactLoadOne i input qi old slot l).run b).1.above low := by
  cases l with
  | memory | saved => exact ⟨Nat.le_refl _,hs⟩
  | take n => exact take_frame b qi slot (linear i n) low hb hs

theorem compactLoadOne_correct (b : Build) (input qi slot : Nat) (i : Expr) (old : List Expr) (l : Load) (p : Payload)
    (hi : i.eval p.data p.wires = some index) (hm : Matches p.data p.wires old values) :
    ∃ result, ((compactLoadOne i input qi old slot l).run b).1.Eval cap p result ∧
      result.map (observeTake qi slot) =
        ((l.at index).eval (arrayInput (p.data.arrays input)) values (p.queues qi)).map (fun (v,qs) => (p.data,v,qs)) := by
  cases l with
  | take n =>
    obtain ⟨r,hr,ho⟩ := take_correct (cap:=cap) b qi slot (linear i n) p
    refine ⟨r,hr,?_⟩
    cases hn : (p.queues qi)[(n.eval index).toNat]? <;>
    simpa [Load.at,linear_correct n hi,WindowFIFO.Load.eval,hn] using ho
  | memory a =>
    refine ⟨_,Schedule.Eval.step,?_⟩
    simp only [Action.eval,Action.node,execute,expressionEvaluation_original,Payload.at,Expr.eval,linear_correct a hi,bind,Option.bind,Load.at,WindowFIFO.Load.eval]
    cases arrayInput (p.data.arrays input) (a.eval index) <;> simp [observeTake,Runtime.payload,Runtime.setWire]
  | saved n =>
    refine ⟨_,Schedule.Eval.step,?_⟩
    simp only [Action.eval,Action.node,execute,expressionEvaluation_original,Payload.at,hm n,Load.at,WindowFIFO.Load.eval]
    cases values[n]? <;> simp [observeTake,Runtime.payload,Runtime.setWire]

end IRComparison.Circuit

namespace IRComparison.Circuit

theorem compactLoads_frame (i : Expr) (input qi : Nat) (old : List Expr) (items : List Load)
    (slots : List Nat) (b : Build) (low : Nat)
    (hb : low ≤ b.wires.size) (hs : ∀ slot ∈ slots, low ≤ slot)
    (lengths : items.length = slots.length) :
    b.wires.size ≤ ((loads i input qi old items slots).run b).2.wires.size ∧
      ((loads i input qi old items slots).run b).1.above low := by
  induction items generalizing slots b with
  | nil => cases slots with
    | nil => exact ⟨Nat.le_refl _,True.intro⟩
    | cons => simp at lengths
  | cons load items ih =>
    cases slots with
    | nil => simp at lengths
    | cons slot slots =>
      have hslot := hs slot (by simp)
      have htail : ∀ n ∈ slots, low ≤ n := fun n hn => hs n (by simp [hn])
      have hlen : items.length = slots.length := by simpa using lengths
      cases load with
      | memory a | saved n =>
        have h := ih slots b hb htail hlen
        dsimp only [loads,compactLoadOne,bind,pure,StateT.bind,StateT.pure,StateT.run]
        dsimp only [StateT.run] at h
        generalize he : loads i input qi old items slots b = pair at *
        obtain ⟨tail,b'⟩ := pair
        exact ⟨h.1,⟨hslot,h.2⟩⟩
      | take n =>
        dsimp only [loads,compactLoadOne,bind,pure,StateT.bind,StateT.pure,StateT.run]
        have hfirst := take_frame b qi slot (linear i n) low hb hslot
        dsimp only [StateT.run] at hfirst
        generalize he : take qi slot (linear i n) b = pair at *
        obtain ⟨first,b1⟩ := pair
        dsimp only
        have ht := ih slots b1 (Nat.le_trans hb hfirst.1) htail hlen
        dsimp only [StateT.run] at ht
        generalize he' : loads i input qi old items slots b1 = pair' at *
        obtain ⟨tail,b2⟩ := pair'
        exact ⟨Nat.le_trans hfirst.1 ht.1,⟨hfirst.2,ht.2⟩⟩


end IRComparison.Circuit

namespace IRComparison.Circuit

/-- A whole buffer refill is evaluated before its values are exposed to the
body. Fresh, increasing destinations preserve the previous buffer's captures. -/
theorem compactLoads_correct (i : Expr) (input qi : Nat) (old : List Expr) (items : List Load)
    (slots : List Nat) (b : Build) (p : Payload) (low : Nat) (values : List Int)
    (lengths : items.length = slots.length) (ordered : slots.Pairwise (· < ·))
    (bounds : ∀ n ∈ slots, low ≤ n ∧ n < b.wires.size) (lowBound : low ≤ b.wires.size)
    (scopeOK : ∀ e ∈ old, Static low e) (hm : Matches p.data p.wires old values)
    (indexScope : Static low i) (hi : i.eval p.data p.wires = some index) :
    ∃ result, ((loads i input qi old items slots).run b).1.Eval cap p result ∧
      result.map (observeLoads qi slots) =
        (WindowFIFO.execute (arrayInput (p.data.arrays input)) values (items.map (Load.at index)) (p.queues qi)).map
          (fun (vs,qs) => (p.data,vs,qs)) := by
  induction items generalizing slots b p with
  | nil => cases slots with
    | nil => exact ⟨some p,.skip,rfl⟩
    | cons => simp at lengths
  | cons l items ih =>
    cases slots with
    | nil => simp at lengths
    | cons slot slots =>
      have hlens : items.length = slots.length := by simpa using lengths
      have hpairs := List.pairwise_cons.mp ordered
      have hslot := bounds slot (by simp)
      have hf := compactLoadOne_frame (low:=low) b input qi slot i old l lowBound hslot.1
      obtain ⟨r,hr,ho⟩ := compactLoadOne_correct (cap:=cap) b input qi slot i old l p hi hm
      dsimp only [loads,bind,pure,StateT.bind,StateT.pure,StateT.run]
      dsimp only [StateT.run] at hf hr
      generalize hcompile : compactLoadOne i input qi old slot l b = pair at *
      obtain ⟨first,b1⟩ := pair
      dsimp only
      cases hl : (l.at index).eval (arrayInput (p.data.arrays input)) values (p.queues qi) with
      | none =>
        have rr : r = none := by cases r <;> simp_all
        subst r
        exact ⟨none,.seq_error hr,by simp [List.map_cons,WindowFIFO.execute,expressionEvaluation_original,hl]⟩
      | some pair =>
        obtain ⟨v,qs⟩ := pair
        cases r with
        | none => simp [hl] at ho
        | some q =>
          have hobs : q.data = p.data ∧ q.wires slot = v ∧ q.queues qi = qs := by
            simpa [hl,observeTake] using ho
          have hw := first.preserves_below hr hf.2 rfl
          have hm' : Matches q.data q.wires old values := by
            intro n
            exact ((lookup_static scopeOK).stable hw).symm.trans (hm n)
          have hbounds : ∀ n ∈ slots, low ≤ n ∧ n < b1.wires.size := by
            intro n hn
            have hn := bounds n (by simp [hn])
            exact ⟨hn.1,Nat.lt_of_lt_of_le hn.2 hf.1⟩
          obtain ⟨r',hr',ho'⟩ := ih slots b1 q hlens hpairs.2 hbounds (Nat.le_trans lowBound hf.1) hm'
            ((indexScope.stable hw).symm.trans hi)
          have tailFrame := compactLoads_frame i input qi old items slots b1 (slot+1)
            (Nat.succ_le_of_lt (Nat.lt_of_lt_of_le hslot.2 hf.1)) (fun n hn => by have := hpairs.1 n hn; omega) hlens
          have hhead : ∀ t, r' = some t → t.wires slot = v := by
            intro t ht
            have stable := ((loads i input qi old items slots).run b1).1.preserves_below hr' tailFrame.2 ht
            exact (stable slot (by omega)).symm.trans hobs.2.1
          refine ⟨r',.seq hr hr',?_⟩
          have lifted := congrArg (Option.map (fun (s,vs,qs) => (s,v::vs,qs))) ho'
          simp only [Option.map_map] at lifted
          cases hrval : r' with
          | none =>
            cases htail : WindowFIFO.execute (arrayInput (p.data.arrays input)) values (items.map (Load.at index)) qs <;>
            simpa [htail,hrval,List.map_cons,WindowFIFO.execute,expressionEvaluation_original,hl,hobs.1,hobs.2.2,Option.map_bind,bind,Option.bind] using lifted
          | some t =>
            have ht := hhead t hrval
            cases htail : WindowFIFO.execute (arrayInput (p.data.arrays input)) values (items.map (Load.at index)) qs <;>
            simpa [htail,hrval,observeLoads,ht,List.map_cons,WindowFIFO.execute,expressionEvaluation_original,hl,hobs.1,hobs.2.2,Option.map_bind,bind,Option.bind] using lifted

end IRComparison.Circuit
