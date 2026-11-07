import IRComparison.Circuit.LoadOneSound

namespace IRComparison.Circuit

def observeLoads (qi : Nat) (slots : List Nat) (p : Payload) : State × List Int × List Int :=
  (p.data,slots.map p.wires,p.queues qi)

/-- A whole buffer refill is evaluated before its values are exposed to the
body. Fresh, increasing destinations preserve the previous buffer's captures. -/
theorem expandedLoads_correct (input qi : Nat) (old : List Expr) (loads : List WindowFIFO.Load)
    (slots : List Nat) (b : Build) (p : Payload) (low : Nat) (values : List Int)
    (lengths : loads.length = slots.length) (ordered : slots.Pairwise (· < ·))
    (bounds : ∀ n ∈ slots, low ≤ n ∧ n < b.wires.size) (lowBound : low ≤ b.wires.size)
    (scopeOK : ∀ e ∈ old, Static low e) (hm : Matches p.data p.wires old values) :
    ∃ result, ((expandedLoads input qi old loads slots).run b).1.Eval cap p result ∧
      result.map (observeLoads qi slots) =
        (WindowFIFO.execute (arrayInput (p.data.arrays input)) values loads (p.queues qi)).map
          (fun (vs,qs) => (p.data,vs,qs)) := by
  induction loads generalizing slots b p with
  | nil => cases slots with
    | nil => exact ⟨some p,.skip,rfl⟩
    | cons => simp at lengths
  | cons l loads ih =>
    cases slots with
    | nil => simp at lengths
    | cons slot slots =>
      have hlens : loads.length = slots.length := by simpa using lengths
      have hpairs := List.pairwise_cons.mp ordered
      have hslot := bounds slot (by simp)
      have hf := loadOne_frame (low:=low) b input qi slot old l lowBound hslot.1
      obtain ⟨r,hr,ho⟩ := loadOne_correct (cap:=cap) b input qi slot old l p hm
      dsimp only [expandedLoads,bind,pure,StateT.bind,StateT.pure,StateT.run]
      dsimp only [StateT.run] at hf hr
      generalize hcompile : loadOne input qi old slot l b = pair at *
      obtain ⟨first,b1⟩ := pair
      dsimp only
      cases hl : l.eval (arrayInput (p.data.arrays input)) values (p.queues qi) with
      | none =>
        have rr : r = none := by cases r <;> simp_all
        subst r
        exact ⟨none,.seq_error hr,by simp [WindowFIFO.execute,hl]⟩
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
          have tailFrame := expandedLoads_frame input qi old loads slots b1 (slot+1)
            (Nat.succ_le_of_lt (Nat.lt_of_lt_of_le hslot.2 hf.1)) (fun n hn => by have := hpairs.1 n hn; omega) hlens
          have hhead : ∀ t, r' = some t → t.wires slot = v := by
            intro t ht
            have stable := ((expandedLoads input qi old loads slots).run b1).1.preserves_below hr' tailFrame.2 ht
            exact (stable slot (by omega)).symm.trans hobs.2.1
          refine ⟨r',.seq hr hr',?_⟩
          have lifted := congrArg (Option.map (fun (s,vs,qs) => (s,v::vs,qs))) ho'
          simp only [Option.map_map] at lifted
          cases hrval : r' with
          | none =>
            cases htail : WindowFIFO.execute (arrayInput (p.data.arrays input)) values loads qs <;>
            simpa [htail,hrval,WindowFIFO.execute,hl,hobs.1,hobs.2.2,Option.map_bind,bind,Option.bind] using lifted
          | some t =>
            have ht := hhead t hrval
            cases htail : WindowFIFO.execute (arrayInput (p.data.arrays input)) values loads qs <;>
            simpa [htail,hrval,observeLoads,ht,WindowFIFO.execute,hl,hobs.1,hobs.2.2,Option.map_bind,bind,Option.bind] using lifted

end IRComparison.Circuit
