import IRComparison.Circuit.TakeSound

namespace IRComparison.Circuit

theorem take_frame (b : Build) (qi slot : Nat) (e : Expr) (low : Nat)
    (hb : low ≤ b.wires.size) (hs : low ≤ slot) :
    b.wires.size ≤ ((take qi slot e).run b).2.wires.size ∧ ((take qi slot e).run b).1.above low := by
  simp only [take,freshFor,bounds,fresh,bind,pure,StateT.bind,StateT.pure,StateT.run]
  simp only [Build.addWire,Array.size_push,counterLoop,Schedule.above,Action.above]
  omega

theorem expandedLoads_frame (input qi : Nat) (old : List Expr) (loads : List WindowFIFO.Load)
    (slots : List Nat) (b : Build) (low : Nat)
    (hb : low ≤ b.wires.size) (hs : ∀ slot ∈ slots, low ≤ slot)
    (lengths : loads.length = slots.length) :
    b.wires.size ≤ ((expandedLoads input qi old loads slots).run b).2.wires.size ∧
      ((expandedLoads input qi old loads slots).run b).1.above low := by
  induction loads generalizing slots b with
  | nil => cases slots with
    | nil => exact ⟨Nat.le_refl _,True.intro⟩
    | cons => simp at lengths
  | cons load loads ih =>
    cases slots with
    | nil => simp at lengths
    | cons slot slots =>
      have hslot := hs slot (by simp)
      have htail : ∀ n ∈ slots, low ≤ n := fun n hn => hs n (by simp [hn])
      have hlen : loads.length = slots.length := by simpa using lengths
      cases load with
      | memory a | saved n =>
        have h := ih slots b hb htail hlen
        dsimp only [expandedLoads,loadOne,bind,pure,StateT.bind,StateT.pure,StateT.run]
        dsimp only [StateT.run] at h
        generalize he : expandedLoads input qi old loads slots b = pair at *
        obtain ⟨tail,b'⟩ := pair
        exact ⟨h.1,⟨hslot,h.2⟩⟩
      | take n =>
        dsimp only [expandedLoads,loadOne,bind,pure,StateT.bind,StateT.pure,StateT.run]
        have hfirst := take_frame b qi slot (.lit n) low hb hslot
        dsimp only [StateT.run] at hfirst
        generalize he : take qi slot (.lit n) b = pair at *
        obtain ⟨first,b1⟩ := pair
        dsimp only
        have ht := ih slots b1 (Nat.le_trans hb hfirst.1) htail hlen
        dsimp only [StateT.run] at ht
        generalize he' : expandedLoads input qi old loads slots b1 = pair' at *
        obtain ⟨tail,b2⟩ := pair'
        exact ⟨Nat.le_trans hfirst.1 ht.1,⟨hfirst.2,ht.2⟩⟩

theorem copies_frame (dst src : List Nat) (h : ∀ slot ∈ dst, low ≤ slot) : (copies dst src).above low := by
  induction dst generalizing src with
  | nil => trivial
  | cons d ds ih =>
    cases src with
    | nil => trivial
    | cons s ss => exact ⟨h d (by simp),ih ss (fun n hn => h n (by simp [hn]))⟩

end IRComparison.Circuit
