import IRComparison.Circuit.CompactLoadOneSound

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
