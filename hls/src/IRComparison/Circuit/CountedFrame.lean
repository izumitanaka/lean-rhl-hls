import IRComparison.Circuit.ResourceFrame
import IRComparison.Circuit.CountedRound

namespace IRComparison.Circuit

def Grows (f : Builder α) : Prop := ∀ b, b.wires.size ≤ (f b).2.wires.size

theorem grows_pure (a : α) : Grows (pure a) := fun _ => Nat.le_refl _
theorem grows_bind (f : Builder α) (g : α → Builder β) (hf : Grows f) (hg : ∀ a, Grows (g a)) :
    Grows (f >>= g) := fun b => Nat.le_trans (hf b) (hg (f b).1 (f b).2)
theorem grows_fresh (r : Interval) : Grows (fresh r) := by intro b; simp [fresh,Build.addWire]

theorem loads_grows (i : Expr) (input qi : Nat) (old : List Expr) (items : List Load) (slots : List Nat) :
    Grows (loads i input qi old items slots) := by
  induction items generalizing slots with
  | nil => exact grows_pure _
  | cons l ls ih =>
    cases slots with
    | nil => exact grows_pure _
    | cons n ns =>
      exact grows_bind _ _ (fun b => (compactLoadOne_frame b input qi n i old l (Nat.zero_le _) (Nat.zero_le _)).1)
        (fun _ => grows_bind _ _ (ih ns) (fun _ => grows_pure _))

theorem prepareCounted_grows (start stride : Int) (count : Nat) (initial refill : List Load)
    (body : HybridIR.Cmd) (input qi qo : Nat) :
    Grows (prepareCounted start stride count initial refill body input qi qo) := by
  apply grows_bind _ _ (grows_fresh _)
  intro k
  apply grows_bind _ _ (fun b => by have h := (newSlots_shape (max initial.length refill.length) b).2; dsimp only [StateT.run] at h; omega)
  intro held
  apply grows_bind _ _ (fun b => by have h := (newSlots_shape refill.length b).2; dsimp only [StateT.run] at h; omega)
  intro scratch
  apply grows_bind _ _ (loads_grows _ _ _ _ _ _)
  intro _
  apply grows_bind _ _ (fun b => (command_frame _ _ _ _ b).1)
  intro _
  apply grows_bind _ _ (loads_grows _ _ _ _ _ _)
  intro _
  apply grows_bind _ _ (loads_grows _ _ _ _ _ _)
  intro _
  exact grows_bind _ _ (fun b => (command_frame _ _ _ _ b).1) (fun _ => grows_pure _)

theorem counted_grows (start stride : Int) (count : Nat) (initial refill : List Load)
    (body : HybridIR.Cmd) (input qi qo : Nat) : Grows (counted start stride count initial refill body input qi qo) := by
  intro b
  by_cases hz : count = 0
  · simp [counted,hz,pure,StateT.pure]
  · have h := prepareCounted_grows start stride count initial refill body input qi qo b
    simpa [counted,hz,bind,pure,StateT.bind,StateT.pure] using h

theorem counted_frame (start stride : Int) (count : Nat) (initial refill : List Load)
    (body : HybridIR.Cmd) (input qi qo : Nat) (b : Build) (inputs : 2 ≤ b.wires.size) :
    (counted start stride count initial refill body input qi qo b).1.above b.wires.size := by
  by_cases hz : count = 0
  · simp [counted,hz,Schedule.above,pure,StateT.pure]
  · have h := (prepareCounted_parts start stride count initial refill body input qi qo b inputs).round_frame
    have counter := prepareCounted_counter start stride count initial refill body input qi qo b
    generalize he : prepareCounted start stride count initial refill body input qi qo b = pair at *
    obtain ⟨c,b1⟩ := pair
    dsimp only at h counter
    have frame : (counterLoop c.counter (.lit count) (c.round refill.length)).above b.wires.size := by
      refine ⟨?_,?_,?_⟩
      · change b.wires.size ≤ c.counter; omega
      · exact (c.round refill.length).above_mono h (by omega)
      · change b.wires.size ≤ c.counter; omega
    simpa [counted,hz,bind,pure,StateT.bind,StateT.pure,he] using frame

theorem copies_noQueue (dest source : List Nat) : (copies dest source).noQueue q := by
  induction dest generalizing source with
  | nil => trivial
  | cons d ds ih => cases source with
    | nil => trivial
    | cons s ss => exact ⟨True.intro,ih ss⟩

theorem counted_noQueue (start stride : Int) (count : Nat) (initial refill : List Load)
    (body : HybridIR.Cmd) (input qi qo : Nat) (b : Build) (inputs : 2 ≤ b.wires.size)
    (hin : qi ≠ protectedQueue) (hout : qo ≠ protectedQueue) :
    (counted start stride count initial refill body input qi qo b).1.noQueue protectedQueue := by
  by_cases hz : count = 0
  · simp [counted,hz,Schedule.noQueue,pure,StateT.pure]
  · have h := prepareCounted_parts start stride count initial refill body input qi qo b inputs
    generalize he : prepareCounted start stride count initial refill body input qi qo b = pair at *
    obtain ⟨c,b1⟩ := pair
    have frame : (counterLoop c.counter (.lit count) (c.round refill.length)).noQueue protectedQueue :=
      ⟨True.intro,⟨⟨⟨h.later.queueFrame _ hin,h.firstRefill.queueFrame _ hin⟩,
        ⟨copies_noQueue _ _,h.laterBody.queueFrame _ hout⟩⟩,
        ⟨h.first.queueFrame _ hin,h.firstBody.queueFrame _ hout⟩⟩,True.intro⟩
    simpa [counted,hz,bind,pure,StateT.bind,StateT.pure,he] using frame

end IRComparison.Circuit
