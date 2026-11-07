import IRComparison.Circuit.StageParts
import IRComparison.Circuit.Allocate

namespace IRComparison.Circuit

def CountedLayout.index (c : CountedLayout) (start stride : Int) : Expr :=
  .bin .add (.lit start) (.bin .mul (.wire c.counter) (.lit stride))

/-- Static allocation facts, including the distinct scratch bank used before
copying a refilled window into its persistent holding registers. -/
structure CountedParts (c : CountedLayout) (start stride : Int) (initial refill : List Load)
    (body : HybridIR.Cmd) (input qi qo : Nat) where
  inputs : 2 ≤ c.counter
  first : WindowSpec c.firstLoads (c.index start stride) input qi [] initial (c.held.take initial.length)
  firstBody : BodySpec c.firstBody (c.index start stride) ((c.held.take initial.length).map Expr.wire) body qo
  firstRefill : WindowSpec c.firstRefill (c.index start stride) input qi
    ((c.held.take initial.length).map Expr.wire) refill c.scratch
  later : WindowSpec c.laterLoads (c.index start stride) input qi
    ((c.held.take refill.length).map Expr.wire) refill c.scratch
  laterBody : BodySpec c.laterBody (c.index start stride) ((c.held.take refill.length).map Expr.wire) body qo
  move : MoveSpec (copies (c.held.take refill.length) c.scratch) (c.held.take refill.length) c.scratch (c.counter+1)
  firstBound : c.counter+1 ≤ first.bound
  refillBound : c.counter+1 ≤ firstRefill.bound
  laterBound : c.counter+1 ≤ later.bound
  firstBodyBound : c.counter+1 ≤ firstBody.bound
  laterBodyBound : c.counter+1 ≤ laterBody.bound
  heldAbove : ∀ n ∈ c.held, c.counter < n

/-- The actual allocator constructs the contracts needed for every compact
loop. No assumption about a particular source example is used. -/
def prepareCounted_parts (start stride : Int) (count : Nat) (initial refill : List Load)
    (body : HybridIR.Cmd) (input qi qo : Nat) (b : Build) (inputs : 2 ≤ b.wires.size) :
    CountedParts (prepareCounted start stride count initial refill body input qi qo b).1
      start stride initial refill body input qi qo := by
  let k := b.wires.size
  let i := Expr.bin .add (.lit start) (.bin .mul (.wire k) (.lit stride))
  have iscope : Static (k+1) i := .bin .lit (.bin (.wire (by omega)) .lit)
  have a1 := newSlots_shape (max initial.length refill.length) (b.addWire ⟨0,count⟩)
  dsimp only [StateT.run] at a1
  dsimp only [prepareCounted,fresh,bind,pure,StateT.bind,StateT.pure]
  generalize h1 : newSlots (max initial.length refill.length) (b.addWire ⟨0,count⟩) = pair1 at *
  obtain ⟨held,b1⟩ := pair1
  dsimp only at a1
  have addSize : (b.addWire ⟨0,count⟩).wires.size = k+1 := by simp [Build.addWire,k]
  rw [addSize] at a1
  dsimp only
  have a2 := newSlots_shape refill.length b1
  dsimp only [StateT.run] at a2
  generalize h2 : newSlots refill.length b1 = pair2 at *
  obtain ⟨scratch,b2⟩ := pair2
  dsimp only at a2 ⊢
  have heldLength : held.length = max initial.length refill.length := by simp [a1.1]
  have firstLength : initial.length = (held.take initial.length).length := by simp only [List.length_take,heldLength]; omega
  have laterLength : refill.length = (held.take refill.length).length := by simp only [List.length_take,heldLength]; omega
  have scratchLength : refill.length = scratch.length := by simp [a2.1]
  have heldBounds : ∀ n ∈ held, k+1 ≤ n ∧ n < b1.wires.size := by
    intro n hn
    rw [a1.1,List.mem_range'_1] at hn
    simpa [a1.2] using hn
  have scratchBounds : ∀ n ∈ scratch, b1.wires.size ≤ n ∧ n < b2.wires.size := by
    intro n hn
    rw [a2.1,List.mem_range'_1] at hn
    simpa [a2.2] using hn
  have grow1 : k+1 ≤ b1.wires.size := by have := a1.2; omega
  have grow2 : b1.wires.size ≤ b2.wires.size := by have := a2.2; omega
  have heldOrder : held.Pairwise (· < ·) := by rw [a1.1]; exact List.pairwise_lt_range'
  have scratchOrder : scratch.Pairwise (· < ·) := by rw [a2.1]; exact List.pairwise_lt_range'
  have firstBounds : ∀ n ∈ held.take initial.length, k+1 ≤ n ∧ n < b2.wires.size := by
    intro n hn
    have hh := heldBounds n (List.mem_of_mem_take hn)
    exact ⟨hh.1,Nat.lt_of_lt_of_le hh.2 grow2⟩
  have heldScope : ∀ e ∈ held.map Expr.wire, Static b1.wires.size e := by
    intro e he; obtain ⟨n,hn,rfl⟩ := List.mem_map.mp he
    exact .wire (heldBounds n hn).2
  have takeScope : ∀ len e, e ∈ (held.take len).map Expr.wire → Static b1.wires.size e := by
    intro len e he; obtain ⟨n,hn,rfl⟩ := List.mem_map.mp he
    exact .wire (heldBounds n (List.mem_of_mem_take hn)).2
  change CountedParts (
    let (firstLoads,b3) := loads i input qi [] initial (held.take initial.length) b2
    let (firstBody,b4) := command i ((held.take initial.length).map Expr.wire) qo body b3
    let (firstRefill,b5) := loads i input qi ((held.take initial.length).map Expr.wire) refill scratch b4
    let (laterLoads,b6) := loads i input qi ((held.take refill.length).map Expr.wire) refill scratch b5
    let (laterBody,_) := command i ((held.take refill.length).map Expr.wire) qo body b6
    ⟨k,held,scratch,firstLoads,firstBody,firstRefill,laterLoads,laterBody⟩) start stride initial refill body input qi qo
  let ws :=  WindowSpec.ofLoads i input qi [] initial (held.take initial.length) b2 (k+1)
    firstLength heldOrder.take firstBounds (Nat.le_trans grow1 grow2) (by simp) iscope
  have wsBound : ws.bound = k+1 := rfl
  clear_value ws
  have gf := compactLoads_frame i input qi [] initial (held.take initial.length) b2 (k+1)
    (Nat.le_trans grow1 grow2) (fun n hn => (firstBounds n hn).1) firstLength
  dsimp only [StateT.run] at gf
  generalize h3 : loads i input qi [] initial (held.take initial.length) b2 = pair3 at *
  obtain ⟨firstLoads,b3⟩ := pair3
  dsimp only at gf ⊢
  have grow3 : b1.wires.size ≤ b3.wires.size := Nat.le_trans grow2 gf.1
  let bs :=  BodySpec.ofCommand b3 i ((held.take initial.length).map Expr.wire) body qo
    (by dsimp [k] at grow1; omega) (iscope.mono (Nat.le_trans grow1 grow3))
    (fun e he => (takeScope initial.length e he).mono grow3)
  have bsBound : bs.bound = b3.wires.size := rfl
  clear_value bs
  have gb := command_frame body i ((held.take initial.length).map Expr.wire) qo b3
  dsimp only [StateT.run] at gb
  generalize h4 : command i ((held.take initial.length).map Expr.wire) qo body b3 = pair4 at *
  obtain ⟨firstBody,b4⟩ := pair4
  dsimp only at gb ⊢
  have grow4 : b1.wires.size ≤ b4.wires.size := Nat.le_trans grow3 gb.1
  let wr :=  WindowSpec.ofLoads i input qi ((held.take initial.length).map Expr.wire) refill scratch b4 b1.wires.size
    scratchLength scratchOrder (fun n hn => ⟨(scratchBounds n hn).1,Nat.lt_of_lt_of_le (scratchBounds n hn).2 (Nat.le_trans gf.1 gb.1)⟩)
    grow4 (takeScope initial.length) (iscope.mono grow1)
  have wrBound : wr.bound = b1.wires.size := rfl
  clear_value wr
  have gr := compactLoads_frame i input qi ((held.take initial.length).map Expr.wire) refill scratch b4 b1.wires.size
    grow4 (fun n hn => (scratchBounds n hn).1) scratchLength
  dsimp only [StateT.run] at gr
  generalize h5 : loads i input qi ((held.take initial.length).map Expr.wire) refill scratch b4 = pair5 at *
  obtain ⟨firstRefill,b5⟩ := pair5
  dsimp only at gr ⊢
  have grow5 := Nat.le_trans grow4 gr.1
  let wl :=  WindowSpec.ofLoads i input qi ((held.take refill.length).map Expr.wire) refill scratch b5 b1.wires.size
    scratchLength scratchOrder (fun n hn => ⟨(scratchBounds n hn).1,Nat.lt_of_lt_of_le (scratchBounds n hn).2 (Nat.le_trans gf.1 (Nat.le_trans gb.1 gr.1))⟩)
    grow5 (takeScope refill.length) (iscope.mono grow1)
  have wlBound : wl.bound = b1.wires.size := rfl
  clear_value wl
  have gl := compactLoads_frame i input qi ((held.take refill.length).map Expr.wire) refill scratch b5 b1.wires.size
    grow5 (fun n hn => (scratchBounds n hn).1) scratchLength
  dsimp only [StateT.run] at gl
  generalize h6 : loads i input qi ((held.take refill.length).map Expr.wire) refill scratch b5 = pair6 at *
  obtain ⟨laterLoads,b6⟩ := pair6
  dsimp only at gl ⊢
  have grow6 := Nat.le_trans grow5 gl.1
  let bl :=  BodySpec.ofCommand b6 i ((held.take refill.length).map Expr.wire) body qo
    (by dsimp [k] at grow1; omega) (iscope.mono (Nat.le_trans grow1 grow6))
    (fun e he => (takeScope refill.length e he).mono grow6)
  have blBound : bl.bound = b6.wires.size := rfl
  clear_value bl
  generalize h7 : command i ((held.take refill.length).map Expr.wire) qo body b6 = pair7 at *
  obtain ⟨laterBody,b7⟩ := pair7
  have mv :=  MoveSpec.ofCopies (held.take refill.length) scratch (laterLength.symm.trans scratchLength)
    (heldOrder.take.imp (by intro a b h; omega))
    (by intro d hd s hs; have := heldBounds d (List.mem_of_mem_take hd); have := scratchBounds s hs; omega)
    (fun n hn => (heldBounds n (List.mem_of_mem_take hn)).1)
  change CountedParts ⟨k,held,scratch,firstLoads,firstBody,firstRefill,laterLoads,laterBody⟩ start stride initial refill body input qi qo
  refine ⟨inputs,ws,bs,wr,wl,bl,mv,?_,?_,?_,?_,?_,?_⟩
  · change k+1 ≤ ws.bound; rw [wsBound]
    exact Nat.le_refl _
  · change k+1 ≤ wr.bound; rw [wrBound]; exact grow1
  · change k+1 ≤ wl.bound; rw [wlBound]; exact grow1
  · change k+1 ≤ bs.bound; rw [bsBound]; exact Nat.le_trans grow1 grow3
  · change k+1 ≤ bl.bound; rw [blBound]; exact Nat.le_trans grow1 grow6
  · intro n hn; change k < n; have := (heldBounds n hn).1; omega

end IRComparison.Circuit
