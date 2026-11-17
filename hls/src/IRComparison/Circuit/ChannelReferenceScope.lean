import IRComparison.Circuit.ReferenceScope
import IRComparison.Circuit.CaptureRanges
import IRComparison.Hybrid.ChannelReferences

namespace IRComparison.Circuit

namespace ReferenceScope

theorem Control.counterLoop (body : Control b code) (counter : k < b.wires.size)
    (bound : Expression b limit) : Control b (Circuit.counterLoop k limit code) :=
  ⟨⟨counter,trivial⟩,⟨counter,bound⟩,body,⟨counter,counter,trivial⟩⟩

theorem Expression.bufferRead (inside : bank.stop ≤ b.wires.size) :
    Expression b (ChannelLower.Buffers.read bank slot) := by
  unfold ChannelLower.Buffers.read
  split
  · rename_i valid
    simp only [Expression,ChannelLower.Buffers.valid,ChannelLower.Buffers.value]
    dsimp [ChannelLower.Buffers.stop] at inside
    exact ⟨by omega,by omega,trivial⟩
  · trivial

theorem Expression.contextRead {b : Build} (inputs : 2 ≤ b.wires.size)
    (index : Expression b i) (locals : ∀ e ∈ ls, Expression b e)
    {e : HybridIR.ReadCode} (arrays : e.ArraysWithin (Memory b)) :
    Expression b (Circuit.read i (.wire 0) (.wire 1) ls [] e) :=
  Expression.read e arrays index (by change 0 < b.wires.size; omega)
    (by change 1 < b.wires.size; omega) locals (by simp)

end ReferenceScope

namespace ChannelLower
open HybridIR ReferenceScope

/-- All references in the actual body lowerer are declared. Scalar register
IDs are left for the final inventory scan; banks and holding wires are proved
here without running either storage validation or source code. -/
theorem lower_references (c : ChannelCmd)
    (refs : c.References (Memory final) (Queue final))
    (inputs : 2 ≤ final.wires.size) (index : Expression final i)
    (locals : ∀ e ∈ ls, Expression final e)
    (bankInside : bank.stop ≤ final.wires.size) (bankCount : bufferCount c ≤ bank.count)
    (kept : WireAllocation.Extends (lower bank i ls c b).2 final) :
    Control final (lower bank i ls c b).1 := by
  induction c generalizing b ls with
  | skip => trivial
  | assign => exact Expression.contextRead inputs index locals refs
  | store => exact ⟨refs.1,Expression.contextRead inputs index locals refs.2.1,Expression.contextRead inputs index locals refs.2.2⟩
  | send => exact ⟨refs.1,Expression.contextRead inputs index locals refs.2⟩
  | hold slot e =>
    have slotValid : slot < bank.count := by change slot+1 ≤ bank.count at bankCount; omega
    have valueValid : bank.value slot < final.wires.size := by dsimp [Buffers.stop,Buffers.value] at *; omega
    have flagValid : bank.valid slot < final.wires.size := by dsimp [Buffers.stop,Buffers.valid] at *; omega
    exact ⟨⟨valueValid,Expression.contextRead inputs index locals refs⟩,flagValid,trivial⟩
  | receive q slot =>
    have slotValid : slot < bank.count := by change slot+1 ≤ bank.count at bankCount; omega
    have valueValid : bank.value slot < final.wires.size := by dsimp [Buffers.stop,Buffers.value] at *; omega
    have flagValid : bank.valid slot < final.wires.size := by dsimp [Buffers.stop,Buffers.valid] at *; omega
    exact ⟨⟨refs,valueValid⟩,flagValid,trivial⟩
  | letBuffer slot body ih =>
    let b1 := b.addWire wordRange
    have grown := WireAllocation.channelLower body bank i (.wire b.wires.size::ls) b1
    have newValid : b.wires.size < final.wires.size := by
      simpa using WireAllocation.fresh_valid (grown.trans kept)
    refine ⟨⟨newValid,Expression.bufferRead bankInside⟩,?_⟩
    apply ih refs ?_ (Nat.le_trans (Nat.le_max_right _ _) bankCount) kept
    intro e member
    rcases List.mem_cons.mp member with rfl | member
    · exact newValid
    · exact locals e member
  | letValue e body ih =>
    let expr := Circuit.read i (.wire 0) (.wire 1) ls [] e
    let b1 := b.addWire (b.exprRange expr)
    have grown := WireAllocation.channelLower body bank i (.wire b.wires.size::ls) b1
    have newValid : b.wires.size < final.wires.size := by
      simpa using WireAllocation.fresh_valid (grown.trans kept)
    refine ⟨⟨newValid,Expression.contextRead inputs index locals refs.1⟩,?_⟩
    apply ih refs.2 ?_ bankCount kept
    intro e member
    rcases List.mem_cons.mp member with rfl | member
    · exact newValid
    · exact locals e member
  | seq a c ia ic | branch e a c ia ic =>
    let middle := (lower bank i ls a b).2
    have restGrowth := WireAllocation.channelLower c bank i ls middle
    have leftCount : bufferCount a ≤ bank.count := Nat.le_trans (Nat.le_max_left _ _) bankCount
    have rightCount : bufferCount c ≤ bank.count := Nat.le_trans (Nat.le_max_right _ _) bankCount
    first
    | exact ⟨ia refs.1 locals leftCount (restGrowth.trans kept),ic refs.2 locals rightCount kept⟩
    | exact ⟨Expression.contextRead inputs index locals refs.1,ia refs.2.1 locals leftCount (restGrowth.trans kept),ic refs.2.2 locals rightCount kept⟩
  | «repeat» n body ih =>
    let b1 := b.addWire ⟨0,n⟩
    have grown := WireAllocation.channelLower body bank i ls b1
    have valid : b.wires.size < final.wires.size := by simpa using WireAllocation.fresh_valid (grown.trans kept)
    exact Control.counterLoop (ih refs locals bankCount kept) valid trivial
  | forRange e body ih =>
    let expr := Expr.natIndex (Circuit.read i (.wire 0) (.wire 1) ls [] e)
    let b1 := b.addWire (b.exprRange expr)
    let b2 := b1.addWire (b1.exprRange expr)
    have grown := WireAllocation.channelLower body bank i (.wire b1.wires.size::ls) b2
    have kValid : b1.wires.size < final.wires.size := by simpa using WireAllocation.fresh_valid (grown.trans kept)
    have nValid : b.wires.size < final.wires.size := by simp [b1,Build.addWire] at kValid; omega
    refine ⟨⟨nValid,Expression.contextRead inputs index locals refs.1⟩,?_⟩
    apply Control.counterLoop (limit:=.wire b.wires.size) (ih refs.2 ?_ bankCount kept) kValid nValid
    intro e member
    rcases List.mem_cons.mp member with rfl | member
    · exact kValid
    · exact locals e member

end ChannelLower
end IRComparison.Circuit

namespace IRComparison.Circuit.ChannelCounted
open HybridIR ReferenceScope
variable {body : Cmd} {c : ChannelCmd} {memory queue : Nat → Prop}

private theorem capture_references (slots : List Nat) (h : c.References memory queue) :
    (ChannelBuffers.capture slots c).References memory queue := by
  induction slots generalizing c with
  | nil => exact h
  | cons slot slots ih => exact ih (c:=.letBuffer slot c) h

private theorem loads_references (ls : List ChannelWindow.Load) (inputDeclared : memory input)
    (queueDeclared : queue qi) :
    (ChannelWindow.loads input qi base width padding index ls).References memory queue := by
  induction ls generalizing base with
  | nil => trivial
  | cons l ls ih =>
    refine ⟨?_,ih⟩
    cases l with
    | memory => exact inputDeclared
    | saved => trivial
    | take => exact ⟨trivial,queueDeclared⟩

private theorem piece_references (bodyClosed : body.ArraysWithin memory)
    (inputDeclared : memory input) (receiveDeclared : queue qi) (sendDeclared : queue qo) :
    (piece input qi qo width ls body).References memory queue := by
  exact ⟨capture_references _ (loads_references _ inputDeclared receiveDeclared),
    capture_references _ (ChannelCommandBridge.command_references bodyClosed sendDeclared)⟩

theorem command_references (bodyClosed : body.ArraysWithin memory)
    (inputDeclared : memory input) (receiveDeclared : queue qi) (sendDeclared : queue qo) :
    (command input qi qo start stride count initial refill body).References memory queue := by
  refine ⟨trivial,trivial,trivial,?_,?_⟩
  · exact ⟨trivial,piece_references bodyClosed inputDeclared receiveDeclared sendDeclared,
      piece_references bodyClosed inputDeclared receiveDeclared sendDeclared⟩
  · exact piece_references bodyClosed inputDeclared receiveDeclared sendDeclared

/-- Bank reservation and the complete named-communication command retain
reference closure, regardless of loop counts or data values. -/
theorem lower_references
    (bodyClosed : body.ArraysWithin (Memory final))
    (inputDeclared : Memory final input) (receiveDeclared : Queue final qi) (sendDeclared : Queue final qo)
    (inputs : 2 ≤ final.wires.size)
    (kept : WireAllocation.Extends (lower start stride count initial refill body input qi qo b).2 final) :
    Control final (lower start stride count initial refill body input qi qo b).1 := by
  let c := command input qi qo start stride count initial refill body
  have grown := WireAllocation.channelLower c (ChannelLower.bankFor c b) (.lit 0) [] (ChannelLower.reserve c b)
  apply ChannelLower.lower_references (bank:=ChannelLower.bankFor c b) (i:=.lit 0) (ls:=[])
    (b:=ChannelLower.reserve c b) c
    (command_references bodyClosed inputDeclared receiveDeclared sendDeclared) inputs trivial (by simp)
  · simpa only [← ChannelLower.reserve_size] using (grown.trans kept).size
  · exact Nat.le_refl _
  · exact kept

end IRComparison.Circuit.ChannelCounted
