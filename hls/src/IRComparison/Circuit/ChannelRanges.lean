import IRComparison.Circuit.GeneratedRanges
import IRComparison.Circuit.ChannelWordRanges

namespace IRComparison.Circuit.ChannelLower
open HybridIR CommandWordRanges

/-- The bank uses word cells and one-bit validity flags. This is the existing
allocation's layout, not an extra source-language restriction. -/
structure BankRanges (bank : Buffers) (b : Build) : Prop where
  fits : bank.stop ≤ b.wires.size
  values : ∀ slot, slot < bank.count → Frame.get b.wires.toList (bank.value slot) = wordRange
  flags : ∀ slot, slot < bank.count → Frame.get b.wires.toList (bank.valid slot) = ⟨0,1⟩

theorem BankRanges.extend (h : BankRanges bank before) (kept : WireAllocation.Extends before after) :
    BankRanges bank after := by
  have held (n : Nat) (valid : n < before.wires.size) :
      Frame.get after.wires.toList n = Frame.get before.wires.toList n := by
    simp only [Frame.get,Array.getElem?_toList,← kept.get valid]
  refine ⟨Nat.le_trans h.fits kept.size,?_,?_⟩
  · intro slot valid
    rw [held _ (by have := h.fits; dsimp [Buffers.value,Buffers.stop] at *; omega),h.values slot valid]
  · intro slot valid
    rw [held _ (by have := h.fits; dsimp [Buffers.valid,Buffers.stop] at *; omega),h.flags slot valid]

theorem BankRanges.value_valid (h : BankRanges bank b) (valid : slot < bank.count) :
    bank.value slot < b.wires.toList.length := by
  have := h.fits
  simp only [Array.length_toList]
  dsimp [Buffers.value,Buffers.stop] at *
  omega

theorem BankRanges.flag_valid (h : BankRanges bank b) (valid : slot < bank.count) :
    bank.valid slot < b.wires.toList.length := by
  have := h.fits
  simp only [Array.length_toList]
  dsimp [Buffers.valid,Buffers.stop] at *
  omega

theorem BankRanges.read_word (h : BankRanges bank b) :
    WordRanges.Word (Frame.get b.wires.toList) (bank.read slot) := by
  unfold Buffers.read
  split
  · rename_i valid
    apply WordRanges.select
    · change isWord (Frame.get b.wires.toList (bank.value slot)) = true
      rw [h.values slot valid]; rfl
    · rfl
  · rfl

theorem BankRanges.flag_safe (h : BankRanges bank b) (valid : slot < bank.count) :
    RangeSafe b.wires.toList (.step (.wire (bank.valid slot) (.lit 1))) := by
  apply RangeSafe.wire (h.flag_valid valid)
  rw [h.flags slot valid]
  change (0:Int) ≤ 1 ∧ (1:Int) ≤ 1
  omega

theorem reserve_ranges (c : ChannelCmd) (b : Build) : BankRanges (bankFor c b) (reserve c b) := by
  refine ⟨by simp [reserve_size],?_,?_⟩
  · intro slot valid
    have index : b.wires.size ≤ (bankFor c b).value slot := by dsimp [bankFor,Buffers.value]; omega
    have bound : 2*slot < 2*bufferCount c := by change slot < bufferCount c at valid; omega
    simp [Frame.get,reserve,bankFor,Buffers.value,Array.getElem?_append,index,bound]
  · intro slot valid
    have index : b.wires.size ≤ (bankFor c b).valid slot := by dsimp [bankFor,Buffers.valid]; omega
    have bound : 2*slot+1 < 2*bufferCount c := by change slot < bufferCount c at valid; omega
    simp [Frame.get,reserve,bankFor,Buffers.valid,Array.getElem?_append,index,bound,Nat.add_assoc]

/-- Every typed named-communication body satisfies the actual interval
interpreter's structural rules, including buffers and unbounded loop ordinals. -/
theorem lower_ranges (typed : WordChannel types c)
    (ctx : CommandWordRanges.Context b slots types) (hi : RangeScoped b.wires.size i)
    (bankRanges : BankRanges bank b) (bankSize : bufferCount c ≤ bank.count)
    (kept : WireAllocation.Extends (lower bank i (slots.map Expr.wire) c b).2 final) :
    RangeSafe final.wires.toList (lower bank i (slots.map Expr.wire) c b).1 := by
  induction typed generalizing b slots with
  | skip => exact RangeSafe.skip
  | assign he | store he | send he =>
    exact RangeSafe.data ((ctx.extend kept).frameRead (hi.mono kept.size) he)
  | @hold types e slot he =>
    have valid : slot < bank.count := by change slot+1 ≤ bank.count at bankSize; omega
    have bankFinal := bankRanges.extend kept
    apply RangeSafe.seq ?_ (bankFinal.flag_safe valid)
    apply RangeSafe.wire (bankFinal.value_valid valid)
    rw [bankFinal.values slot valid]
    exact WordRanges.bounds ((ctx.extend kept).frameRead (hi.mono kept.size) he)
  | @receive types q slot =>
    have valid : slot < bank.count := by change slot+1 ≤ bank.count at bankSize; omega
    have bankFinal := bankRanges.extend kept
    apply RangeSafe.seq ?_ (bankFinal.flag_safe valid)
    apply RangeSafe.receive (bankFinal.value_valid valid)
    rw [bankFinal.values slot valid]
    exact ⟨Int.le_refl _,Int.le_refl _⟩
  | @letBuffer types body slot typed ih =>
    let b1 := b.addWire wordRange
    have firstGrowth := addWire_prefix b wordRange
    have bodyGrowth := WireAllocation.channelLower body bank i (.wire b.wires.size::slots.map Expr.wire) b1
    have firstKept := bodyGrowth.trans kept
    have newCtx := (ctx.extend firstGrowth).push (slot:=b.wires.size) (kind:=True)
      (by simp [Build.addWire]) (fun _ => fresh_word (by decide : isWord wordRange = true))
    apply RangeSafe.seq
    · apply RangeSafe.wire (WireAllocation.fresh_valid firstKept)
      rw [WireAllocation.fresh_bound firstKept]
      exact WordRanges.bounds ((bankRanges.extend (firstGrowth.trans firstKept)).read_word (slot:=slot))
    · exact ih newCtx (hi.mono firstGrowth.size) (bankRanges.extend firstGrowth)
        (Nat.le_trans (Nat.le_max_right _ _) bankSize) kept
  | @letWord types e body he hb ih =>
    let expr := read i (.wire 0) (.wire 1) (slots.map Expr.wire) [] e
    let b1 := b.addWire (b.exprRange expr)
    have firstGrowth := addWire_prefix b (b.exprRange expr)
    have bodyGrowth := WireAllocation.channelLower body bank i (.wire b.wires.size::slots.map Expr.wire) b1
    have newCtx := (ctx.extend firstGrowth).push (slot:=b.wires.size) (kind:=True)
      (by simp [Build.addWire]) (fun _ => fresh_word (ctx.read he))
    exact RangeSafe.seq (RangeSafe.capture (RangeScoped.context_read ctx hi e) (bodyGrowth.trans kept))
      (ih newCtx (hi.mono firstGrowth.size) (bankRanges.extend firstGrowth) bankSize kept)
  | @letInteger types body e typed ih =>
    let expr := read i (.wire 0) (.wire 1) (slots.map Expr.wire) [] e
    let b1 := b.addWire (b.exprRange expr)
    have firstGrowth := addWire_prefix b (b.exprRange expr)
    have bodyGrowth := WireAllocation.channelLower body bank i (.wire b.wires.size::slots.map Expr.wire) b1
    have newCtx := (ctx.extend firstGrowth).push (slot:=b.wires.size) (kind:=False)
      (by simp [Build.addWire]) (fun impossible => False.elim impossible)
    exact RangeSafe.seq (RangeSafe.capture (RangeScoped.context_read ctx hi e) (bodyGrowth.trans kept))
      (ih newCtx (hi.mono firstGrowth.size) (bankRanges.extend firstGrowth) bankSize kept)
  | @seq types a c first second ha hb =>
    let middle := (lower bank i (slots.map Expr.wire) a b).2
    have firstGrowth := WireAllocation.channelLower a bank i (slots.map Expr.wire) b
    have secondGrowth := WireAllocation.channelLower c bank i (slots.map Expr.wire) middle
    exact RangeSafe.seq
      (ha ctx hi bankRanges (Nat.le_trans (Nat.le_max_left _ _) bankSize) (secondGrowth.trans kept))
      (hb (ctx.extend firstGrowth) (hi.mono firstGrowth.size) (bankRanges.extend firstGrowth)
        (Nat.le_trans (Nat.le_max_right _ _) bankSize) kept)
  | @branch types a c e first second ha hb =>
    let middle := (lower bank i (slots.map Expr.wire) a b).2
    have firstGrowth := WireAllocation.channelLower a bank i (slots.map Expr.wire) b
    have secondGrowth := WireAllocation.channelLower c bank i (slots.map Expr.wire) middle
    exact RangeSafe.branch
      (ha ctx hi bankRanges (Nat.le_trans (Nat.le_max_left _ _) bankSize) (secondGrowth.trans kept))
      (hb (ctx.extend firstGrowth) (hi.mono firstGrowth.size) (bankRanges.extend firstGrowth)
        (Nat.le_trans (Nat.le_max_right _ _) bankSize) kept)
  | @«repeat» types body n typed ih =>
    let b1 := b.addWire ⟨0,n⟩
    have firstGrowth := addWire_prefix b ⟨0,n⟩
    have bodyGrowth := WireAllocation.channelLower body bank i (slots.map Expr.wire) b1
    have child := ih (ctx.extend firstGrowth) (hi.mono firstGrowth.size) (bankRanges.extend firstGrowth) bankSize kept
    apply RangeSafe.repeat n (bodyGrowth.trans kept) child
    · simpa only [b1,Build.addWire,Array.size_push] using
        (lower_frame body bank b1 i (slots.map Expr.wire) bankSize).2
    · exact bankRanges.fits
  | @forWord types e body he typed ih =>
    let expr := Expr.natIndex (read i (.wire 0) (.wire 1) (slots.map Expr.wire) [] e)
    let b1 := b.addWire (b.exprRange expr)
    let b2 := b1.addWire (b1.exprRange expr)
    have one := addWire_prefix b (b.exprRange expr)
    have two := addWire_prefix b1 (b1.exprRange expr)
    have both := one.trans two
    have newCtx : CommandWordRanges.Context b2 (b1.wires.size::slots) (pushWord True types) := by
      apply (ctx.extend both).push (by simp [b2,Build.addWire])
      intro _
      exact fresh_word (WordRanges.natIndex ((ctx.extend one).read he))
    have child := ih newCtx (hi.mono both.size) (bankRanges.extend both) bankSize kept
    have grown := WireAllocation.channelLower body bank i ((b1.wires.size::slots).map Expr.wire) b2
    have framed : frame bank (b.wires.size+2) (lower bank i ((b1.wires.size::slots).map Expr.wire) body b2).1 := by
      simpa only [b2,b1,Build.addWire,Array.size_push,Nat.add_assoc] using
        (lower_frame body bank b2 i ((b1.wires.size::slots).map Expr.wire) bankSize).2
    have safe := RangeSafe.capturedLoop ((RangeScoped.context_read ctx hi e).natIndex) (grown.trans kept) child framed bankRanges.fits
    change RangeSafe _ (.seq (.step (.wire b.wires.size expr))
      (counterLoop b1.wires.size (.wire b.wires.size) (lower bank i ((b1.wires.size::slots).map Expr.wire) body b2).1))
    simpa only [b1,Build.addWire,Array.size_push] using safe
  | @forInteger types body e typed ih =>
    let expr := Expr.natIndex (read i (.wire 0) (.wire 1) (slots.map Expr.wire) [] e)
    let b1 := b.addWire (b.exprRange expr)
    let b2 := b1.addWire (b1.exprRange expr)
    have one := addWire_prefix b (b.exprRange expr)
    have two := addWire_prefix b1 (b1.exprRange expr)
    have both := one.trans two
    have newCtx : CommandWordRanges.Context b2 (b1.wires.size::slots) (pushWord False types) := by
      apply (ctx.extend both).push (by simp [b2,Build.addWire])
      exact fun impossible => False.elim impossible
    have child := ih newCtx (hi.mono both.size) (bankRanges.extend both) bankSize kept
    have grown := WireAllocation.channelLower body bank i ((b1.wires.size::slots).map Expr.wire) b2
    have framed : frame bank (b.wires.size+2) (lower bank i ((b1.wires.size::slots).map Expr.wire) body b2).1 := by
      simpa only [b2,b1,Build.addWire,Array.size_push,Nat.add_assoc] using
        (lower_frame body bank b2 i ((b1.wires.size::slots).map Expr.wire) bankSize).2
    have safe := RangeSafe.capturedLoop ((RangeScoped.context_read ctx hi e).natIndex) (grown.trans kept) child framed bankRanges.fits
    change RangeSafe _ (.seq (.step (.wire b.wires.size expr))
      (counterLoop b1.wires.size (.wire b.wires.size) (lower bank i ((b1.wires.size::slots).map Expr.wire) body b2).1))
    simpa only [b1,Build.addWire,Array.size_push] using safe

end IRComparison.Circuit.ChannelLower

namespace IRComparison.Circuit.ChannelCounted
open HybridIR

/-- The complete named FIFO/buffer lowering satisfies range inference,
including its private bank allocation and all destructive reads. -/
theorem lower_ranges (typed : WordCommand (fun _ => True) body)
    (ctx : CommandWordRanges.Context b [] (fun _ => True))
    (kept : WireAllocation.Extends (lower start stride count initial refill body input qi qo b).2 final) :
    RangeSafe final.wires.toList (lower start stride count initial refill body input qi qo b).1 := by
  let c := command input qi qo start stride count initial refill body
  have reserved := ctx.extend (WireAllocation.reserve c b)
  exact ChannelLower.lower_ranges (bank:=ChannelLower.bankFor c b) (i:=.lit 0)
    (slots:=[]) (b:=ChannelLower.reserve c b) (c:=c) (final:=final)
    (command_word typed) reserved RangeScoped.lit (ChannelLower.reserve_ranges c b) (Nat.le_refl _) kept

end IRComparison.Circuit.ChannelCounted
