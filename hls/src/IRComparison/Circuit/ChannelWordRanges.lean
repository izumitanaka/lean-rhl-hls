import IRComparison.Circuit.CommandWordRanges
import IRComparison.Hybrid.ChannelWordTyping

namespace IRComparison.Circuit.ChannelLower
open HybridIR CommandWordRanges

/-- The actual named-communication lowering preserves word data. The lexical
context also allows integer indices/counters introduced by the compiler. -/
theorem lower_dataWords (typed : WordChannel types c)
    (ctx : CommandWordRanges.Context b slots types)
    (kept : WireAllocation.Extends (lower bank i (slots.map Expr.wire) c b).2 final) :
    DataWords final (lower bank i (slots.map Expr.wire) c b).1 := by
  induction typed generalizing b slots with
  | skip => trivial
  | assign he | store he | send he => exact (ctx.extend kept).read he
  | hold | receive => exact ⟨trivial,trivial⟩
  | @letBuffer types body slot typed ih =>
    have newCtx := (ctx.extend (addWire_prefix b wordRange)).push
      (slot:=b.wires.size) (kind:=True) (by simp [Build.addWire])
      (fun _ => fresh_word (by decide : isWord wordRange = true))
    exact ⟨trivial,ih newCtx kept⟩
  | @letWord types e body he hb ih =>
    let expr := read i (.wire 0) (.wire 1) (slots.map Expr.wire) [] e
    have newCtx := (ctx.extend (addWire_prefix b (b.exprRange expr))).push
      (slot:=b.wires.size) (kind:=True) (by simp [Build.addWire])
      (fun _ => fresh_word (ctx.read he))
    exact ⟨trivial,ih newCtx kept⟩
  | @letInteger types body e typed ih =>
    let expr := read i (.wire 0) (.wire 1) (slots.map Expr.wire) [] e
    have newCtx := (ctx.extend (addWire_prefix b (b.exprRange expr))).push
      (slot:=b.wires.size) (kind:=False) (by simp [Build.addWire])
      (fun impossible => False.elim impossible)
    exact ⟨trivial,ih newCtx kept⟩
  | @seq types a c first second ha hb =>
    let middle := (lower bank i (slots.map Expr.wire) a b).2
    have firstGrowth := WireAllocation.channelLower a bank i (slots.map Expr.wire) b
    have secondGrowth := WireAllocation.channelLower c bank i (slots.map Expr.wire) middle
    exact ⟨ha ctx (secondGrowth.trans kept),hb (ctx.extend firstGrowth) kept⟩
  | @branch types a c e first second ha hb =>
    let middle := (lower bank i (slots.map Expr.wire) a b).2
    have firstGrowth := WireAllocation.channelLower a bank i (slots.map Expr.wire) b
    have secondGrowth := WireAllocation.channelLower c bank i (slots.map Expr.wire) middle
    exact ⟨ha ctx (secondGrowth.trans kept),hb (ctx.extend firstGrowth) kept⟩
  | @«repeat» types body n typed ih =>
    exact ⟨trivial,ih (ctx.extend (addWire_prefix b ⟨0,n⟩)) kept,trivial⟩
  | @forWord types e body he typed ih =>
    let expr := Expr.natIndex (read i (.wire 0) (.wire 1) (slots.map Expr.wire) [] e)
    let b1 := b.addWire (b.exprRange expr)
    let b2 := b1.addWire (b1.exprRange expr)
    have captured : CommandWordRanges.Context b1 slots types := ctx.extend (addWire_prefix b _)
    have newCtx : CommandWordRanges.Context b2 (b1.wires.size::slots) (pushWord True types) := by
      apply (captured.extend (addWire_prefix b1 _)).push (by simp [b2,Build.addWire])
      intro _
      exact fresh_word (WordRanges.natIndex (captured.read he))
    exact ⟨trivial,trivial,ih newCtx kept,trivial⟩
  | @forInteger types body e typed ih =>
    let expr := Expr.natIndex (read i (.wire 0) (.wire 1) (slots.map Expr.wire) [] e)
    let b1 := b.addWire (b.exprRange expr)
    let b2 := b1.addWire (b1.exprRange expr)
    have captured : CommandWordRanges.Context b1 slots types := ctx.extend (addWire_prefix b _)
    have newCtx : CommandWordRanges.Context b2 (b1.wires.size::slots) (pushWord False types) := by
      apply (captured.extend (addWire_prefix b1 _)).push (by simp [b2,Build.addWire])
      exact fun impossible => False.elim impossible
    exact ⟨trivial,trivial,ih newCtx kept,trivial⟩

end IRComparison.Circuit.ChannelLower

namespace IRComparison.Circuit.ChannelCounted
open HybridIR

private theorem padded_types (width : Nat) :
    ChannelScope.wordBindings width 2 (fun _ => True) = prependWords width (fun n => 2 ≤ n) := by
  funext n
  simp only [ChannelScope.wordBindings,prependWords]
  split
  · rfl
  · apply propext
    omega

private theorem loads_word (ls : List ChannelWindow.Load) :
    WordChannel (prependWords width (fun n => 2 ≤ n))
      (ChannelWindow.loads input qi base width 2 index ls) := by
  induction ls generalizing base with
  | nil => exact .skip
  | cons l ls ih =>
    refine .seq ?_ ih
    cases l with
    | memory a => exact .hold (.memory input _)
    | saved n =>
      apply WordChannel.hold
      apply WordRead.pure
      apply WordValue.local
      by_cases hn : n < width <;> simp [prependWords,hn,show ¬ width+2 < width from by omega]
    | take d => exact .forInteger .receive

theorem piece_word (typed : WordCommand (fun _ => True) body) :
    WordChannel (fun n => 2 ≤ n) (piece input qi qo width ls body) := by
  apply WordChannel.seq
  · apply WordChannel.capture
    simpa using (loads_word (ls.map load) (width:=width) (input:=input) (qi:=qi) (base:=0) (index:=.local width))
  · apply WordChannel.capture
    simpa only [List.length_map,List.length_range,padded_types] using
      (ChannelCommandBridge.command_word (width:=ls.length) (padding:=2) (output:=qo) typed)

theorem command_word (typed : WordCommand (fun _ => True) body) :
    WordChannel (fun _ => True) (command input qi qo start stride count initial refill body) := by
  apply WordChannel.forInteger
  apply WordChannel.letInteger
  have types : (fun n => 2 ≤ n) = pushWord False (pushWord False (fun _ => True)) := by
    funext n
    cases n with
    | zero => simp [pushWord]
    | succ n => cases n <;> simp [pushWord]
  apply WordChannel.branch
  · apply WordChannel.branch
    · simpa only [types] using (piece_word (width:=refill.length) (ls:=refill) typed)
    · simpa only [types] using (piece_word (width:=initial.length) (ls:=refill) typed)
  · simpa only [types] using (piece_word (width:=0) (ls:=initial) typed)

theorem lower_dataWords (typed : WordCommand (fun _ => True) body)
    (ctx : CommandWordRanges.Context b [] (fun _ => True))
    (kept : WireAllocation.Extends (lower start stride count initial refill body input qi qo b).2 final) :
    CommandWordRanges.DataWords final (lower start stride count initial refill body input qi qo b).1 := by
  let c := command input qi qo start stride count initial refill body
  have reserved := ctx.extend (WireAllocation.reserve c b)
  have typec : WordChannel (fun _ => True) c := command_word typed
  exact ChannelLower.lower_dataWords (bank:=ChannelLower.bankFor c b) (i:=.lit 0)
    (slots:=[]) (b:=ChannelLower.reserve c b) (c:=c) (final:=final) typec reserved kept

end IRComparison.Circuit.ChannelCounted
