import IRComparison.Circuit.WordRanges
import IRComparison.Circuit.Allocation

namespace IRComparison.Circuit

namespace CommandWordRanges
open HybridIR

def wires (b : Build) (n : Nat) : Interval := b.wires[n]?.getD wordRange

/-- Lexical locals refer to already allocated holding registers. Only locals
marked as source data words must fit BV32; integer ordinals are left unmarked. -/
structure Context (b : Build) (slots : List Nat) (types : WordBindings) : Prop where
  inputs : 2 ≤ b.wires.size
  left : WordRanges.Word (wires b) (.wire 0)
  right : WordRanges.Word (wires b) (.wire 1)
  scopedSlots : ∀ n ∈ slots, n < b.wires.size
  words : ∀ n, types n → WordRanges.Word (wires b) (lookup (slots.map Expr.wire) n)

theorem Context.extend (h : Context before slots types) (growth : WireAllocation.Extends before after) :
    Context after slots types := by
  have held (n : Nat) (valid : n < before.wires.size) : wires before n = wires after n := by
    unfold wires
    rw [growth.get valid]
  refine ⟨Nat.le_trans h.inputs growth.size,?_,?_,?_,?_⟩
  · change isWord (wires after 0) = true
    rw [← held 0 (by have := h.inputs; omega)]
    exact h.left
  · change isWord (wires after 1) = true
    rw [← held 1 (by have := h.inputs; omega)]
    exact h.right
  · intro n member
    exact Nat.lt_of_lt_of_le (h.scopedSlots n member) growth.size
  · intro n word
    have prior := h.words n word
    cases found : slots[n]? with
    | none => simp [lookup,List.getElem?_map,found,WordRanges.Word,range,wrapped?,isWord]
    | some slot =>
      have same := held slot (h.scopedSlots slot (List.mem_of_getElem? found))
      simpa [lookup,List.getElem?_map,found,WordRanges.Word,range,wrapped?,← same] using prior

theorem addWire_prefix (b : Build) (r : Interval) : WireAllocation.Extends b (b.addWire r) :=
  ⟨[⟨min 0 r.lo,max 0 r.hi⟩],by simp [Build.addWire]⟩

theorem Context.push (h : Context b slots types) (valid : slot < b.wires.size)
    (word : kind → WordRanges.Word (wires b) (.wire slot)) :
    Context b (slot::slots) (pushWord kind types) := by
  refine ⟨h.inputs,h.left,h.right,?_,?_⟩
  · intro n member
    rcases List.mem_cons.mp member with rfl | member
    · exact valid
    · exact h.scopedSlots n member
  · intro n typed
    cases n with
    | zero => exact word typed
    | succ n => exact h.words n typed

theorem fresh_word {b : Build} (word : isWord r = true) :
    WordRanges.Word (wires (b.addWire r)) (.wire b.wires.size) := by
  have bounds : 0 ≤ r.lo ∧ r.hi ≤ 4294967295 := by simpa [isWord] using word
  simp only [WordRanges.Word,range,wrapped?,Option.isSome_none,Bool.false_eq_true,↓reduceIte]
  simp [wires,Build.addWire,isWord]
  omega

theorem Context.read (h : Context b slots types) (typed : WordRead types (fun _ => False) e) :
    WordRanges.Word (wires b) (read i (.wire 0) (.wire 1) (slots.map Expr.wire) [] e) :=
  WordRanges.read_word typed h.left h.right h.words (fun _ impossible => False.elim impossible)

def ActionWords (b : Build) : Action → Prop
  | .assign _ e | .store _ _ e | .send _ e => WordRanges.Word (wires b) e
  | _ => True

def DataWords (b : Build) : Schedule → Prop
  | .skip => True
  | .step a => ActionWords b a
  | .seq a c | .branch _ a c => DataWords b a ∧ DataWords b c
  | .loop _ c => DataWords b c

/-- The actual imperative body builder preserves the word-data property for
all typed bodies. Arbitrarily many enclosing integer counter loops are allowed.
The final extension parameter accounts for later allocations in sibling code. -/
theorem command_dataWords (typed : WordCommand types c) (ctx : Context b slots types)
    (kept : WireAllocation.Extends (command i (slots.map Expr.wire) output c b).2 final) :
    DataWords final (command i (slots.map Expr.wire) output c b).1 := by
  induction typed generalizing b slots with
  | skip => trivial
  | assign he | store he | send he => exact (ctx.extend kept).read he
  | @letValue localTypes e body he hb ih =>
    let expr := read i (.wire 0) (.wire 1) (slots.map Expr.wire) [] e
    let b1 := b.addWire (b.exprRange expr)
    have newCtx : Context b1 (b.wires.size::slots) (pushWord True localTypes) := by
      apply (ctx.extend (addWire_prefix b _)).push (by simp [b1,Build.addWire])
      intro _
      exact fresh_word (ctx.read he)
    have child := ih newCtx kept
    exact ⟨trivial,child⟩
  | @seq localTypes a c first second ha hb =>
    have firstGrowth := WireAllocation.command a i (slots.map Expr.wire) output b
    let middle := (command i (slots.map Expr.wire) output a b).2
    have secondGrowth := WireAllocation.command c i (slots.map Expr.wire) output middle
    exact ⟨ha ctx (secondGrowth.trans kept),hb (ctx.extend firstGrowth) kept⟩
  | @branch localTypes a c e first second ha hb =>
    have firstGrowth := WireAllocation.command a i (slots.map Expr.wire) output b
    let middle := (command i (slots.map Expr.wire) output a b).2
    have secondGrowth := WireAllocation.command c i (slots.map Expr.wire) output middle
    exact ⟨ha ctx (secondGrowth.trans kept),hb (ctx.extend firstGrowth) kept⟩
  | @«repeat» localTypes body n typed ih =>
    have child := ih (ctx.extend (addWire_prefix b ⟨0,n⟩)) kept
    exact ⟨trivial,child,trivial⟩
  | @forWord localTypes e body he typed ih =>
    let expr := Expr.natIndex (read i (.wire 0) (.wire 1) (slots.map Expr.wire) [] e)
    let b1 := b.addWire (b.exprRange expr)
    let b2 := b1.addWire (b1.exprRange expr)
    have captured : Context b1 slots localTypes := ctx.extend (addWire_prefix b _)
    have newCtx : Context b2 (b1.wires.size::slots) (pushWord True localTypes) := by
      apply (captured.extend (addWire_prefix b1 _)).push (by simp [b2,Build.addWire])
      intro _
      exact fresh_word (WordRanges.natIndex (captured.read he))
    have child := ih newCtx kept
    exact ⟨trivial,trivial,child,trivial⟩

  | @forInteger localTypes body e typed ih =>
    let expr := Expr.natIndex (read i (.wire 0) (.wire 1) (slots.map Expr.wire) [] e)
    let b1 := b.addWire (b.exprRange expr)
    let b2 := b1.addWire (b1.exprRange expr)
    have captured : Context b1 slots localTypes := ctx.extend (addWire_prefix b _)
    have newCtx : Context b2 (b1.wires.size::slots) (pushWord False localTypes) := by
      apply (captured.extend (addWire_prefix b1 _)).push (by simp [b2,Build.addWire])
      exact fun impossible => False.elim impossible
    have child := ih newCtx kept
    exact ⟨trivial,trivial,child,trivial⟩

/-- In particular, every source command lowered by the actual body builder
satisfies the BV32 conditions on data-register, memory, and FIFO writes. -/
theorem source_dataWords (source : HybridWord.Cmd) (layout : Array (Nat × Nat))
    (i : Expr) (output : Nat) :
    let initial : Build := {memories := layout,nextArray := layoutLimit layout}
    let generated := command i [] output source.lower.target initial
    DataWords generated.2 generated.1 := by
  let initial : Build := {memories := layout,nextArray := layoutLimit layout}
  have ctx : Context initial [] (fun _ => True) := {
    inputs := by change 2 ≤ 2; decide
    left := rfl
    right := rfl
    scopedSlots := by simp
    words := fun _ _ => by simp [lookup,WordRanges.Word,range,wrapped?,isWord] }
  exact command_dataWords source.lower_word ctx (.refl _)

end CommandWordRanges
end IRComparison.Circuit
