import IRComparison.Circuit.AllocationLayout
import IRComparison.Circuit.CommandWordRanges

namespace IRComparison.Circuit

namespace ReferenceScope

def Memory (b : Build) (id : Nat) : Prop := ∃ size, (id,size) ∈ b.memories.toList
def Queue (b : Build) (id : Nat) : Prop := ∃ size, (id,size) ∈ b.queues.toList

def Copy (b : Build) (dst src : Nat) : Prop :=
  ∃ size, (dst,size) ∈ b.memories.toList ∧ (src,size) ∈ b.memories.toList

/-- Source scalar registers are declared by scanning the final nodes. Here we
track the allocated wires and banks, whose declarations are made separately. -/
def Expression (b : Build) : Expr → Prop
  | .fail | .lit _ | .reg _ => True
  | .wire k => k < b.wires.size
  | .memory a j => Memory b a ∧ Expression b j
  | .bin _ a c | .seq a c => Expression b a ∧ Expression b c
  | .wrap32 a => Expression b a
  | .natIndex a => Expression b a
  | .select c a d => Expression b c ∧ Expression b a ∧ Expression b d

def Operation (b : Build) : Action → Prop
  | .wire k e => k < b.wires.size ∧ Expression b e
  | .assign _ e => Expression b e
  | .store a j e => Memory b a ∧ Expression b j ∧ Expression b e
  | .send q e => Queue b q ∧ Expression b e
  | .receive q k => Queue b q ∧ k < b.wires.size
  | .snapshot dst src => Copy b dst src
  | .erase a => Memory b a
  | .clear q => Queue b q

def Control (b : Build) : Schedule → Prop
  | .skip => True
  | .step action => Operation b action
  | .seq a c => Control b a ∧ Control b c
  | .branch e a c => Expression b e ∧ Control b a ∧ Control b c
  | .loop e c => Expression b e ∧ Control b c

structure Extension (before after : Build) : Prop where
  wires : before.wires.size ≤ after.wires.size
  memories : before.memories.toList ⊆ after.memories.toList
  queues : before.queues.toList ⊆ after.queues.toList

theorem Extension.refl (b : Build) : Extension b b := ⟨Nat.le_refl _,fun _ h => h,fun _ h => h⟩
theorem Extension.trans (a : Extension first second) (b : Extension second third) : Extension first third :=
  ⟨Nat.le_trans a.wires b.wires,fun _ h => b.memories (a.memories h),fun _ h => b.queues (a.queues h)⟩
theorem Extension.fresh (b : Build) (r : Interval) : Extension b (b.addWire r) :=
  ⟨by simp [Build.addWire],fun _ h => h,fun _ h => h⟩

private def extensionRules (original : Build) : BuildInvariant.Rules (Extension original) where
  fresh := fun r b h => h.trans (.fresh b r)
  queue := fun n b h => h.trans ⟨Nat.le_refl _,fun _ hm => hm,by
    intro p hp
    change p ∈ (b.queues.push (b.nextQueue,n)).toList
    simpa only [Array.toList_push,List.mem_append,List.mem_singleton] using Or.inl hp⟩
  snapshot := fun a sizes b h => h.trans ⟨Nat.le_refl _,by
    intro p hp
    change p ∈ (b.memories.push (b.nextArray,sizes a)).toList
    simpa only [Array.toList_push,List.mem_append,List.mem_singleton] using Or.inl hp,fun _ hq => hq⟩

private theorem named_preserves (original : Build) (start stride count initial refill body input qi qo) :
    BuildInvariant.Preserves (Extension original)
      (CountedBackend.named.build start stride count initial refill body input qi qo) := by
  intro b h
  apply (extensionRules original).channelLower
  apply h.trans
  exact ⟨by simp [ChannelLower.reserve],fun _ hm => hm,fun _ hq => hq⟩

theorem Extension.named (start stride count initial refill body input qi qo b) :
    Extension b (CountedBackend.named.build start stride count initial refill body input qi qo b).2 :=
  named_preserves b start stride count initial refill body input qi qo b (.refl _)

theorem Extension.symbolicInstruction (sizes channels : Nat → Nat) (c : HybridSymbolicGlobal.Instruction) (b : Build) :
    Extension b (symbolicInstructionWith CountedBackend.named.build sizes channels c b).2 :=
  (extensionRules b).symbolicInstruction CountedBackend.named.build (named_preserves b) sizes channels c b (.refl _)

theorem Extension.symbolicInstructions (sizes channels : Nat → Nat) (cs : List HybridSymbolicGlobal.Instruction) (b : Build) :
    Extension b (symbolicInstructionsWith CountedBackend.named.build sizes channels cs b).2 :=
  (extensionRules b).symbolicInstructions CountedBackend.named.build (named_preserves b) sizes channels cs b (.refl _)

theorem Extension.channels (capacity : Nat → Nat) (ids : List Nat) (b : Build) :
    Extension b (allocateChannels capacity ids b).2 :=
  (extensionRules b).channels capacity ids b (.refl _)

theorem Extension.chooseInput (channels : Nat → Nat) (mode : GlobalPipeline.InputMode) (b : Build) :
    Extension b (chooseInputQueue channels mode b).2 :=
  (extensionRules b).chooseInput channels mode b (.refl _)

theorem Extension.chooseOutput (channels : Nat → Nat) (budget : Nat) (output : Option Nat) (b : Build) :
    Extension b (chooseOutputQueue channels budget output b).2 :=
  (extensionRules b).chooseOutput channels budget output b (.refl _)

theorem Memory.extend {id : Nat} (h : Memory before id) (kept : Extension before after) : Memory after id := by
  obtain ⟨n,h⟩ := h
  exact ⟨n,kept.memories h⟩
theorem Queue.extend {id : Nat} (h : Queue before id) (kept : Extension before after) : Queue after id := by
  obtain ⟨n,h⟩ := h
  exact ⟨n,kept.queues h⟩
theorem Copy.extend (h : Copy before dst src) (kept : Extension before after) : Copy after dst src := by
  obtain ⟨n,hd,hs⟩ := h
  exact ⟨n,kept.memories hd,kept.memories hs⟩

theorem Expression.extend (h : Expression before e) (kept : Extension before after) : Expression after e := by
  induction e <;> simp_all [Expression,Memory.extend]
  case wire => exact Nat.lt_of_lt_of_le h kept.wires
  case memory => exact Memory.extend h.1 kept

theorem Operation.extend (h : Operation before a) (kept : Extension before after) : Operation after a := by
  cases a with
  | wire => exact ⟨Nat.lt_of_lt_of_le h.1 kept.wires,h.2.extend kept⟩
  | assign => exact Expression.extend h kept
  | store => exact ⟨h.1.extend kept,h.2.1.extend kept,h.2.2.extend kept⟩
  | snapshot => exact Copy.extend h kept
  | erase => exact Memory.extend h kept
  | clear => exact Queue.extend h kept
  | send => exact ⟨h.1.extend kept,h.2.extend kept⟩
  | receive => exact ⟨h.1.extend kept,Nat.lt_of_lt_of_le h.2 kept.wires⟩

theorem Control.extend (h : Control before c) (kept : Extension before after) : Control after c := by
  induction c with
  | skip => trivial
  | step => exact Operation.extend h kept
  | seq _ _ a c => exact ⟨a h.1,c h.2⟩
  | branch _ _ _ a c => exact ⟨h.1.extend kept,a h.2.1,c h.2.2⟩
  | loop _ _ ih => exact ⟨h.1.extend kept,ih h.2⟩

theorem Expression.lookup (h : ∀ e ∈ es, Expression b e) : Expression b (Circuit.lookup es k) := by
  cases found : es[k]? with
  | none => simp [Circuit.lookup,found,Expression]
  | some e => simpa [Circuit.lookup,found] using h e (List.mem_of_getElem? found)

theorem Expression.value (v : HybridIR.Value)
    (hi : Expression b i) (hx : Expression b x) (hy : Expression b y)
    (locals : ∀ e ∈ ls, Expression b e) (temps : ∀ e ∈ ts, Expression b e) :
    Expression b (Circuit.value i x y ls ts v) := by
  induction v <;> simp_all [Circuit.value,Expression,Expression.lookup]

theorem Expression.read (e : HybridIR.ReadCode)
    (arrays : e.ArraysWithin (Memory b))
    (hi : Expression b i) (hx : Expression b x) (hy : Expression b y)
    (locals : ∀ e ∈ ls, Expression b e) (temps : ∀ e ∈ ts, Expression b e) :
    Expression b (Circuit.read i x y ls ts e) := by
  induction e generalizing ts with
  | pure v => exact value v hi hx hy locals temps
  | register => trivial
  | memory a j => exact ⟨arrays,value j hi hx hy locals temps⟩
  | bind a c ia ic =>
    have first := ia arrays.1 temps
    refine ⟨first,ic arrays.2 ?_⟩
    intro e member
    rcases List.mem_cons.mp member with rfl | member
    · exact first
    · exact temps e member
  | branch e a c ia ic => exact ⟨value e hi hx hy locals temps,ia arrays.1 temps,ic arrays.2 temps⟩

end ReferenceScope
end IRComparison.Circuit
