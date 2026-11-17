import IRComparison.Circuit.SharedPipeline
import IRComparison.Circuit.CountedBackend

namespace IRComparison.Circuit.Shared

/-- Only numeric intervals may differ. Resource identifiers and allocation
order stay identical, so surrounding code uses the same banks and captures. -/
structure BuildRelated (a b : Build) : Prop where
  size : a.wires.size = b.wires.size
  resources : a.resources = b.resources

theorem BuildRelated.refl (b : Build) : BuildRelated b b := ⟨rfl,rfl⟩
theorem BuildRelated.addWire (h : BuildRelated a b) (x y : Interval) :
    BuildRelated (a.addWire x) (b.addWire y) :=
  ⟨by simpa [Build.addWire] using h.size,h.resources⟩

def BuilderRelated (R : α → β → Prop) (left : Builder α) (right : Builder β) : Prop :=
  ∀ a b, BuildRelated a b → R (left a).1 (right b).1 ∧ BuildRelated (left a).2 (right b).2

namespace BuilderRelated

theorem pure (h : R x y) : BuilderRelated R (pure x) (pure y) := fun _ _ same => ⟨h,same⟩

theorem bind (first : BuilderRelated R left right)
    (rest : ∀ x y, R x y → BuilderRelated S (f x) (g y)) :
    BuilderRelated S (left >>= f) (right >>= g) := by
  intro a b same
  have step := first a b same
  exact rest _ _ step.1 _ _ step.2

theorem equalBind (first : BuilderRelated Eq left right)
    (rest : ∀ x, BuilderRelated S (f x) (g x)) :
    BuilderRelated S (left >>= f) (right >>= g) :=
  bind first (fun x y eq => eq ▸ rest x)

theorem fresh (x y : Interval) : BuilderRelated Eq (Circuit.fresh x) (Circuit.fresh y) := by
  intro a b h
  exact ⟨h.size,h.addWire x y⟩

theorem newSlots (n : Nat) : BuilderRelated Eq (Circuit.newSlots n) (Circuit.newSlots n) := by
  induction n with
  | zero => exact pure rfl
  | succ n ih =>
    apply equalBind (fresh _ _)
    intro k
    exact equalBind ih (fun ks => pure rfl)

theorem queue (n : Nat) : BuilderRelated Eq (Circuit.queue n) (Circuit.queue n) := by
  intro a b h
  have resources := h.resources
  simp only [Build.resources,Prod.mk.injEq] at resources
  exact ⟨resources.2.2.2,⟨h.size,by change (a.memories,a.queues.push (a.nextQueue,n),a.nextArray,a.nextQueue+1) = (b.memories,b.queues.push (b.nextQueue,n),b.nextArray,b.nextQueue+1); rw [resources.1,resources.2.1,resources.2.2.1,resources.2.2.2]⟩⟩

theorem snapshot (input : Nat) (sizes : Nat → Nat) :
    BuilderRelated Eq (Circuit.snapshot input sizes) (Circuit.snapshot input sizes) := by
  intro a b h
  have resources := h.resources
  simp only [Build.resources,Prod.mk.injEq] at resources
  exact ⟨resources.2.2.1,⟨h.size,by change (a.memories.push (a.nextArray,sizes input),a.queues,a.nextArray+1,a.nextQueue) = (b.memories.push (b.nextArray,sizes input),b.queues,b.nextArray+1,b.nextQueue); rw [resources.1,resources.2.1,resources.2.2.1,resources.2.2.2]⟩⟩

end BuilderRelated

theorem command_resources (c : HybridIR.Cmd) (i : Expr) (locals : List Expr) (output : Nat) :
    PreservesResources (command i locals output c) := by
  induction c generalizing i locals with
  | skip | assign | store | send => exact resources_pure _
  | letValue e b ih =>
    apply resources_bind _ _ (fun _ => rfl)
    intro n
    exact resources_bind _ _ (ih i (.wire n::locals)) (fun _ => resources_pure _)
  | seq a b ia ib =>
    exact resources_bind _ _ (ia i locals) (fun _ => resources_bind _ _ (ib i locals) (fun _ => resources_pure _))
  | branch e a b ia ib =>
    exact resources_bind _ _ (ia i locals) (fun _ => resources_bind _ _ (ib i locals) (fun _ => resources_pure _))
  | «repeat» n b ih =>
    exact resources_bind _ _ (resources_fresh _) (fun _ => resources_bind _ _ (ih i locals) (fun _ => resources_pure _))
  | forRange e b ih =>
    apply resources_bind _ _ (fun _ => rfl)
    intro n
    apply resources_bind _ _ (fun _ => rfl)
    intro _
    apply resources_bind _ _ (resources_fresh _)
    intro k
    exact resources_bind _ _ (ih i (.wire k::locals)) (fun _ => resources_pure _)

theorem channel_resources (c : HybridIR.ChannelCmd) (bank : ChannelLower.Buffers) (i : Expr) (ls : List Expr) :
    PreservesResources (channel bank i ls c) := by
  induction c generalizing ls with
  | skip | assign | store | send | hold | receive => exact resources_pure _
  | letValue e c ih =>
    exact resources_bind _ _ (fun _ => rfl) (fun n => resources_bind _ _ (ih (.wire n::ls)) (fun _ => resources_pure _))
  | letBuffer n c ih =>
    exact resources_bind _ _ (resources_fresh _) (fun n => resources_bind _ _ (ih (.wire n::ls)) (fun _ => resources_pure _))
  | seq a b ia ib | branch e a b ia ib =>
    exact resources_bind _ _ (ia ls) (fun _ => resources_bind _ _ (ib ls) (fun _ => resources_pure _))
  | «repeat» n c ih =>
    exact resources_bind _ _ (resources_fresh _) (fun _ => resources_bind _ _ (ih ls) (fun _ => resources_pure _))
  | forRange e c ih =>
    apply resources_bind _ _ (fun _ => rfl)
    intro n
    apply resources_bind _ _ (fun _ => rfl)
    intro range
    apply resources_bind _ _ (resources_fresh range)
    intro k
    exact resources_bind _ _ (ih (.wire k::ls)) (fun _ => resources_pure _)


theorem command_related (c : HybridIR.Cmd) (i : Circuit.Expr) (ls : List Circuit.Expr) (output : Nat) :
    BuilderRelated Schedule.Simulates (Circuit.command i ls output c) (command i ls output c) := by
  intro a b h
  have proof := command_simulates c i ls output a b h.size
  exact ⟨proof.2,proof.1,by rw [Circuit.command_resources c i ls output,command_resources c i ls output]; exact h.resources⟩

theorem channel_related (c : HybridIR.ChannelCmd) (bank : ChannelLower.Buffers) (i : Circuit.Expr) (ls : List Circuit.Expr) :
    BuilderRelated Schedule.Simulates (ChannelLower.lower bank i ls c) (channel bank i ls c) := by
  intro a b h
  have proof := channel_simulates c bank i ls a b h.size
  exact ⟨proof.2,proof.1,by rw [ChannelLower.resources c bank i ls,channel_resources c bank i ls]; exact h.resources⟩

end IRComparison.Circuit.Shared
