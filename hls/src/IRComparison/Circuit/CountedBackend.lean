import IRComparison.Circuit.ChannelCountedLower
import IRComparison.Circuit.InstructionContract

namespace IRComparison.Circuit

/-- The outer per-array composition depends only on this proved contract.
Both implementations preserve the same window and communication policy. -/
structure CountedBackend where
  build : CountedBuilder
  resources : ∀ start stride count initial refill body input qi qo,
    PreservesResources (build start stride count initial refill body input qi qo)
  grows : ∀ start stride count initial refill body input qi qo b,
    b.wires.size ≤ (build start stride count initial refill body input qi qo b).2.wires.size
  frame : ∀ start stride count initial refill body input qi qo b, 2 ≤ b.wires.size →
    (build start stride count initial refill body input qi qo b).1.above b.wires.size
  correct : ∀ start stride count initial refill body input qi qo b cap bound,
    2 ≤ b.wires.size → qi ≠ qo → input ∉ commandWrites body →
    sendBound body = some bound → count*bound ≤ cap qo →
    BlocksContract cap (build start stride count initial refill body input qi qo b).1 input qi qo
      (referenceBlocks start stride count initial refill body)

def CountedBackend.legacy : CountedBackend where
  build := counted
  resources := counted_resources
  grows := counted_grows
  frame := counted_frame
  correct := by
    intro start stride count initial refill body input qi qo b cap bound inputs distinct readonly known capacity
    exact ⟨Schedule.above_mono _ (counted_frame _ _ _ _ _ _ _ _ _ _ inputs) inputs,
      fun p x y hx hy empty => counted_full_reference _ _ _ _ _ _ _ _ _ _ p inputs distinct empty readonly hx hy known capacity⟩

theorem CountedBackend.extension (backend : CountedBackend) (start stride count initial refill body input qi qo) :
    ExtendsBuild (backend.build start stride count initial refill body input qi qo) := by
  intro b
  have hr := backend.resources start stride count initial refill body input qi qo b
  have hq := congrArg (fun r => r.2.1) hr
  have hn := congrArg (fun r => r.2.2.2) hr
  dsimp only [Build.resources] at hq hn
  exact ⟨backend.grows _ _ _ _ _ _ _ _ _ _,fun p hp => by rw [hq]; exact hp,by rw [hn]; exact Nat.le_refl _⟩

namespace ChannelLower

theorem resources (c : HybridIR.ChannelCmd) (bank : Buffers) (i : Expr) (ls : List Expr) :
    PreservesResources (lower bank i ls c) := by
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

theorem frame_above (h : frame bank bound code) (le : bank.base ≤ bound) : code.above bank.base := by
  induction code with
  | skip => trivial
  | step a =>
    cases a <;> try trivial
    case wire slot e =>
      by_cases low : bank.base ≤ slot
      · exact low
      · exact False.elim (h slot ⟨by omega,Or.inl (by omega)⟩ rfl)
    case receive q slot =>
      by_cases low : bank.base ≤ slot
      · exact low
      · exact False.elim (h slot ⟨by omega,Or.inl (by omega)⟩ rfl)
  | seq _ _ ia ib | branch _ _ _ ia ib => exact ⟨ia h.1,ib h.2⟩
  | loop _ _ ih => exact ih h

end ChannelLower

def CountedBackend.named : CountedBackend where
  build := ChannelCounted.lower
  resources := by
    intro start stride count initial refill body input qi qo b
    exact ChannelLower.resources _ _ _ _ _
  grows := by
    intro start stride count initial refill body input qi qo b
    let c := ChannelCounted.command input qi qo start stride count initial refill body
    have h := ChannelLower.lower_frame c (ChannelLower.bankFor c b) (ChannelLower.reserve c b) (.lit 0) [] (Nat.le_refl _)
    have reserve : b.wires.size ≤ (ChannelLower.reserve c b).wires.size := by
      simp [ChannelLower.reserve]
    exact Nat.le_trans reserve h.1
  frame := by
    intro start stride count initial refill body input qi qo b inputs
    let c := ChannelCounted.command input qi qo start stride count initial refill body
    have h := ChannelLower.lower_frame c (ChannelLower.bankFor c b) (ChannelLower.reserve c b) (.lit 0) [] (Nat.le_refl _)
    exact ChannelLower.frame_above h.2 (by simp [ChannelLower.bankFor,ChannelLower.reserve])
  correct := by
    intro start stride count initial refill body input qi qo b cap bound inputs distinct readonly known capacity
    let c := ChannelCounted.command input qi qo start stride count initial refill body
    have h := ChannelLower.lower_frame c (ChannelLower.bankFor c b) (ChannelLower.reserve c b) (.lit 0) [] (Nat.le_refl _)
    have framed := ChannelLower.frame_above h.2 (by simp [ChannelLower.bankFor,ChannelLower.reserve])
    exact ⟨Schedule.above_mono _ framed inputs,
      fun p x y hx hy empty => ChannelCounted.lower_reference b p inputs distinct empty readonly hx hy known capacity⟩

end IRComparison.Circuit
