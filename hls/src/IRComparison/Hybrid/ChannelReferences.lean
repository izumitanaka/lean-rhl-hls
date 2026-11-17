import IRComparison.Hybrid.References
import IRComparison.Hybrid.ChannelCommandBridge
import IRComparison.Hybrid.ChannelWindowLoads

namespace IRComparison.HybridIR

/-- Static names used by the existing communication language. This excludes
local buffer cells, whose fixed bank is allocated separately. -/
def ChannelCmd.References (memory queue : Nat → Prop) : ChannelCmd → Prop
  | .skip => True
  | .assign _ e | .hold _ e => e.ArraysWithin memory
  | .store a j e => memory a ∧ j.ArraysWithin memory ∧ e.ArraysWithin memory
  | .send q e => queue q ∧ e.ArraysWithin memory
  | .receive q _ => queue q
  | .letBuffer _ c | .repeat _ c => References memory queue c
  | .letValue e c | .forRange e c => e.ArraysWithin memory ∧ References memory queue c
  | .seq a b => References memory queue a ∧ References memory queue b
  | .branch e a b => e.ArraysWithin memory ∧ References memory queue a ∧ References memory queue b

end IRComparison.HybridIR

namespace IRComparison.ChannelScope
open HybridIR

theorem read_arrays (e : ReadCode) (h : e.ArraysWithin allowed) :
    (read width padding e).ArraysWithin allowed := by
  induction e <;> simp_all [read,ReadCode.ArraysWithin]

end IRComparison.ChannelScope

namespace IRComparison.ChannelCommandBridge
open HybridIR

theorem command_references {c : Cmd} {memory queue : Nat → Prop} (h : c.ArraysWithin memory) (send : queue output) :
    (command output width padding c).References memory queue := by
  induction c generalizing width with
  | skip => trivial
  | assign => exact ChannelScope.read_arrays _ h
  | store => exact ⟨h.1,ChannelScope.read_arrays _ h.2.1,ChannelScope.read_arrays _ h.2.2⟩
  | send => exact ⟨send,ChannelScope.read_arrays _ h⟩
  | letValue _ _ ih | forRange _ _ ih => exact ⟨ChannelScope.read_arrays _ h.1,ih h.2⟩
  | seq _ _ a b => exact ⟨a h.1,b h.2⟩
  | branch _ _ _ a b => exact ⟨ChannelScope.read_arrays _ h.1,a h.2.1,b h.2.2⟩
  | «repeat» _ _ ih => exact ih h

end IRComparison.ChannelCommandBridge
