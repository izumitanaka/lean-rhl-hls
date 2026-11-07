import IRComparison.Core.VersionedStorage
import IRComparison.Core.VersionedAllocation

namespace IRComparison.VersionedPlacement
/-- Logical storage assignment, not BRAM/port/timing binding. Snapshot slots
    preserve all old versions when single-current-state lowering is unavailable. -/
inductive Code where
  | inPlace (body : HybridIR.MemoryCmd)
  | snapshots (body : VersionedStorage.Code)
  deriving Repr

def Code.eval (code : Code) (i x y : Int) (s : State) (ls : List Int := []) : Option State :=
  match code with
  | .inPlace b => b.eval i x y s ls
  | .snapshots b => b.eval i x y [s] ls

structure Compiled (source : VersionedHybrid.Term) where
  code : Code
  correct : ∀ i x y s ls, code.eval i x y s ls = source.eval i x y [s] ls

def compile (source : VersionedHybrid.Term) : Compiled source :=
  match h : VersionedAllocation.lower source with
  | some body => ⟨.inPlace body,fun i x y s ls => VersionedAllocation.lower_correct source body h i x y s [] ls⟩
  | none => ⟨.snapshots (VersionedStorage.lower source),fun i x y s ls => VersionedStorage.lower_correct source i x y [s] ls⟩
end IRComparison.VersionedPlacement
