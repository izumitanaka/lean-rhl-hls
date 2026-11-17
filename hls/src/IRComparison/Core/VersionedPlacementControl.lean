import IRComparison.Core.Execution
import IRComparison.Core.VersionedPlacement
import IRComparison.Core.VersionedStorageControl
import IRComparison.Hybrid.HybridCommandControl
namespace IRComparison.VersionedPlacementControl
inductive Config where
  | start (code : VersionedPlacement.Code) (s : State) (ls : List Int)
  | inPlace (control : HybridCommandControl.Config)
  | snapshots (control : VersionedStorageControl.Config)
  | stopped (result : Option State)

def step (i x y : Int) : Config → Config
  | .start (.inPlace b) s ls => .inPlace (.running [(b.target,ls)] s [])
  | .start (.snapshots b) s ls => .snapshots (.running b [s] ls [])
  | .inPlace (.stopped r) => .stopped (r.map Prod.fst)
  | .inPlace c@(.running ..) => .inPlace (HybridCommandControl.step i x y c)
  | .snapshots (.stopped r) => .stopped r
  | .snapshots c => .snapshots (VersionedStorageControl.step i x y c)
  | .stopped r => .stopped r
abbrev Reaches (i x y : Int) : Config → Config → Prop :=
  Execution.Reaches (step i x y)

theorem liftInPlace (h : HybridCommandControl.Reaches i x y a b) : Reaches i x y (.inPlace a) (.inPlace b) := by
  apply Execution.Reaches.map h (fun a => Config.inPlace a)
  intro a
  cases a <;> first | exact .next (.refl _) | exact .refl _

theorem liftSnapshots (h : VersionedStorageControl.Reaches i x y a b) : Reaches i x y (.snapshots a) (.snapshots b) := by
  apply Execution.Reaches.map h (fun a => Config.snapshots a)
  intro a
  cases a <;> first | exact .next (.refl _) | exact .refl _

theorem correct (code : VersionedPlacement.Code) (s : State) (ls : List Int) :
    Reaches i x y (.start code s ls) (.stopped (code.eval i x y s ls)) := by
  cases code with
  | inPlace b =>
    apply Execution.Reaches.next
    have h := HybridCommandControl.correct (i:=i) (x:=x) (y:=y) b.target s [] ls []
    have endBody : HybridCommandControl.Reaches i x y (.running [(b.target,ls)] s [])
        (.stopped (b.target.eval i x y s [] ls)) := by
      apply h.trans
      cases b.target.eval i x y s [] ls with
      | none => exact .refl _
      | some p => obtain ⟨t,q⟩ := p; exact .next (.refl _)
    apply (liftInPlace endBody).trans
    apply Execution.Reaches.next
    simpa [step,HybridIR.MemoryCmd.target_correct,Option.map_map,Function.comp_def,VersionedPlacement.Code.eval] using
      (Execution.Reaches.refl (Config.stopped (b.eval i x y s ls)))
  | snapshots b =>
    apply Execution.Reaches.next
    have h := VersionedStorageControl.lower_correct b i x y [s] ls []
    have ended := h.trans (Execution.Reaches.next (.refl _))
    exact (liftSnapshots ended).trans (.next (.refl _))

def run (i x y : Int) : Nat → Config → Config :=
  Execution.run (step i x y)

end IRComparison.VersionedPlacementControl
