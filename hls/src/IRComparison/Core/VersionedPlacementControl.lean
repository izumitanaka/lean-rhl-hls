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
inductive Reaches (i x y : Int) : Config → Config → Prop where
  | refl (a) : Reaches i x y a a
  | next : Reaches i x y (step i x y a) b → Reaches i x y a b

theorem Reaches.trans (h : Reaches i x y a b) (g : Reaches i x y b c) : Reaches i x y a c := by
  induction h with
  | refl => exact g
  | next _ ih => exact .next (ih g)

theorem liftInPlace (h : HybridCommandControl.Reaches i x y a b) : Reaches i x y (.inPlace a) (.inPlace b) := by
  induction h with
  | refl => exact .refl _
  | @next a b h ih => cases a with
    | running => exact .next ih
    | stopped => simpa [HybridCommandControl.step] using ih

theorem liftSnapshots (h : VersionedStorageControl.Reaches i x y a b) : Reaches i x y (.snapshots a) (.snapshots b) := by
  induction h with
  | refl => exact .refl _
  | @next a b h ih => cases a with
    | running | iterating | returning => exact .next ih
    | stopped => simpa [VersionedStorageControl.step] using ih

theorem correct (code : VersionedPlacement.Code) (s : State) (ls : List Int) :
    Reaches i x y (.start code s ls) (.stopped (code.eval i x y s ls)) := by
  cases code with
  | inPlace b =>
    apply Reaches.next
    have h := HybridCommandControl.correct (i:=i) (x:=x) (y:=y) b.target s [] ls []
    have endBody : HybridCommandControl.Reaches i x y (.running [(b.target,ls)] s [])
        (.stopped (b.target.eval i x y s [] ls)) := by
      apply h.trans
      cases b.target.eval i x y s [] ls with
      | none => exact .refl _
      | some p => obtain ⟨t,q⟩ := p; exact .next (.refl _)
    apply (liftInPlace endBody).trans
    apply Reaches.next
    simpa [step,HybridIR.MemoryCmd.target_correct,Option.map_map,Function.comp_def,VersionedPlacement.Code.eval] using
      (Reaches.refl (.stopped (b.eval i x y s ls)))
  | snapshots b =>
    apply Reaches.next
    have h := VersionedStorageControl.lower_correct b i x y [s] ls []
    have ended := h.trans (VersionedStorageControl.Reaches.next (.refl _))
    exact (liftSnapshots ended).trans (.next (.refl _))

def run (i x y : Int) : Nat → Config → Config
  | 0,c => c
  | n+1,c => run i x y n (step i x y c)
theorem Reaches.finite (h : Reaches i x y a b) : ∃ n, run i x y n a = b := by
  induction h with
  | refl => exact ⟨0,rfl⟩
  | next _ ih => obtain ⟨n,hn⟩ := ih; exact ⟨n+1,hn⟩
end IRComparison.VersionedPlacementControl
