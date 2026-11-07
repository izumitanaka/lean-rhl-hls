import IRComparison.Core.VersionedOrder
import IRComparison.Core.VersionedMemoryControl
import IRComparison.Core.VersionedFIFOControl
import IRComparison.Hybrid.HybridSymbolicWindowControl
import IRComparison.Hybrid.HybridCompactFIFOControl
namespace IRComparison.VersionedOrderControl
/-- none means fuel exhausted; some none is a completed failing computation. -/
def run (code : VersionedOrder.Code) (input : Input) (x y : Int) (fuel : Nat) (s : State) (q : List Int) :
    Option (Option State) :=
  match code with
  | .lateMemory c => match VersionedMemoryControl.run c input x y fuel (.start s) with
      | .stopped r => some r
      | _ => none
  | .lateFIFO c => match VersionedFIFOControl.run c x y fuel (.start s q) with
      | .stopped r => some (r.map Prod.fst)
      | _ => none
  | .earlyMemory c => match HybridSymbolicWindowControl.run c input x y fuel (.start s) with
      | .stopped r => some r
      | _ => none
  | .earlyFIFO c => match HybridCompactFIFOControl.run c x y fuel (.start s q) with
      | .stopped r => some (r.map Prod.fst)
      | _ => none

theorem finishes (code : VersionedOrder.Code) (s : State) (q : List Int) :
    ∃ n, run code input x y n s q = some (code.eval input x y s q) := by
  cases code with
  | lateMemory c =>
    obtain ⟨n,hn⟩ := (VersionedMemoryControl.correct (input:=input) (x:=x) (y:=y) c s).finite
    exact ⟨n,by simp [run,hn,VersionedOrder.Code.eval]⟩
  | lateFIFO c =>
    obtain ⟨n,hn⟩ := (VersionedFIFOControl.correct (x:=x) (y:=y) c s q).finite
    exact ⟨n,by simp [run,hn,VersionedOrder.Code.eval]⟩
  | earlyMemory c =>
    obtain ⟨n,hn⟩ := (HybridSymbolicWindowControl.correct (input:=input) (x:=x) (y:=y) c s).finite
    exact ⟨n,by simp [run,hn,VersionedOrder.Code.eval]⟩
  | earlyFIFO c =>
    obtain ⟨n,hn⟩ := (HybridCompactFIFOControl.correct (x:=x) (y:=y) c s q).finite
    exact ⟨n,by simp [run,hn,VersionedOrder.Code.eval]⟩

theorem artifact_finishes (p : VersionedOrder.Artifact size array body start stride count supplier)
    (s : State) (sized : (s.arrays array).size = size)
    (hq : CommunicationIR.Corresponds (arrayInput (s.arrays array)) supplier.entries q) :
    ∃ n, run p.code (arrayInput (s.arrays array)) x y n s q =
      some (Source.iterate (fun i => VersionedWindow.run body i x y) stride count start s) := by
  obtain ⟨n,hn⟩ := finishes (input:=arrayInput (s.arrays array)) (x:=x) (y:=y) p.code s q
  exact ⟨n,hn.trans (congrArg some (p.correct s sized x y q hq))⟩
end IRComparison.VersionedOrderControl
