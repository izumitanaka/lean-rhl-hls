import IRComparison.Frontend.LeanSnapshotCommand
import IRComparison.Core.VersionedOrder

namespace IRComparison
open Lean Elab Command
/-- Both orders share the version-preserving frontend output. The imperative
    declaration also produced by hls_snapshots is not used by either entry here. -/
elab "hls_versioned " source:ident " as " target:ident : command => do
  elabCommand (← `(hls_snapshots $source as $target))
  let f := mkIdent (.str target.getId "functional")
  let fp := mkIdent (.str target.getId "functional_correct")
  let b := mkIdent (.str target.getId "versionedBody")
  let bp := mkIdent (.str target.getId "versionedBody_correct")
  elabCommand (← `(def $b : VersionedHybrid.Term := VersionedHybrid.ofFunctional $f))
  elabCommand (← `(theorem $bp (i x y : Int) (s : State) :
      ($b).eval i x y [s] [] = $source i x y s := by
    exact (VersionedHybrid.ofFunctional_correct $f).trans ($fp i x y s)))
  for (label,compiler) in [("early",``VersionedOrder.early),("late",``VersionedOrder.late)] do
    let out := mkIdent (.str target.getId label)
    let correct := mkIdent (.str target.getId (label ++ "_correct"))
    let c := mkIdent compiler
    elabCommand (← `(def $out (size array : Nat) (start stride : Int) (count : Nat) (supplier : CompactSequence.Seq) :=
      $c size array $b start stride count supplier))
    elabCommand (← `(theorem $correct (size array : Nat) (start stride : Int) (count : Nat) (supplier : CompactSequence.Seq)
        (s : State) (sized : (s.arrays array).size = size) (x y : Int) (q : List Int)
        (hq : CommunicationIR.Corresponds (arrayInput (s.arrays array)) supplier.entries q) :
        ($out size array start stride count supplier).code.eval (arrayInput (s.arrays array)) x y s q =
          Source.iterate (fun i => $source i x y) stride count start s := by
      rw [VersionedOrder.Artifact.correct _ s sized x y q hq]
      exact Source.iterate_congr _ _ (fun i t => $bp i x y t) stride count start s))
end IRComparison
