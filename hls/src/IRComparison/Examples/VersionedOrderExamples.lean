import IRComparison.Frontend.LeanVersionedCommand
import IRComparison.Examples.WindowWorkloads
import IRComparison.Examples.SnapshotEntryExamples
import IRComparison.Examples.OldReadEntryExamples

namespace IRComparison.VersionedOrderExamples
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
hls_versioned WindowWorkloads.filter as filter
hls_versioned WindowWorkloads.filterAlt as filterAlt
hls_versioned WindowWorkloads.filterSkip as filterSkip
hls_versioned WindowWorkloads.filterDilated as dilated
hls_versioned WindowWorkloads.filterDilatedAlt as dilatedAlt
hls_versioned WindowWorkloads.filterDilatedRev as dilatedRev
hls_versioned OldReadEntryExamples.previous as previous
hls_versioned SnapshotEntryExamples.threeVersions as threeVersions
hls_versioned SnapshotEntryExamples.returnOld as returnOld
hls_versioned SnapshotEntryExamples.selectedVersion as selected

-- This observes a different array in the older state, hence not an actual
-- need for an old version of the array being read. Conservative retention is
-- measured rather than silently assuming an alias/liveness theorem.
def unchangedOld (i _x _y : Int) (s : State) : Option State := do
  let next ← s.write 1 i 0
  let x ← (s.arrays 0)[i.toNat]?
  let y ← (s.arrays 0)[(i+1).toNat]?
  next.write 1 i (x+y)
hls_versioned unchangedOld as oldOther

example : (VersionedAllocation.lower previous.versionedBody).isNone = true := by decide +kernel
example : ((VersionedPlacement.compile previous.versionedBody).code.eval 0 99 0 OldReadEntryExamples.initial []).map
    (fun s => (s.arrays 0,s.arrays 1)) = some (#[99,8],#[7]) := by decide +kernel
example : ((VersionedPlacement.compile threeVersions.versionedBody).code.eval 0 3 0 SnapshotEntryExamples.initial []).map
    (fun s => s.arrays 1) = some #[234] := by decide +kernel

end IRComparison.VersionedOrderExamples
