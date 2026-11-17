import IRComparison.Examples.VersionedOrderExamples
import IRComparison.Core.VersionedOrderControl
import IRComparison.Examples.VersionedPreservationExamples
open IRComparison IRComparison.VersionedOrderExamples

structure Case where
  name : String
  body : VersionedHybrid.Term
  native : Int → Int → Int → State → Option State
  start : Int := 0
  stride : Int := 1
  count : Nat := 8
  supplier : CompactSequence.Seq := ⟨0,1,64⟩
  x : Int := 9
  y : Int := 0

def copies : VersionedStorage.Code → Nat
  | .yield _ => 0
  | .copy _ b => 1 + copies b
  | .capture _ _ b | .assign _ _ b | .store _ _ _ b => copies b
  | .branch _ _ a b | .bind a b | .call _ a b => copies a + copies b
  | .repeat _ _ a b | .forRange _ _ a b | .forRangeCaptured _ _ a b => copies a + copies b

def slots : VersionedPlacement.Code → Nat
  | .inPlace _ => 0
  | .snapshots c => copies c

def metrics : VersionedOrder.Code → Bool × Nat × Nat × Nat
  | .earlyMemory c => (false,c.initial.length,c.refill.length,0)
  | .earlyFIFO c => (true,c.initial.length,c.refill.length,0)
  | .lateMemory c => (false,c.initial.length,c.refill.length,slots c.body)
  | .lateFIFO c => (true,c.initial.length,c.refill.length,slots c.body)

def observe (s : State) := (s.arrays 0,s.arrays 1,s.arrays 2,s.regs 0,s.regs 1)

def main : IO Unit := do
  IO.FS.createDirAll "artifacts/versioned-order"
  let cases : List Case := [
    {name:= "filter", body:= filter.versionedBody, native:= WindowWorkloads.filter},
    {name:= "filter-reverse", body:= filter.versionedBody, native:= WindowWorkloads.filter, start:= 7, stride:= -1, count:= 8, supplier:= ⟨9,-1,10⟩},
    {name:= "filter-wrong-order", body:= filter.versionedBody, native:= WindowWorkloads.filter, start:= 7, stride:= -1, count:= 8},
    {name:= "filter-stride2", body:= filter.versionedBody, native:= WindowWorkloads.filter, start:= 0, stride:= 2, count:= 8},
    {name:= "filter-skip", body:= filterSkip.versionedBody, native:= WindowWorkloads.filterSkip},
    {name:= "filter-alt", body:= filterAlt.versionedBody, native:= WindowWorkloads.filterAlt, start:= 0, stride:= 1, count:= 8, supplier:= ⟨63,-1,64⟩},
    {name:= "dilated", body:= dilated.versionedBody, native:= WindowWorkloads.filterDilated},
    {name:= "dilated-alt", body:= dilatedAlt.versionedBody, native:= WindowWorkloads.filterDilatedAlt, start:= 0, stride:= 1, count:= 8, supplier:= ⟨63,-1,64⟩},
    {name:= "dilated-reverse", body:= dilatedRev.versionedBody, native:= WindowWorkloads.filterDilatedRev, start:= 7, stride:= -1, count:= 8},
    {name:= "empty", body:= filter.versionedBody, native:= WindowWorkloads.filter, start:= 0, stride:= 1, count:= 0},
    {name:= "clamp-crossing-zero", body:= filter.versionedBody, native:= WindowWorkloads.filter, start:= -1, stride:= 1, count:= 3},
    {name:= "out-of-bounds", body:= filter.versionedBody, native:= WindowWorkloads.filter, start:= 63, stride:= 1, count:= 1},
    {name:= "read-old", body:= previous.versionedBody, native:= OldReadEntryExamples.previous},
    {name:= "three-versions", body:= threeVersions.versionedBody, native:= SnapshotEntryExamples.threeVersions},
    {name:= "return-old", body:= returnOld.versionedBody, native:= SnapshotEntryExamples.returnOld},
    {name:= "selected-old", body:= selected.versionedBody, native:= SnapshotEntryExamples.selectedVersion, start:= 0, stride:= 1, count:= 8, supplier:= ⟨0,1,64⟩, x:= 9, y:= 1},
    {name:= "selected-new", body:= selected.versionedBody, native:= SnapshotEntryExamples.selectedVersion},
    {name:= "unchanged-old-array", body:= oldOther.versionedBody, native:= unchangedOld},
    {name:= "multiple-other-writes", body:= VersionedPreservationExamples.multiple.versionedBody, native:= VersionedPreservationExamples.multipleWrites},
    {name:= "old-read-branch-true", body:= VersionedPreservationExamples.condition.versionedBody, native:= VersionedPreservationExamples.oldCondition, y:= 1},
    {name:= "old-read-branch-false", body:= VersionedPreservationExamples.condition.versionedBody, native:= VersionedPreservationExamples.oldCondition},
    {name:= "joined-writes-true", body:= VersionedPreservationExamples.joined.versionedBody, native:= VersionedPreservationExamples.joinWrites, y:= 1},
    {name:= "joined-writes-false", body:= VersionedPreservationExamples.joined.versionedBody, native:= VersionedPreservationExamples.joinWrites},
    {name:= "joined-input-changed", body:= VersionedPreservationExamples.changedJoin.versionedBody, native:= VersionedPreservationExamples.joinChangesInput, y:= 1},
    {name:= "joined-input-unchanged", body:= VersionedPreservationExamples.changedJoin.versionedBody, native:= VersionedPreservationExamples.joinChangesInput},
    {name:= "unchanged-old-out-of-bounds", body:= oldOther.versionedBody, native:= unchangedOld, start:= 63, count:= 1},
    {name:= "unchanged-old-empty", body:= oldOther.versionedBody, native:= unchangedOld, count:= 0}]
  let mut rows := "case,order,fifo,initial_loads,refill_loads,snapshot_copy_sites\n"
  for c in cases do
    let s := WindowWorkloads.initial
    let input := arrayInput (s.arrays 0)
    let queue := c.supplier.entries.filterMap input
    let expected := Source.iterate (fun i => c.native i c.x c.y) c.stride c.count c.start s
    for (name,compiler) in [("allocate-first",VersionedOrder.early),("optimize-first",VersionedOrder.late)] do
      let p := compiler 64 0 c.body c.start c.stride c.count c.supplier
      let actual := p.code.eval input c.x c.y s queue
      unless actual.map observe == expected.map observe do
        throw (IO.userError s!"{c.name}/{name}: source mismatch")
      let controlled := VersionedOrderControl.run p.code input c.x c.y 100000 s queue
      unless controlled.map (Option.map observe) == some (expected.map observe) do
        throw (IO.userError s!"{c.name}/{name}: control execution mismatch or exhausted fuel")
      let (fifo,initial,refill,copies) := metrics p.code
      rows := rows ++ s!"{c.name},{name},{fifo},{initial},{refill},{copies}\n"
      IO.println s!"{c.name}/{name}: FIFO={fifo}, loads={initial}/{refill}, snapshot sites={copies}; source agrees"
  IO.FS.writeFile "artifacts/versioned-order/results.csv" rows
  for compiler in [VersionedOrder.early,VersionedOrder.late] do
    let preserved := metrics (compiler 64 0 oldOther.versionedBody 0 1 8 ⟨0,1,64⟩).code
    unless preserved == (false,0,0,2) do
      throw (IO.userError "old-state reference unexpectedly simplified")
  let p := VersionedOrder.planLate 64 0 filter.versionedBody 0 1 8 ⟨0,1,64⟩
  IO.FS.writeFile "artifacts/versioned-order/filter-before.txt" (reprStr filter.versionedBody)
  IO.FS.writeFile "artifacts/versioned-order/filter-after-window-before-allocation.txt" (reprStr p.window.code.body)
  IO.FS.writeFile "artifacts/versioned-order/old-version-storage.txt"
    (reprStr (VersionedPlacement.compile threeVersions.versionedBody).code)
  let n := 1000000000
  let large := VersionedOrder.late (n+4) 0 filter.versionedBody 0 1 n ⟨0,1,n+4⟩
  unless metrics large.code == (true,3,3,0) do throw (IO.userError "billion-count late path did not stay compact")
  IO.println s!"{cases.length} cases x 2 orders passed (evaluation and control); old-state references preserved; billion-count late FIFO stays compact"
