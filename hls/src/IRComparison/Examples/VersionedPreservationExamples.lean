import IRComparison.Examples.VersionedOrderExamples

namespace IRComparison.VersionedPreservationExamples
open VersionedHybrid HybridIR

def multipleWrites (i _x _y : Int) (s : State) : Option State := do
  let middle ← s.write 1 i 0
  let latest ← middle.write 2 i 1
  let a ← (s.arrays 0)[i.toNat]?
  let b ← (middle.arrays 0)[(i+1).toNat]?
  latest.write 1 i (a+b)
hls_versioned multipleWrites as multiple

def oldCondition (i x flag : Int) (s : State) : Option State := do
  let latest ← s.write 1 i x
  if flag != 0 then do
    let a ← (s.arrays 0)[i.toNat]?
    let b ← (s.arrays 0)[(i+1).toNat]?
    latest.write 1 i (a+b)
  else do
    let a ← (s.arrays 0)[i.toNat]?
    let b ← (s.arrays 0)[(i+1).toNat]?
    latest.write 1 i (a-b)
hls_versioned oldCondition as condition

def joinWrites (i _x flag : Int) (s : State) : Option State := do
  let latest ← if flag != 0 then s.write 1 i 1 else s.write 2 i 2
  let a ← (s.arrays 0)[i.toNat]?
  let b ← (s.arrays 0)[(i+1).toNat]?
  latest.write 1 i (a+b)
hls_versioned joinWrites as joined

def joinChangesInput (i x flag : Int) (s : State) : Option State := do
  let latest ← if flag != 0 then s.write 0 i x else s.write 1 i 0
  let a ← (s.arrays 0)[i.toNat]?
  let b ← (s.arrays 0)[(i+1).toNat]?
  latest.write 1 i (a+b)
hls_versioned joinChangesInput as changedJoin

end IRComparison.VersionedPreservationExamples
