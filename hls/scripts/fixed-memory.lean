import IRComparison.Examples.FixedMemoryExamples

open IRComparison HybridWord Circuit FixedMemoryExamples
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def initial (first : Array Word := #[10,20,30,40]) : HybridWord.State :=
  ⟨fun _ => 0, fun a => if a = 0 then first else if a = 1 then #[5,6,7,8]
    else if a = 2 then #[101,102,103,104] else #[]⟩

def verify {native : CertifiedHLS.Program} (name : String) (entry : FixedHLS.Entry native)
    (s : HybridWord.State) (expected : Array (Array Int)) : IO Unit := do
  let c ← IO.ofExcept (entry.compile [0,1,2])
  let some result := native s | throw (IO.userError s!"{name}: source failed")
  for a in [0,1,2] do
    unless result.encode.arrays a == expected[a]! do
      throw (IO.userError s!"{name}: source expectation for array {a}")
  let r : RTL.InterfaceState c.backend.artifact.storageShape :=
    ⟨FiniteRuntime.pack c.backend.artifact.storageShape (c.backend.initial s 0 0),true⟩
  let some final := SystemVerilog.runText c.text c.backend.artifact.storageShape 768 r
    | throw (IO.userError s!"{name}: RTL interpretation failed")
  unless final.core.done && !final.busy && !final.core.error do
    throw (IO.userError s!"{name}: RTL did not succeed")
  for a in [0,1,2] do
    unless final.core.decode.data.arrays a == expected[a]! do
      throw (IO.userError s!"{name}: RTL array {a}")
  IO.FS.writeFile s!"artifacts/fixed-memory/{name}.sv" c.text
  IO.println s!"PASS {name}: complete native function → {c.backend.route} → RTL; all three arrays"

def main : IO Unit := do
  IO.FS.createDirAll "artifacts/fixed-memory"
  verify "independent" independentHLS.entry (initial)
    #[#[99,20,30,40],#[10,77,30,40],#[10,77,30,40]]
  verify "repeated" repeatedHLS.entry (initial)
    #[#[11,21,31,40],#[11,21,30,40],#[101,102,103,104]]
  verify "swap" swapHLS.entry (initial)
    #[#[5,6,7,8],#[10,20,30,40],#[10,20,30,40]]
  verify "nested-mixed" nestedHLS.entry (initial #[0,20,30,40])
    #[#[0,20,30,40],#[101,1,103,104],#[101,102,103,104]]
  verify "nested-true" nestedHLS.entry (initial)
    #[#[10,20,30,40],#[10,1,30,40],#[101,102,103,104]]
  verify "self" selfHLS.entry (initial)
    #[#[10,20,30,40],#[5,6,7,8],#[101,102,103,104]]
  let short ← IO.ofExcept (shortHLS.compile [0,1,2])
  let long ← IO.ofExcept (longHLS.compile [0,1,2])
  unless short.backend.artifact.memories == long.backend.artifact.memories &&
      short.backend.artifact.machine.nodes.size == long.backend.artifact.machine.nodes.size &&
      short.backend.artifact.wires.size == long.backend.artifact.wires.size do
    throw (IO.userError "copy loop allocated storage or expanded with iteration count")
  IO.FS.writeFile "artifacts/fixed-memory/long-shape.sv" long.text
  IO.println s!"PASS bounded storage: 3 and 1000 iterations share memory regions, {long.backend.artifact.machine.nodes.size} nodes, and wire count; generation only"
  match independentHLS.compile [3] with
  | .error _ => IO.println "PASS undeclared output rejected"
  | .ok _ => throw (IO.userError "undeclared output accepted")
