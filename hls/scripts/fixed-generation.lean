import IRComparison.Examples.FixedMemoryExamples

open IRComparison HybridWord Circuit FixedMemoryExamples
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def verify {native : CertifiedHLS.Program} (name : String) (entry : FixedHLS.Entry native)
    (outputs : List Nat) (s : HybridWord.State) : IO Unit := do
  let c ← IO.ofExcept (entry.compile outputs)
  let some expected := native s | throw (IO.userError s!"{name}: source failed")
  let r : RTL.InterfaceState c.backend.artifact.storageShape :=
    ⟨FiniteRuntime.pack c.backend.artifact.storageShape (c.backend.initial s 0 0),true⟩
  let some result := SystemVerilog.runText c.text c.backend.artifact.storageShape 256 r
    | throw (IO.userError s!"{name}: RTL interpretation failed")
  unless result.core.done && !result.busy && !result.core.error do
    throw (IO.userError s!"{name}: RTL termination/error")
  for a in outputs do
    unless result.core.decode.data.arrays a == expected.encode.arrays a do
      throw (IO.userError s!"{name}: array {a}")
  for r in [0,1] do
    unless result.core.decode.data.regs r == expected.encode.regs r do
      throw (IO.userError s!"{name}: scalar output {r}")
  IO.FS.writeFile s!"artifacts/fixed-generation/{name}.sv" c.text
  IO.println s!"PASS {name}: source → {c.backend.route} → parsed RTL"

def main : IO Unit := do
  IO.FS.createDirAll "artifacts/fixed-generation"
  match sparseHLS.native.compile [7,11] (FixedMemory.sizes sparseBuffers) sparseBuffers with
  | .error why =>
    unless why == "source arrays missing from original layout: [0]" do
      throw (IO.userError s!"unexpected legacy failure: {why}")
    IO.println s!"REPRODUCED legacy adapter: {why}"
  | .ok _ => throw (IO.userError "legacy counterexample no longer reproduces")
  verify "sparse" sparseHLS.entry [7,11]
    ⟨fun _ => 0,fun a => if a = 7 then #[10,20,30,40] else if a = 11 then #[0,0,0,0] else #[]⟩
  verify "scalar" scalarHLS.entry [] ⟨fun _ => 0,fun _ => #[]⟩
  verify "empty" emptyHLS.entry [7] ⟨fun _ => 0,fun _ => #[]⟩
  verify "captured" capturedHLS.entry [] ⟨fun r => if r = 0 then 17 else 0,fun _ => #[]⟩
  verify "captured-loop" capturedLoopHLS.entry [] ⟨fun r => if r = 0 then 17 else 0,fun _ => #[]⟩
  verify "captured-overflow" capturedHLS.entry [] ⟨fun r => if r = 0 then 4294967295 else 0,fun _ => #[]⟩
  verify "captured-loop-overflow" capturedLoopHLS.entry [] ⟨fun r => if r = 0 then 4294967295 else 0,fun _ => #[]⟩
  let next : Lean.Name → Option (List Lean.Name) := fun n =>
    if n == `a then some [`b] else if n == `b then some [`a] else none
  unless DependencyClosure.walk next 2 (List.replicate 10000 `a) [] == some [`b,`a] do
    throw (IO.userError "cyclic dependency graph with repeated edges failed")
  unless DependencyClosure.walk next 3 [`missing] [] == none do
    throw (IO.userError "missing dependency was accepted")
  IO.println "PASS dependencies: cycle, 10000 repeated edges, missing definition rejected"
