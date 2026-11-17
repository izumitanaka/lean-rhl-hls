import IRComparison.Examples.WholeProgramExamples

open IRComparison HybridWord Circuit Circuit.Pipelining CertifiedHLS WholeProgramExamples
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def sizes (a : Nat) : Nat := if a < 3 then 8 else 0
def layout : Array (Nat × Nat) := #[(0,8),(1,8),(2,8)]
def nominal : Array Word := #[3,6,9,12,15,18,21,24]

def verify {native : Program} (name : String) (entry : ProgramEntry native)
    (output : Nat) (values : Array Word) (expected : Option (Array Int)) : IO Unit := do
  let c ← IO.ofExcept (ProgramEntry.compile entry [output] sizes layout)
  let s : HybridWord.State := ⟨fun _ => 0,
    fun a => if a = 0 then values else if a < 3 then Array.replicate 8 0 else #[]⟩
  unless (native s).map (fun t => t.encode.arrays output) == expected do
    throw (IO.userError s!"{name}: independent source expectation")
  let r : RTL.InterfaceState c.backend.artifact.storageShape :=
    ⟨FiniteRuntime.pack c.backend.artifact.storageShape (c.backend.initial s 0 0),true⟩
  let some final := SystemVerilog.runText c.text c.backend.artifact.storageShape 512 r
    | throw (IO.userError s!"{name}: parsed RTL did not finish")
  unless final.core.done && !final.busy do throw (IO.userError s!"{name}: termination")
  match expected with
  | none => unless final.core.error do throw (IO.userError s!"{name}: missing error")
  | some expected =>
    unless !final.core.error && final.core.decode.data.arrays output == expected do
      throw (IO.userError s!"{name}: RTL observation")
  IO.FS.writeFile s!"artifacts/whole-program/{name}.sv" c.text
  IO.println s!"PASS {name}: original complete Lean function → {c.backend.route} → parsed RTL"

def main : IO Unit := do
  IO.FS.createDirAll "artifacts/whole-program"
  verify "filter" filterHLS.entry 2 nominal (some #[5,8,11,14,17,20,23,0])
  verify "nested" nestedHLS.entry 1 #[0,5,8,0,0,0,0,0] (some #[0,0,6,7,9,10,0,0])
  verify "ascending" ascendingHLS.entry 1 nominal (some #[4,0,10,0,16,0,22,0])
  verify "descending" descendingHLS.entry 1 nominal (some #[4,0,10,0,16,0,22,0])
  verify "empty" emptyHLS.entry 1 nominal (some #[0,0,0,0,0,0,0,0])
  verify "wrapping" wrappingHLS.entry 1 nominal (some #[4,7,0,0,0,0,0,0])
  verify "failing" failingHLS.entry 1 nominal none
  let big ← IO.ofExcept (largeHLS.compile [0] sizes layout)
  let little ← IO.ofExcept (smallHLS.compile [0] sizes layout)
  unless big.backend.artifact.machine.nodes.size == little.backend.artifact.machine.nodes.size &&
      big.backend.artifact.wires.size == little.backend.artifact.wires.size do
    throw (IO.userError "static range was expanded while compiling")
  unless HybridWord.rangeCount 0 4294967297 1 == 4294967297 do
    throw (IO.userError "iteration count was truncated to BV32")
  IO.FS.writeFile "artifacts/whole-program/large-shape.sv" big.text
  IO.println s!"PASS large-shape: 2^32+1 iterations, {big.backend.artifact.machine.nodes.size} nodes; same shape as 8; not executed"
