import IRComparison.Examples.Wrap32Examples

open IRComparison HybridWord Circuit CertifiedHLS Wrap32Examples
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def sizes (a : Nat) : Nat := if a < 2 then 4 else 0
def layout : Array (Nat × Nat) := #[(0,4),(1,4)]

def main (args : List String) : IO Unit := do
  let out : System.FilePath := args.headD "artifacts/ir-refinement"
  IO.FS.createDirAll out
  let compiled ← IO.ofExcept (arithmeticHLS.compile [1] sizes layout)
  unless compiled.backend.route == "structured" do
    throw (IO.userError "arithmetic did not use the normal shared route")
  let _ ← IO.ofExcept compiled.checkExternalPorts
  IO.FS.writeFile (out / "arithmetic.sv") compiled.text
  for (name,x,expected) in [
      ("zero",0,#[4294967295,4294967295,0,0]),
      ("one",1,#[0,0,4294967295,4294967295]),
      ("high-bit",2147483648,#[2147483647,2147483647,2147483648,2147483648]),
      ("maximum",4294967295,#[4294967294,4294967294,1,1])] do
    let source : HybridWord.State := ⟨fun _ => 0,
      fun a => if a = 0 then #[BitVec.ofNat 32 x,0,0,0] else Array.replicate 4 0⟩
    unless (arithmetic source).map (fun t => t.encode.arrays 1) == some expected do
      throw (IO.userError s!"{name}: source mismatch")
    let initial : RTL.InterfaceState compiled.backend.artifact.storageShape :=
      ⟨FiniteRuntime.pack compiled.backend.artifact.storageShape (compiled.backend.initial source 0 0),true⟩
    let some final := SystemVerilog.runText compiled.text compiled.backend.artifact.storageShape 128 initial
      | throw (IO.userError s!"{name}: generated text did not finish")
    unless final.core.done && !final.core.error && final.core.decode.data.arrays 1 == expected do
      throw (IO.userError s!"{name}: generated RTL mismatch")
    IO.println s!"PASS wrap32 {name}: source → generated SystemVerilog text"
