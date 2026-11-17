import IRComparison.Frontend.LeanHLSCommand

open IRComparison HybridWord
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-! Add one to each element. Array 0: input; array 1: output. -/
def buffers : FixedMemory.Declarations := #[(0,5),(1,5)]

def program (s : HybridWord.State) : Option HybridWord.State := do
  let mut t := s
  for i in HybridWord.range 0 5 1 do
    let v ← (t.arrays 0)[i.toNat]?
    t ← t.write 1 i (v+1)
  return t

hls_fixed_program program using buffers as generated

-- Sample input for evaluating the Lean function, not a hard-coded circuit input.
def sample : HybridWord.State :=
  ⟨fun _ => 0, fun a => if a = 0 then #[3,6,9,12,15] else if a = 1 then Array.replicate 5 0 else #[]⟩

#guard (program sample).map (fun t => t.arrays 1) == some (#[4,7,10,13,16] : Array Word)

-- Run from hls/: lake env lean --run examples/Increment.lean
-- The generated circuit receives its inputs through configuration ports.
def main : IO Unit := do
  let circuit ← IO.ofExcept (generated.compile [1])
  let _ ← IO.ofExcept circuit.checkExternalPorts
  let out : System.FilePath := "examples/generated"
  IO.FS.createDirAll out
  -- Add line breaks for browsing; preserve the compiler's SystemVerilog tokens.
  let text := String.intercalate " " (circuit.text.splitOn " " |>.map fun token =>
    if token == ";" || token == "begin" || token == "end" || token == "endcase"
    then token ++ "\n" else token)
  IO.FS.writeFile (out / "Increment.sv") (text.trimAsciiEnd.toString ++ "\n")
  IO.println "Wrote examples/generated/Increment.sv"
