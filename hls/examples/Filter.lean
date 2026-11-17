import IRComparison.Frontend.LeanHLSCommand

open IRComparison HybridWord
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-! Produce B = A + 1, then average three adjacent values of B.
Array 0: input A; array 1: intermediate B; array 2: output.
The last two output elements retain their initial value. -/
def buffers : FixedMemory.Declarations := #[(0,5),(1,5),(2,5)]

def program (s : HybridWord.State) : Option HybridWord.State := do
  let mut t := s
  for i in HybridWord.range 0 5 1 do
    let v ← (t.arrays 0)[i.toNat]?
    t ← t.write 1 i (v+1)
  for i in HybridWord.range 0 3 1 do
    let a ← (t.arrays 1)[i.toNat]?
    let b ← (t.arrays 1)[(i+1).toNat]?
    let c ← (t.arrays 1)[(i+2).toNat]?
    t ← t.write 2 i ((a+b+c)/3)
  return t

hls_fixed_program program using buffers as generated

-- Sample input for evaluating the Lean function, not a hard-coded circuit input.
def sample : HybridWord.State :=
  ⟨fun _ => 0, fun a => if a = 0 then #[3,6,9,12,15] else if a < 3 then Array.replicate 5 0 else #[]⟩

#guard (program sample).map (fun t => t.arrays 2) == some (#[7,10,13,0,0] : Array Word)

-- Run from hls/: lake env lean --run examples/Filter.lean
-- The generated circuit receives its inputs through configuration ports.
def main : IO Unit := do
  let circuit ← IO.ofExcept (generated.compile [2])
  let _ ← IO.ofExcept circuit.checkExternalPorts
  let out : System.FilePath := "examples/generated"
  IO.FS.createDirAll out
  -- Add line breaks for browsing; preserve the compiler's SystemVerilog tokens.
  let text := String.intercalate " " (circuit.text.splitOn " " |>.map fun token =>
    if token == ";" || token == "begin" || token == "end" || token == "endcase"
    then token ++ "\n" else token)
  IO.FS.writeFile (out / "Filter.sv") (text.trimAsciiEnd.toString ++ "\n")
  IO.println "Wrote examples/generated/Filter.sv"
