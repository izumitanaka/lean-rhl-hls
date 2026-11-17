import IRComparison.Frontend.LeanHLSCommand

open IRComparison HybridWord
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-! Swap arrays 0 and 1 using predeclared temporary array 2.
All three regions have the same fixed length; no allocation occurs in the program. -/
def buffers : FixedMemory.Declarations := #[(0,4),(1,4),(2,4)]

def program (s : HybridWord.State) : Option HybridWord.State := do
  let t ← s.copy 2 0 4
  let t ← t.copy 0 1 4
  t.copy 1 2 4

hls_fixed_program program using buffers as generated

-- Sample input for evaluating the Lean function, not a hard-coded circuit input.
def sample : HybridWord.State :=
  ⟨fun _ => 0, fun a => if a = 0 then #[10,20,30,40] else if a = 1 then #[5,6,7,8] else if a = 2 then Array.replicate 4 0 else #[]⟩

#guard (program sample).map (fun t => t.arrays 0) == some (#[5,6,7,8] : Array Word)

#guard (program sample).map (fun t => t.arrays 1) == some (#[10,20,30,40] : Array Word)

-- Run from hls/: lake env lean --run examples/Swap.lean
-- The generated circuit receives its inputs through configuration ports.
def main : IO Unit := do
  let circuit ← IO.ofExcept (generated.compile [0,1])
  let _ ← IO.ofExcept circuit.checkExternalPorts
  let out : System.FilePath := "examples/generated"
  IO.FS.createDirAll out
  -- Add line breaks for browsing; preserve the compiler's SystemVerilog tokens.
  let text := String.intercalate " " (circuit.text.splitOn " " |>.map fun token =>
    if token == ";" || token == "begin" || token == "end" || token == "endcase"
    then token ++ "\n" else token)
  IO.FS.writeFile (out / "Swap.sv") (text.trimAsciiEnd.toString ++ "\n")
  IO.println "Wrote examples/generated/Swap.sv"
