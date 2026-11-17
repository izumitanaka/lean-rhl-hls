import IRComparison.Frontend.LeanHLSCommand

open IRComparison HybridWord
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-! Reverse outer traversal with an inner loop and a conditional array copy.
Array 0: branch input; array 1: output; array 2: alternative copy source. -/
def buffers : FixedMemory.Declarations := #[(0,4),(1,4),(2,4)]

def program (s : HybridWord.State) : Option HybridWord.State := do
  let mut t := s
  for i in HybridWord.range 1 (-1) (-1) do
    for j in HybridWord.range 0 2 1 do
      let v ← (t.arrays 0)[i.toNat]?
      if v != 0 then
        t ← t.copy 1 0 4
      else
        t ← t.copy 1 2 4
      t ← t.write 1 j (i+j)
  return t

hls_fixed_program program using buffers as generated

-- Sample input for evaluating the Lean function, not a hard-coded circuit input.
def sample : HybridWord.State :=
  ⟨fun _ => 0, fun a => if a = 0 then #[0,2,3,4] else if a = 1 then Array.replicate 4 0 else if a = 2 then #[9,8,7,6] else #[]⟩

#guard (program sample).map (fun t => t.arrays 1) == some (#[9,1,7,6] : Array Word)

-- Run from hls/: lake env lean --run examples/NestedLoops.lean
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
  IO.FS.writeFile (out / "NestedLoops.sv") (text.trimAsciiEnd.toString ++ "\n")
  IO.println "Wrote examples/generated/NestedLoops.sv"
