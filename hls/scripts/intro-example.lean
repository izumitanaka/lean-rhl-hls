import IRComparison.Frontend.LeanHLSCommand

open IRComparison HybridWord Circuit CertifiedHLS
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

-- A complete ordinary Lean program: the loop is part of the input.
def buffers : FixedMemory.Declarations := #[(0,5),(1,5)]
def increment (s : HybridWord.State) : Option HybridWord.State := do
  let mut t := s
  for i in HybridWord.range 0 5 1 do
    let v ← (t.arrays 0)[i.toNat]?
    t ← t.write 1 i (v+1)
  return t
hls_fixed_program increment using buffers as incrementHLS

-- The optimization entry: bodies plus explicit stage boundaries and iteration ranges.
def producer (i _x _y : Word) (s : HybridWord.State) : Option HybridWord.State := do
  let v ← (s.arrays 0)[i.toNat]?
  s.write 1 i (v+1)
hls_certified producer as producerHLS

def filter (i _x _y : Word) (s : HybridWord.State) : Option HybridWord.State := do
  let a ← (s.arrays 1)[i.toNat]?
  let b ← (s.arrays 1)[(i+1).toNat]?
  let c ← (s.arrays 1)[(i+2).toNat]?
  s.write 2 i ((a+b+c)/3)
hls_certified filter as filterHLS

def noSupplier (_ : Unit) : List Int := []
def stages : List CertifiedHLS.Stage :=
  [producerHLS.entry.stage 5 0 0 1 5 noSupplier,
   filterHLS.entry.stage 5 1 0 1 3 noSupplier]
def pipeline : CertifiedHLS.Entry stages :=
  .cons producerHLS.entry (.cons filterHLS.entry .nil)
def sizes (a : Nat) : Nat := if a < 3 then 5 else 0
def layout : Array (Nat × Nat) := #[(0,5),(1,5),(2,5)]
def initial (last : Nat) : HybridWord.State :=
  ⟨fun _ => 0, fun a => if a = 0 then #[3,6,9,12,15]
    else if a ≤ last then Array.replicate 5 0 else #[]⟩

def checkText {source : List CertifiedHLS.Stage} {entry : CertifiedHLS.Entry source}
    {outputs : List Nat} {sizeOf : Nat → Nat} {memoryLayout : Array (Nat × Nat)} {budget : Nat}
    (c : Compiled entry outputs sizeOf memoryLayout budget)
    (s : HybridWord.State) (output : Nat) (expected : Array Int) : IO Unit := do
  let _ ← IO.ofExcept c.checkExternalPorts
  let start : RTL.InterfaceState c.backend.artifact.storageShape :=
    ⟨FiniteRuntime.pack _ (c.backend.initial s 0 0),true⟩
  let some result := SystemVerilog.runText c.text c.backend.artifact.storageShape 2048 start
    | throw (IO.userError "generated text did not finish")
  unless result.core.done && !result.busy && !result.core.error &&
      result.core.decode.data.arrays output == expected do
    throw (IO.userError "generated text result mismatch")

def main : IO Unit := do
  let out : System.FilePath := "artifacts/intro-example"
  IO.FS.createDirAll out
  let whole ← IO.ofExcept (incrementHLS.compile [1])
  let expected : Array Int := #[4,7,10,13,16]
  unless (increment (initial 1)).map (fun s => s.encode.arrays 1) == some expected do
    throw (IO.userError "whole-program source result mismatch")
  checkText whole (initial 1) 1 expected
  IO.FS.writeFile (out / "increment.sv") whole.text
  IO.FS.writeFile (out / "increment-ir.txt") (reprStr incrementHLS.native.wordBody.lower)
  IO.println "PASS increment: [3,6,9,12,15] → [4,7,10,13,16]"
  let optimized ← IO.ofExcept (← CertifiedHLS.compileWithSMT pipeline [2] sizes layout (out / "smt"))
  let .symbolic chosen := optimized.plan | throw (IO.userError "expected symbolic memory plan")
  unless chosen.policy == [1] do throw (IO.userError s!"expected FIFO array 1, got {chosen.policy}")
  let window := HybridUnifiedPipeline.compactStage
    (filterHLS.entry.kernel (stage := filterHLS.entry.stage 5 1 0 1 3 noSupplier)).lower
  unless window.code.initial.length == 3 && window.code.refill.length == 3 do
    throw (IO.userError "expected a three-value reuse buffer")
  let memoryReads := window.code.refill.filter (fun | .memory _ => true | .saved _ => false)
  unless memoryReads.length == 1 do throw (IO.userError "expected one new read per refill")
  IO.FS.writeFile (out / "window.txt") (reprStr window.code.initial ++ "\n" ++ reprStr window.code.refill)
  let result : Array Int := #[7,10,13,0,0]
  unless (CertifiedHLS.runSource stages 0 0 (initial 2)).map (fun s => s.encode.arrays 2) == some result do
    throw (IO.userError "pipeline source result mismatch")
  checkText optimized (initial 2) 2 result
  IO.FS.writeFile (out / "filter.sv") optimized.text
  IO.FS.writeFile (out / "filter-ir.txt") (reprStr filterHLS.wordBody.lower)
  IO.println s!"PASS filter: FIFO arrays={chosen.policy}, window=3, output=[7,10,13,0,0]"
