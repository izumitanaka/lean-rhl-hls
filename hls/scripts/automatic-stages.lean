import IRComparison.Frontend.LeanHLSCommand

open IRComparison HybridWord Circuit CertifiedHLS
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

-- No kernel markers, stage lists, input-array IDs, or iteration metadata.
def declarations : FixedMemory.Declarations := #[(0,5),(1,5),(2,5)]
def forward (s : HybridWord.State) : Option HybridWord.State := do
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
hls_fixed_program forward using declarations as forwardHLS

-- Reverse production and consumption, with a different reuse direction.
def reverse (s : HybridWord.State) : Option HybridWord.State := do
  let mut t := s
  for i in HybridWord.range 4 (-1) (-1) do
    let v ← (t.arrays 0)[i.toNat]?
    t ← t.write 1 i (v+1)
  for i in HybridWord.range 2 (-1) (-1) do
    let a ← (t.arrays 1)[i.toNat]?
    let b ← (t.arrays 1)[(i+1).toNat]?
    let c ← (t.arrays 1)[(i+2).toNat]?
    t ← t.write 2 i ((a+b+c)/3)
  return t
hls_fixed_program reverse using declarations as reverseHLS

-- FIFO order is unsuitable: retain memory instead of changing the source order.
def mismatch (s : HybridWord.State) : Option HybridWord.State := do
  let mut t := s
  for i in HybridWord.range 0 5 1 do
    let v ← (t.arrays 0)[i.toNat]?
    t ← t.write 1 i (v+1)
  for i in HybridWord.range 4 (-1) (-1) do
    let v ← (t.arrays 1)[i.toNat]?
    t ← t.write 2 i (v+1)
  return t
hls_fixed_program mismatch using declarations as mismatchHLS

-- Non-unit stride and sparse array IDs; analysis must not assume 0/1/2.
def sparseDeclarations : FixedMemory.Declarations := #[(7,5),(42,5),(101,5)]
def sparse (s : HybridWord.State) : Option HybridWord.State := do
  let mut t := s
  for i in HybridWord.range 0 5 1 do
    let v ← (t.arrays 7)[i.toNat]?
    t ← t.write 42 i (v+2)
  for i in HybridWord.range 0 5 2 do
    let v ← (t.arrays 42)[i.toNat]?
    t ← t.write 101 i (v+3)
  return t
hls_fixed_program sparse using sparseDeclarations as sparseHLS

-- Both sides strided: the current affine router conservatively retains memory.
def sparseBoth (s : HybridWord.State) : Option HybridWord.State := do
  let mut t := s
  for i in HybridWord.range 0 5 2 do
    let v ← (t.arrays 7)[i.toNat]?
    t ← t.write 42 i (v+2)
  for i in HybridWord.range 0 5 2 do
    let v ← (t.arrays 42)[i.toNat]?
    t ← t.write 101 i (v+3)
  return t
hls_fixed_program sparseBoth using sparseDeclarations as sparseBothHLS

-- A lexical value spanning both loops stays bound at its original evaluation point.
def captured (s : HybridWord.State) : Option HybridWord.State := do
  let old := s.regs 0
  let mut t := s.set 0 99
  for i in HybridWord.range 0 5 1 do
    let v ← (t.arrays 0)[i.toNat]?
    t ← t.write 1 i (v+old)
  for i in HybridWord.range 0 5 1 do
    let v ← (t.arrays 1)[i.toNat]?
    t ← t.write 2 i v
  return t
hls_fixed_program captured using declarations as capturedHLS

-- Constant natural ranges in ordinary foldlM notation.
def natural (s : HybridWord.State) : Option HybridWord.State := do
  let t ← (List.range (5 : Word).toNat).foldlM (fun t k => do
    let v ← (t.arrays 0)[(BitVec.ofNat 32 k).toNat]?
    t.write 1 (BitVec.ofNat 32 k) (v+1)) s
  (List.range (5 : Word).toNat).foldlM (fun t k => do
    let v ← (t.arrays 1)[(BitVec.ofNat 32 k).toNat]?
    t.write 2 (BitVec.ofNat 32 k) v) t
hls_fixed_program natural using declarations as naturalHLS

-- Prefer an intermediate array over an earlier-declared external input.
def twoInputs (s : HybridWord.State) : Option HybridWord.State := do
  let mut t := s
  for i in HybridWord.range 0 5 1 do
    let v ← (t.arrays 0)[i.toNat]?
    t ← t.write 1 i (v+1)
  for i in HybridWord.range 0 5 1 do
    let a ← (t.arrays 0)[i.toNat]?
    let b ← (t.arrays 1)[i.toNat]?
    if a != 0 then t ← t.write 2 i (a+b)
    else t ← t.write 2 i b
  return t
hls_fixed_program twoInputs using declarations as twoInputsHLS

#guard (AutomaticStages.pieces (.forStatic 0 1000000 1 .skip)).length == 1
#guard ((AutomaticStages.pieces (.forStatic 0 1000000 1 .skip)).head?.map (·.count)) == some 1000000

-- Failure after a completed producer is still observable.
def invalid (s : HybridWord.State) : Option HybridWord.State := do
  let mut t := s
  for i in HybridWord.range 0 5 1 do
    let v ← (t.arrays 0)[i.toNat]?
    t ← t.write 1 i v
  for i in HybridWord.range 0 6 1 do
    let v ← (t.arrays 1)[i.toNat]?
    t ← t.write 2 i v
  return t
hls_fixed_program invalid using declarations as invalidHLS

def zero (s : HybridWord.State) : Option HybridWord.State := do
  let mut t := s
  for i in HybridWord.range 3 3 1 do
    let v ← (t.arrays 0)[99]?
    t ← t.write 1 i v
  return t
hls_fixed_program zero using declarations as zeroHLS

def initial (ds : FixedMemory.Declarations) (input : Nat) : HybridWord.State :=
  ⟨fun _ => 10,fun a => if a = input then #[3,6,9,12,15]
    else Array.replicate (FixedMemory.sizes ds a) 0⟩

def check (name : String) (e : FixedHLS.Entry native) (input output : Nat)
    (expectedStages : Nat) (expectedPolicy : List Nat)
    (c : e.Compiled [output] 4096) : IO Unit := do
  unless e.stages.length == expectedStages do
    throw (IO.userError s!"{name}: expected {expectedStages} stages, got {e.stages.length}")
  let .symbolic plan := c.plan | throw (IO.userError s!"{name}: expected symbolic plan")
  unless plan.policy == expectedPolicy do
    throw (IO.userError s!"{name}: expected FIFO {expectedPolicy}, got {plan.policy}")
  let s := initial e.declarations input
  let expected := native s
  let actual := CertifiedHLS.runSource e.stages 0 0 s
  unless actual.map (fun t => (t.regs 0,t.arrays output)) ==
      expected.map (fun t => (t.regs 0,t.arrays output)) do
    throw (IO.userError s!"{name}: stage/source mismatch")
  let _ ← IO.ofExcept c.checkExternalPorts
  let start : RTL.InterfaceState c.backend.artifact.storageShape :=
    ⟨FiniteRuntime.pack _ (c.backend.initial s 0 0),true⟩
  let some result := SystemVerilog.runText c.text c.backend.artifact.storageShape 256 start
    | throw (IO.userError s!"{name}: text did not finish")
  unless result.core.done && !result.busy && result.core.error == expected.isNone do
    throw (IO.userError s!"{name}: status mismatch")
  if let some t := expected then
    unless result.core.decode.data.arrays output == t.encode.arrays output do
      throw (IO.userError s!"{name}: output mismatch")
  let out : System.FilePath := "artifacts/automatic-stages"
  IO.FS.writeFile (out / s!"{name}.sv") c.text
  IO.println s!"PASS {name}: stages={e.stages.length}, FIFO={plan.policy}, output={expected.map (fun t => t.encode.arrays output)}"

def main : IO Unit := do
  IO.FS.createDirAll "artifacts/automatic-stages"
  check "forward" forwardHLS.entry 0 2 2 [1] (← IO.ofExcept (forwardHLS.compile [2]))
  check "reverse" reverseHLS.entry 0 2 2 [1] (← IO.ofExcept (reverseHLS.compile [2]))
  check "mismatch" mismatchHLS.entry 0 2 2 [] (← IO.ofExcept (mismatchHLS.compile [2]))
  check "sparse" sparseHLS.entry 7 101 2 [42] (← IO.ofExcept (sparseHLS.compile [101]))
  check "sparse-both" sparseBothHLS.entry 7 101 2 [] (← IO.ofExcept (sparseBothHLS.compile [101]))
  check "captured" capturedHLS.entry 0 2 1 [] (← IO.ofExcept (capturedHLS.compile [2]))
  check "natural" naturalHLS.entry 0 2 2 [1] (← IO.ofExcept (naturalHLS.compile [2]))
  check "two-inputs" twoInputsHLS.entry 0 2 2 [1] (← IO.ofExcept (twoInputsHLS.compile [2]))
  check "invalid" invalidHLS.entry 0 2 2 [] (← IO.ofExcept (invalidHLS.compile [2]))
  check "zero" zeroHLS.entry 0 2 1 [1] (← IO.ofExcept (zeroHLS.compile [2]))
  check "forward-smt" forwardHLS.entry 0 2 2 [1]
    (← IO.ofExcept (← forwardHLS.compileWithSMT [2] "artifacts/automatic-stages/smt"))
