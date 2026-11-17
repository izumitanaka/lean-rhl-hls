import IRComparison.Examples.CertifiedHLSExamples

open IRComparison Circuit HybridWord CertifiedHLS
set_option maxRecDepth 65536
set_option maxHeartbeats 32000000

-- Retain actual register arguments before updating the same register.
def retainedSnapshot (i x _y : Word) (s : HybridWord.State) : Option HybridWord.State :=
  let s := s.set 0 x
  let update := fun (value : Word) (memory : HybridWord.State) => do
    let memory := memory.set 0 7
    memory.write 1 i value
  update (s.regs 0) s
hls_certified retainedSnapshot as snapshotHLS

def multiple (i x y : Word) (s : HybridWord.State) : Option HybridWord.State :=
  let s := s.set 0 x
  let s := s.set 1 y
  let update := fun (first : Word) (memory : HybridWord.State) (second : BitVec 32) => do
    let memory := memory.set 0 7
    let memory := memory.set 1 9
    memory.write 1 i (first + second)
  update (s.regs 0) s (s.regs 1)
hls_certified multiple as multipleHLS

def unused (i _x _y : Word) (s : HybridWord.State) : Option HybridWord.State := do
  let value ← (s.arrays 0)[99]?
  let ignore := fun (_value : Word) (memory : HybridWord.State) => memory.write 1 i 7
  ignore value s
hls_certified unused as unusedHLS

def branch (i x y : Word) (s : HybridWord.State) : Option HybridWord.State := do
  let update := fun (value : Word) (memory : HybridWord.State) => do
    let memory := memory.set 0 7
    memory.write 1 i value
  if y != 0 then
    let value ← (s.arrays 0)[99]?
    update value s
  else
    let s := s.set 0 x
    update (s.regs 0) s
hls_certified branch as branchHLS

def sizes (a : Nat) := if a < 2 then 1 else 0
def layout : Array (Nat × Nat) := #[(0,1),(1,1)]
def supply (_ : Unit) : List Int := []
def initial : HybridWord.State := ⟨fun _ => 0,fun a => if a = 0 then #[20] else #[0]⟩

def verify {source : List Stage} {entry : Entry source} (name : String)
    (c : Compiled entry [1] sizes layout 4096) (x y : Word) (expected : Option Int) : IO Lean.Json := do
  let native := CertifiedHLS.runSource source x y initial
  unless native.map (fun s => (s.arrays 1)[0]!.toNat) == expected.map Int.toNat do
    throw (IO.userError s!"{name}: source expectation")
  let start : RTL.InterfaceState c.backend.artifact.storageShape :=
    ⟨FiniteRuntime.pack _ (c.backend.initial initial x y),true⟩
  let some result := SystemVerilog.runText c.text c.backend.artifact.storageShape 128 start
    | throw (IO.userError s!"{name}: printed module does not run")
  unless result.core.done && !result.busy && result.core.error == expected.isNone do
    throw (IO.userError s!"{name}: control result")
  if let some v := expected then
    unless (result.core.decode.data.arrays 1)[0]? == some v do
      throw (IO.userError s!"{name}: output result")
  IO.FS.writeFile s!"artifacts/retained-arguments/{name}.sv" c.text
  IO.println s!"PASS {name}: ordinary Lean → {c.backend.route} → printed RTL"
  return Lean.Json.mkObj [("name",Lean.toJson name),("expected",Lean.toJson expected),
    ("x",Lean.toJson x.toNat),("y",Lean.toJson y.toNat)]

def main : IO Unit := do
  IO.FS.createDirAll "artifacts/retained-arguments"
  let snapshot ← IO.ofExcept (snapshotHLS.compile 1 0 0 1 1 supply [1] sizes layout 4096)
  let multiple ← IO.ofExcept (multipleHLS.compile 1 0 0 1 1 supply [1] sizes layout 4096)
  let unused ← IO.ofExcept (unusedHLS.compile 1 0 0 1 1 supply [1] sizes layout 4096)
  let branch ← IO.ofExcept (branchHLS.compile 1 0 0 1 1 supply [1] sizes layout 4096)
  let cases ← #[verify "snapshot" snapshot 3 0 (some 3),
    verify "multiple" multiple 3 5 (some 8),
    verify "overflow" multiple 4294967295 2 (some 1),
    verify "unused-invalid" unused 0 0 none,
    verify "unchosen-invalid" branch 3 0 (some 3),
    verify "chosen-invalid" branch 3 1 none].mapM id
  IO.FS.writeFile "artifacts/retained-arguments/cases.json" (Lean.toJson cases).pretty
