import IRComparison.Examples.CertifiedHLSExamples

open IRComparison HybridWord Circuit Circuit.Pipelining CertifiedHLS CertifiedHLSExamples
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def verify {source : List Stage} {entry : Entry source}
    (name route : String) (c : Compiled entry outputs sizes layout fuel)
    (values : Array Word) (expected : Option (Array Int)) (x : Word := 0) (y : Word := 0) : IO Unit := do
  unless c.backend.route == route do throw (IO.userError s!"{name}: wrong backend")
  let s : HybridWord.State := ⟨fun _ => 0,
    fun n => if n = 0 then values else if n < 3 then Array.replicate 5 0 else #[]⟩
  let source := CertifiedHLS.runSource source x y s
  let output := outputs.headD 0
  unless source.map (fun s => s.encode.arrays output) == expected do
    throw (IO.userError s!"{name}: native result")
  let r : RTL.InterfaceState c.backend.artifact.storageShape :=
    ⟨FiniteRuntime.pack c.backend.artifact.storageShape (c.backend.initial s x y),true⟩
  let some result := SystemVerilog.runText c.text c.backend.artifact.storageShape 256 r
    | throw (IO.userError s!"{name}: parse/run failed")
  unless result.core.done && !result.busy do throw (IO.userError s!"{name}: termination")
  match expected with
  | none => unless result.core.error do throw (IO.userError s!"{name}: error correspondence")
  | some expected =>
    unless !result.core.error && result.core.decode.data.arrays output == expected do
      throw (IO.userError s!"{name}: public output")
  if let some final := source then
    for a in outputs do
      unless result.core.decode.data.arrays a == final.encode.arrays a do
        throw (IO.userError s!"{name}: public array {a}")
  IO.FS.writeFile s!"artifacts/certified-hls/{name}.sv" c.text
  IO.println s!"PASS {name}: native Lean → parsed RTL ({route})"

/-- Exercise the sequential alternative from a real source, without inventing
a broken IR. This is route coverage, not an observed auto-fallback case. -/
def sequential (c : Compiled entry outputs sizes layout fuel) : Except String (Compiled entry outputs sizes layout fuel) := do
  match hc : Circuit.compile layout (HybridUnifiedPipeline.lower c.plan) CountedBackend.named.build with
  | .error why => throw why
  | .ok checked =>
    match he : checked.emit outputs with
    | .error why => throw why
    | .ok text =>
      let backend : Integrated c.plan layout fuel := .sequential checked text hc he "route coverage"
      if ports : ∀ a ∈ outputs, backend.artifact.storageShape.hasMemory a then
        return ⟨c.plan,backend,c.outputsSafe,ports⟩
      else throw "missing output"

def main : IO Unit := do
  IO.FS.createDirAll "artifacts/certified-hls"
  let filter ← IO.ofExcept (filterHLS.compile 5 0 0 1 3 supply [1] sizes layout 4096)
  verify "filter" "structured" filter #[3,6,9,12,15] (some #[6,9,12,0,0])
  verify "filter-overflow" "structured" filter #[4294967295,1,2,3,4] (some #[0,2,3,0,0])
  let expanded ← IO.ofExcept (filterHLS.compile 5 0 0 1 3 supply [1] sizes layout 4096 .staticExpansion)
  verify "filter-expanded" "static" expanded #[3,6,9,12,15] (some #[6,9,12,0,0])
  let reverse ← IO.ofExcept (filterHLS.compile 5 0 2 (-1) 3 supply [1] sizes layout 4096)
  verify "reverse" "structured" reverse #[3,6,9,12,15] (some #[6,9,12,0,0])
  let budget ← IO.ofExcept (filterHLS.compile 5 0 0 1 3 supply [1] sizes layout 0 .staticExpansion)
  verify "budget-structured" "structured" budget #[3,6,9,12,15] (some #[6,9,12,0,0])
  let conditional ← IO.ofExcept (conditionalHLS.compile 5 0 0 1 1 (fun _ => []) [1] sizes layout 4096)
  verify "branch-true" "structured" conditional #[3,6,9,12,15] (some #[7,0,0,0,0]) 7 1
  verify "branch-false" "structured" conditional #[3,6,9,12,15] (some #[0,0,0,0,0]) 7 0
  let chain ← IO.ofExcept (CertifiedHLS.compile chainEntry [2] sizes layout 4096)
  verify "chain" "structured" chain #[3,6,9,12,15] (some #[8,14,20,26,32])
  let publicChain ← IO.ofExcept (CertifiedHLS.compile chainEntry [1,2] sizes layout 4096)
  verify "public-chain" "structured" publicChain #[3,6,9,12,15] (some #[4,7,10,13,16])
  let empty ← IO.ofExcept (filterHLS.compile 5 0 999 1 0 supply [1] sizes layout 4096)
  verify "zero-count" "structured" empty #[3,6,9,12,15] (some #[0,0,0,0,0])
  let strideTwo ← IO.ofExcept (filterHLS.compile 5 0 0 2 2 supply [1] sizes layout 4096)
  verify "stride-two" "structured" strideTwo #[3,6,9,12,15] (some #[6,0,12,0,0])
  let serial ← IO.ofExcept (sequential filter)
  verify "sequential-route" "sequential" serial #[3,6,9,12,15] (some #[6,9,12,0,0])
  let oob ← IO.ofExcept (filterHLS.compile 5 0 4 1 1 (fun _ => []) [1] sizes layout 4096)
  verify "source-error" "structured" oob #[3,6,9,12,15] none
  match filterHLS.compile 5 0 0 1 3 supply [9] sizes layout 4096 with
  | .error _ => IO.println "PASS missing-public-output/rejected"
  | .ok _ => throw (IO.userError "missing public output accepted")
