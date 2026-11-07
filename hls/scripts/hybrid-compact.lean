import IRComparison.Hybrid.HybridInputs
import IRComparison.Hybrid.HybridUnifiedPipeline
import IRComparison.Hybrid.HybridCompactTransport
open IRComparison

def check (name : String) (ks : List HybridIR.Kernel)
    (p : HybridUnifiedPipeline.Plan [4] (fun _ => 64) ks) : IO Unit := do
  match p with
  | .expanded _ => throw (IO.userError s!"{name}: expected counted compilation")
  | .compact _ => pure ()
  let source := HybridIR.source 0 0 ks WindowWorkloads.initial
  let observe := fun s : State => s.arrays 4
  let actual := p.eval 0 0 WindowWorkloads.initial
  unless source.isSome && actual.map observe == source.map observe do
    throw (IO.userError s!"{name}: source mismatch")
  let some state := actual | throw (IO.userError "failed result")
  unless [1,2,3].all (fun a => (state.arrays a).isEmpty) do
    throw (IO.userError s!"{name}: retained intermediate array")
  match HybridUnifiedPipeline.run 0 0 100000
      (HybridUnifiedPipeline.start (HybridUnifiedPipeline.lower p) WindowWorkloads.initial) with
  | .stopped r => unless r.map observe == actual.map observe do throw (IO.userError s!"{name}: control mismatch")
  | _ => throw (IO.userError s!"{name}: control did not finish")
  IO.println s!"{name}: counted mixed IR, source, optimized result and control agree"

def largeGeometry (n : Nat) (p : HybridUnifiedPipeline.Plan outputs sizes ks) : Bool :=
  match p with
  | .expanded _ => false
  | .compact p => p.sender.code.count == n && p.sender.code.initial.length == 3 && p.sender.code.refill.length == 3

def generatedSequence (p : HybridUnifiedPipeline.Plan outputs sizes ks) : Option CompactSequence.Seq :=
  match p with
  | .expanded _ => none
  | .compact p => some p.sender.sequence

def checkQueries (directory : System.FilePath) (wanted : CompactSequence.Seq) : IO Unit := do
  for path in [directory,directory / "next",directory / "next" / "next"] do
    let request ← IO.FS.readFile (path / "request.smt2")
    let response ← IO.FS.readFile (path / "response.txt")
    unless (CompactSequence.accept wanted request response).isSome do
      throw (IO.userError s!"solver response was not accepted: {path}")

def main : IO Unit := do
  for w in HybridInputs.UnifiedWorkloads.workloads do
    let some p := HybridUnifiedPipeline.compile [4] (fun _ => 64) w.imperative
      | throw (IO.userError s!"{w.name}: compile failed")
    check w.name w.imperative p
    let some smt ← HybridUnifiedPipeline.compileWithSMT [4] (fun _ => 64) w.imperative
        (System.FilePath.mk "artifacts/hybrid-compact" / w.name)
      | throw (IO.userError s!"{w.name}: SMT compile failed")
    check (w.name ++ "/SMT") w.imperative smt
    let some wanted := generatedSequence smt | throw (IO.userError "expected solver chain")
    checkQueries (System.FilePath.mk "artifacts/hybrid-compact" / w.name) wanted
  let n := 1000000000
  let size := n+4
  -- Suppliers deliberately throw if forced. Counted compilation must never
  -- enumerate the source loop or consult expanded supplier lists.
  let supply := fun _ : Unit => panic! "expanded supplier forced"
  let ks := [
    HybridInputs.WindowWorkloads.filterCode.hybridKernel size 0 0 1 n supply,
    HybridInputs.StreamWorkloads.sink.hybridKernel size 1 0 1 n supply,
    HybridInputs.AutoPipelineExamples.stage3.hybridKernel size 2 0 1 n supply,
    HybridInputs.AutoPipelineExamples.stage4.hybridKernel size 3 0 1 n supply]
  let some large ← HybridUnifiedPipeline.compileWithSMT [4] (fun _ => size) ks "artifacts/hybrid-compact/billion"
    | throw (IO.userError "billion compile failed")
  unless largeGeometry n large do throw (IO.userError "billion code expanded or unexpected buffer geometry")
  checkQueries "artifacts/hybrid-compact/billion" ⟨0,1,n⟩
  IO.println "billion-count mixed compilation: fixed-size initial/refill and lazy suppliers passed"
  let some w := HybridInputs.UnifiedWorkloads.workloads.head? | throw (IO.userError "missing workload")
  IO.FS.writeFile "artifacts/hybrid-compact/not-directory" "simulate IO failure"
  let some fallback ← HybridUnifiedPipeline.compileWithSMT [4] (fun _ => 64) w.imperative
      "artifacts/hybrid-compact/not-directory/child" | throw (IO.userError "IO fallback failed")
  check "solver IO failure/static fallback" w.imperative fallback
