import IRComparison.Tests
import IRComparison.Frontend.WordStructuralBody

/-! Check the new path directly; compatibility success cannot hide a miss.
This is regression coverage, not the independent grammar-completeness proof. -/
open Lean Elab Command IRComparison
set_option maxRecDepth 65536
set_option maxHeartbeats 0

def theoremBody : Lean.Expr → Lean.Expr
  | .forallE _ _ body _ => theoremBody body
  | e => e

run_cmd do
  let native ← getEnv
  let sources := native.constants.toList.filterMap fun (name,info) => do
    if !name.toString.endsWith ".wordBody_correct" then none else do
      let rhs ← (theoremBody info.type).getAppArgs.toList.getLast?
      rhs.getAppFn.constName?
  let sources := sources.mergeSort (fun a b => a.toString ≤ b.toString)
  let mut records : Array Json := #[]
  let mut missing := 0
  for source in sources do
    let start ← IO.monoMsNow
    let result := WordFrontend.StructuralBody.compileRetained native source
    let stop ← IO.monoMsNow
    unless result.isSome do missing := missing + 1
    logInfo m!"{if result.isSome then "PASS" else "MISS"} structural {source} ({stop-start}ms)"
    records := records.push (Json.mkObj [("source",toJson source.toString),
      ("structural_success",toJson result.isSome),("ms",toJson (stop-start))])
  IO.FS.createDirAll "artifacts/structural-frontend"
  IO.FS.writeFile "artifacts/structural-frontend/coverage.json" (Json.mkObj [
    ("tested",toJson sources.length),("misses",toJson missing),("cases",toJson records),
    ("note",toJson "Direct ordinary retained-argument entry checks of existing ordinary-Lean inputs. Not a grammar-wide success theorem.")]).pretty
  logInfo m!"STRUCTURAL {sources.length-missing}/{sources.length}"
