import IRComparison.Examples.WordWorkloads
import IRComparison.Circuit.PolicyProperties

open IRComparison HybridSymbolicGlobal
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

-- check-timeout-retention.py supplies a fake z3: first routing succeeds;
-- later queries exit after spawning a child which keeps the output pipes.
def main : IO Unit := do
  let a := WordWorkloads.Global.producerA.kernel 8 0 0 1 8 (fun _ => [])
  let c := WordWorkloads.Global.consumerA.kernel 8 1 0 1 8 (fun _ => [])
  let b := WordWorkloads.Global.producerB.kernel 8 0 0 1 8 (fun _ => [])
  let d := WordWorkloads.Global.consumerB.kernel 8 5 0 1 8 (fun _ => [])
  let ps := HybridUnifiedPipeline.compactStages ([a,c,b,d].map HybridWord.Kernel.lower)
  let started ← IO.monoMsNow
  let root ← HybridRoutingVC.freshDirectory "artifacts/process-deadline/retention"
  let some plan ← compileWithSMT [2,6] (fun _ => 8) ps root 2000
    | throw (IO.userError "timeout lost compilation")
  let elapsed := (← IO.monoMsNow)-started
  unless plan.policy == [1] && elapsed < 5000 do
    throw (IO.userError s!"timeout lost adopted policy: {plan.policy}, {elapsed}ms")
  IO.FS.writeFile (root / "retained.txt") s!"policy={plan.policy} elapsed={elapsed}ms\n"
  IO.println s!"PASS adopted policy retained after descendant-pipe timeout: {plan.policy}, {elapsed}ms"
