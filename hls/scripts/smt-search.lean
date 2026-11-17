import IRComparison.Examples.WordWorkloads
import IRComparison.Circuit.PolicyProperties

open IRComparison HybridSymbolicGlobal
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def main : IO Unit := do
  let root ← HybridRoutingVC.freshDirectory "artifacts/smt-greedy"
  let a := WordWorkloads.Global.producerA.kernel 8 0 0 1 8 (fun _ => [])
  let b := WordWorkloads.Global.consumerA.kernel 8 1 0 1 8 (fun _ => [])
  let ps := HybridUnifiedPipeline.compactStages ([a,b].map HybridWord.Kernel.lower)
  let some purePlan := compile [2] (fun _ => 8) ps | throw (IO.userError "pure memory baseline lost")
  unless purePlan.policy == [1] do throw (IO.userError "pure greedy did not accept the chain")
  let some zero ← compileWithSMT [2] (fun _ => 8) ps (root / "zero") 0
    | throw (IO.userError "zero budget failed compilation")
  unless zero.policy == [] do throw (IO.userError "zero budget unexpectedly optimized")
  let some live ← compileWithSMT [2] (fun _ => 8) ps (root / "live")
    | throw (IO.userError "SMT greedy failed")
  unless live.policy == [1] do throw (IO.userError "SMT chain not selected")
  -- Many duplicate occurrences of one write do not create a powerset.
  let repeated := List.replicate 100 (HybridUnifiedPipeline.compactStage a.lower)
  unless (candidates [2] repeated).length == 1 do throw (IO.userError "duplicate candidate")
  let noneSelected := compile [2] (fun _ => 8) repeated
  unless noneSelected.isSome do throw (IO.userError "incompatible candidates lost memory plan")
  let memory := (HybridUnifiedPipeline.compactStage b.lower).code
  let sequence : CompactSequence.Seq := ⟨0,1,8⟩
  let absent ← HybridRoutingVC.solve memory sequence (root / "missing") none "/no-such-hls-test-solver"
  unless absent.isNone do throw (IO.userError "missing solver accepted")
  -- A child ignoring SIGTERM must still be killed by the host deadline.
  let started ← IO.monoMsNow
  let timed ← HybridRoutingVC.processUntil "python3"
    #["-c","import signal,time; signal.signal(signal.SIGTERM, signal.SIG_IGN); print('started', flush=True); time.sleep(30)"]
    (started+100)
  unless timed.timedOut && (← IO.monoMsNow)-started < 3000 do
    throw (IO.userError "host deadline did not stop a faulty child")
  -- Parent exit is not completion: a descendant still owns both writers.
  for (name,childCode) in [
      ("both", "import time; time.sleep(30)"),
      ("stderr-only", "import os,time; os.close(1); time.sleep(30)"),
      ("stdout-only", "import os,time; os.close(2); time.sleep(30)")] do
    let started ← IO.monoMsNow
    let parent := "import subprocess; subprocess.Popen(['python3','-c'," ++
      (Lean.toJson childCode).compress ++ "]); print('parent exited', flush=True)"
    let result ← HybridRoutingVC.processUntil "python3" #["-c",parent] (started+300)
    let elapsed := (← IO.monoMsNow)-started
    unless result.timedOut && result.output.exitCode == 0 && !result.managementError && elapsed < 1500 do
      throw (IO.userError s!"descendant pipe {name}: {elapsed}ms {result.report}")
    IO.FS.writeFile (root / s!"descendant-{name}.json") result.report
    IO.println s!"PASS parent exited / descendant holds {name}: {elapsed}ms, timed out"
  -- EOF alone is not completion either: the direct child may still run.
  let started ← IO.monoMsNow
  let closed ← HybridRoutingVC.processUntil "python3"
    #["-c","import os,time; os.close(1); os.close(2); time.sleep(30)"] (started+100)
  unless closed.timedOut && !closed.managementError && (← IO.monoMsNow)-started < 1500 do
    throw (IO.userError "closed pipes bypassed the child deadline")
  -- Simultaneous callers using the same root have separate transcripts.
  let one ← IO.asTask (HybridRoutingVC.solve memory sequence (root / "concurrent")) .dedicated
  let two ← IO.asTask (HybridRoutingVC.solve memory sequence (root / "concurrent")) .dedicated
  unless (← IO.ofExcept one.get).isSome && (← IO.ofExcept two.get).isSome do
    throw (IO.userError "concurrent solver calls failed")
  unless (← (root / "concurrent").readDir).size == 2 do
    throw (IO.userError "solver transcripts collided")
  IO.FS.writeFile (root / "result.txt") "PASS: pure/SMT greedy, zero budget, rejected candidates, missing solver, host kill, concurrent transcripts\n"
  IO.println s!"PASS SMT greedy and external-process boundaries: {root}"
