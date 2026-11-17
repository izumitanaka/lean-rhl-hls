import IRComparison.Examples.PipelineWorkloads
import IRComparison.Circuit.Pipelining.Dispatch

open IRComparison IRComparison.Circuit IRComparison.Circuit.Pipelining
open IRComparison.PipelineWorkloads IRComparison.PipeliningExamples
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def check (label : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"FAIL {label}")
  IO.println s!"PASS\t{label}"

def state (input : Array HybridWord.Word) (second : Array HybridWord.Word := #[0,0,0,0]) : HybridWord.State :=
  ⟨fun _ => 0, fun a => if a = 0 then input else if a = 1 then second else #[0,0,0,0]⟩

def workloadView (s : State) := (s.regs 0, s.arrays 1, s.arrays 2)

def exercise (name : String) (k : HybridWord.Kernel) (s : HybridWord.State)
    (output : Nat) (expected : Option (Array Int)) (count : HybridWord.Word := 0) : IO Unit := do
  let native := k.source 0 0 s
  check (name ++ "/expected") (native.map (fun s => s.encode.arrays output) == expected)
  if native.isSome then check (name ++ "/count") (native.map (fun s => s.regs 0) == some count)
  for ii in [1,2,3] do
    let (t,_) := pipelineWord k {} ii
    check s!"{name}/II{ii}/native" ((t.execute #[] 512 (wordPayload s 0 0)).map
      (Option.map workloadView) == some (native.map (fun s => workloadView s.encode)))
    match t with
    | .original _ => IO.println s!"SCHEDULE\t{name}\tII={ii}\tstructured fallback"
    | .scheduled code plan =>
      IO.println s!"SCHEDULE\t{name}\tII={ii}\taccepted={plan.accepted}\tactions={code.size}\tclocks={plan.cycles.length}"

def emitIntegrated (name : String) (k : HybridWord.Kernel) (output : Nat) : IO Unit := do
  let some p := HybridWord.compileProgram [output] (fun _ => 4) [k]
    | throw (IO.userError s!"{name}: no memory plan")
  -- Keep the historical static-expansion latency comparison explicit.
  let result ← IO.ofExcept (integrate p #[(0,4),(1,4),(2,4)] 4096 .staticExpansion)
  IO.FS.writeFile s!"artifacts/pipelining/workloads/{name}.sv" result.text
  IO.println s!"INTEGRATED\t{name}\tpipelined={result.isPipelined}\treason={result.fallbackReason}"
  match result with
  | .pipelined built _ => IO.println s!"RTL\t{name}\tclocks={built.realization.batches.length+1}"
  | .structured built _ => IO.println s!"RTL\t{name}\tstructured states={built.graph.nodes.size}"
  | .sequential .. => pure ()

def main : IO Unit := do
  IO.FS.createDirAll "artifacts/pipelining/workloads"
  let gather := gatherCode.kernel 4 0 0 1 4 (fun _ => [])
  let hist := histogramCode.kernel 4 0 0 1 4 (fun _ => [])
  let select := compactCode.kernel 4 0 0 1 4 (fun _ => [])
  check "gather/II1-selected" (match (pipelineWord gather {} 1).1 with
    | .scheduled _ p => p.accepted | _ => false)
  check "histogram/II1-rejected" (match (pipelineWord hist {} 1).1 with
    | .scheduled _ p => !p.accepted | _ => false)
  check "histogram/II2-selected" (match (pipelineWord hist {} 2).1 with
    | .scheduled _ p => p.accepted | _ => false)
  check "select/dynamic-retained" (match (pipelineWord select {} 1).1 with
    | .original _ => true | _ => false)
  exercise "gather" gather (state #[2,0,3,1] #[10,20,30,40]) 2 (some #[31,11,41,21])
  exercise "gather-oob" gather (state #[2,4,3,1] #[10,20,30,40]) 2 none
  exercise "hist-repeat" hist (state #[3,3,1,3]) 1 (some #[0,1,0,3])
  exercise "hist-distinct" hist (state #[0,1,2,3]) 1 (some #[1,1,1,1])
  exercise "hist-wrap" hist (state #[0,0,0,0] #[4294967295,0,0,0]) 1 (some #[3,0,0,0])
  exercise "hist-oob" hist (state #[0,4,0,0]) 1 none
  exercise "select-mixed" select (state #[0,8,0,9]) 1 (some #[8,9,0,0]) 2
  exercise "select-none" select (state #[0,0,0,0]) 1 (some #[0,0,0,0])
  exercise "select-all" select (state #[2,8,1,9]) 1 (some #[2,8,1,9]) 4
  for (name,k,output) in [("gather",gather,2),("histogram",hist,1),("select",select,1)] do
    emitIntegrated name k output
  -- A bad overlap loses a repeated-key update. The production checker rejects it.
  let actions : Array Action := #[.wire 2 (.memory 1 (.lit 3)),
    .store 1 (.lit 3) (.bin .add (.wire 2) (.lit 1)),
    .wire 3 (.memory 1 (.lit 3)), .store 1 (.lit 3) (.bin .add (.wire 3) (.lit 1))]
  let candidate := [[0,2],[1],[3]]
  let p := wordPayload (state #[]) 0 0
  check "hist-collision/rejected" (!(compile actions candidate).accepted)
  check "hist-collision/counterexample"
    ((runCycles (fun _ => 0) actions candidate p).map (fun p => p.data.arrays 1) == some #[0,0,0,1] &&
     (sourceEval (fun _ => 0) actions p).map (fun p => p.data.arrays 1) == some #[0,0,0,2])
  -- FIFO compaction at the existing control level: this is not native push syntax.
  let conditional : Circuit.Schedule := .branch (.wire 0) (.step (.send 0 (.wire 1))) .skip
  let transformed := transform conditional (fun _ => [])
  check "conditional-fifo/structured" (match transformed with | .original _ => true | _ => false)
  let full : Payload := { p with wires := fun n => if n = 1 then 9 else 0, queues := fun _ => [8] }
  let yes := { full with wires := fun n => if n = 0 then 1 else if n = 1 then 9 else 0 }
  check "conditional-fifo/false-full-skips" (match transformed.execute #[(0,1)] 8 full with
    | some (some _) => true | _ => false)
  check "conditional-fifo/true-full-errors" (match transformed.execute #[(0,1)] 8 yes with
    | some none => true | _ => false)
