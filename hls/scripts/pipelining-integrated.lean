import IRComparison.Circuit.Pipelining.Dispatch
import IRComparison.Examples.PipeliningExamples
import IRComparison.Examples.WordFrontendExamples

open IRComparison IRComparison.Circuit IRComparison.Circuit.Pipelining
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def check (label : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"FAIL {label}")
  IO.println s!"PASS\t{label}"

def verify (name : String) (ks : List HybridWord.Kernel) (outputs : List Nat)
    (expected : Array Int) (values : Array HybridWord.Word := #[10,20,30,40,50]) : IO Unit := do
  IO.println s!"BEGIN\t{name}"
  let some p := HybridWord.compileProgram outputs (fun _ => 5) ks
    | throw (IO.userError "memory optimizer did not produce a plan")
  let layout := #[(0,5),(1,5),(2,5)]
  IO.println s!"PLAN\t{name}"
  let built ← IO.ofExcept (compileOptimizedScheduled p layout 4096)
  let integrated ← IO.ofExcept (integrate p layout 4096 .staticExpansion)
  check (name ++ "/integrated-entry") (integrated.isPipelined && integrated.text == built.module.text)
  let s : HybridWord.State := ⟨fun _ => 0,fun n => if n = 0 then values else if n < 3 then Array.replicate 5 0 else #[]⟩
  let result := (batchProgram built.realization.batches built.artifact.machine.capacities).run
    built.artifact.storageShape.wireRange (built.realization.batches.length+1) ((wordPayload s 0 0).at 0)
  let output := outputs.headD 0
  check (name ++ "/native") ((HybridWord.source 0 0 ks s).map (fun s => s.encode.arrays output) == some expected)
  check (name ++ "/rtl") (result.result.map (Option.map (fun s => s.arrays output)) == some (some expected))
  check (name ++ "/schedule") built.scheduleAccepted
  let generated := schedule layout (HybridUnifiedPipeline.lower p)
  let some (actions,_) := linearize 4096 [] generated.schedule
    | throw (IO.userError "unexpected linearization failure")
  check (name ++ "/overlap") (built.realization.batches.length < actions.length)
  let reads := actions.countP (fun a => match a with | .wire _ (.memory ..) => true | _ => false)
  let takes := actions.countP (fun a => match a with | .receive .. => true | _ => false)
  IO.FS.writeFile s!"artifacts/pipelining/rtl/{name}.sv" built.module.text
  IO.println s!"INTEGRATED\t{name}\troute={match HybridUnifiedPipeline.lower p with | .regions _ => "regions" | .expanded _ => "expanded" | .compact _ => "compact"}\tactions={actions.length}\tclocks={built.realization.batches.length+1}\twires={built.virtualWires}->{built.realization.widths.size}\tdirectMemoryLoadActions={reads}\treceives={takes}"

def main : IO Unit := do
  IO.FS.createDirAll "artifacts/pipelining/rtl"
  verify "integrated-buffer" [PipeliningExamples.filterCode.kernel 5 0 0 1 4 (fun _ => [])] [1] #[15,25,35,45,0]
  -- Historical fixture name; the default memory pass now ignores supplier lists.
  -- This checks memory retention, not external-input FIFO conversion.
  verify "integrated-input-fifo" [PipeliningExamples.filterCode.kernel 5 0 0 1 4 (fun _ => [0,1,2,3,4])] [1] #[15,25,35,45,0]
  verify "integrated-chain"
    [WordFrontendExamples.producer.kernel 5 0 0 1 5 (fun _ => [0,1,2,3,4]),
     WordFrontendExamples.consumer.kernel 5 1 0 1 4 (fun _ => [0,1,2,3,4])]
    [2] #[32,52,72,92,0]
  verify "integrated-reverse" [PipeliningExamples.filterCode.kernel 5 0 3 (-1) 4 (fun _ => [])] [1] #[15,25,35,45,0]
  verify "integrated-dilated" [PipeliningExamples.filterCode.kernel 5 0 0 2 2 (fun _ => [])] [1] #[15,0,35,0,0]
  verify "integrated-overflow" [PipeliningExamples.filterCode.kernel 5 0 0 1 4 (fun _ => [0,1,2,3,4])] [1]
    #[0,0,0,0,0] #[4294967295,1,4294967295,1,4294967295]
  let some plan := HybridWord.compileProgram [1] (fun _ => 5)
      [PipeliningExamples.filterCode.kernel 5 0 0 1 4 (fun _ => [0,1,2,3,4])]
    | throw (IO.userError "fallback plan")
  let fallback ← IO.ofExcept (integrate plan #[(0,5),(1,5),(2,5)] 0 .staticExpansion)
  check "budget/structured-route" (fallback.route == "structured")
  IO.FS.writeFile "artifacts/pipelining/rtl/integrated-budget-structured.sv" fallback.text
  let some dynamic := HybridWord.compileProgram [0] (fun _ => 5)
      [WordFrontendExamples.conditionalCode.kernel 5 0 0 1 1 (fun _ => [])]
    | throw (IO.userError "dynamic plan")
  let fallback ← IO.ofExcept (integrate dynamic #[(0,5)] 4096)
  check "dynamic/structured-route" (fallback.route == "structured")
  IO.FS.writeFile "artifacts/pipelining/rtl/integrated-dynamic-structured.sv" fallback.text
  let unknown := Circuit.Schedule.loop (.wire 0) .skip
  check "unknown-control/no-assumed-input" (linearize 16 [] unknown).isNone
  check "budget/no-partial-expansion" (linearize 0 [] .skip).isNone
