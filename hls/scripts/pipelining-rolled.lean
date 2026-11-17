import IRComparison.Circuit.Pipelining.StructuredCompiler
import IRComparison.Examples.CertifiedHLSExamples

open IRComparison Circuit Circuit.Pipelining CertifiedHLS CertifiedHLSExamples
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def check (name : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"FAIL {name}")
  IO.println s!"PASS {name}"

def runToStop (g : ClockGraph) (r : Circuit.Runtime) : Nat → Nat × Circuit.Runtime
  | 0 => (0,r)
  | n+1 => if r.done then (0,r) else let (k,t) := runToStop g (g.tick r) n; (k+1,t)

def visible (r : Circuit.Runtime) := (r.done,r.error,
  (List.range 8).map r.wires,(List.range 4).map r.data.regs,
  (List.range 3).map r.data.arrays,(List.range 3).map r.queues)

def input (n : Nat) : Payload :=
  ⟨⟨fun _ => 0,fun a => if a = 0 then #[10,20,30,40,50,60,70,80] else Array.replicate 8 0⟩,
    fun k => if k = 1 then n else 0,fun _ => []⟩

/-- The saved index makes the next iteration's increment safe to overlap
with this iteration's store. Scheduling, splitting and checks are automatic. -/
def copyLoop (read : Circuit.Expr := .memory 0 (.wire 2)) (dest : Nat := 1) : Circuit.Schedule :=
  .loop (.bin .lt (.wire 2) (.wire 1))
    (.seq (.step (.wire 3 (.wire 2)))
      (.seq (.step (.wire 4 read))
        (.seq (.step (.wire 2 (.bin .add (.wire 2) (.lit 1))))
          (.step (.store dest (.wire 3) (.wire 4))))))

def exercise (name : String) (s : Circuit.Schedule) (p : Payload)
    (improve : Bool := false) (fail : Bool := false) (caps : Array (Nat × Nat) := #[]) (emit : Bool := true) : IO Unit := do
  let before := scheduleStructure earliestProposal s
  let after := overlapLoops before
  let g := after.assemble caps
  let (oldCycles,old) := runToStop (before.assemble caps) (p.at 1) 2048
  let (cycles,result) := runToStop g (p.at 1) 2048
  check (name ++ "/same-state") (old.done && result.done && old.error == fail && result.error == fail &&
    (fail || visible old == visible result))
  if improve then check (name ++ "/faster") (cycles < oldCycles)
  IO.println s!"ROLLED {name}: cycles={oldCycles}->{cycles}, states={before.size+1}->{after.size+1}"
  if !emit then return
  let layout := #[(0,8),(1,8),(2,8)]
  let a := g.artifact (Array.replicate 8 ⟨0,4294967295⟩) layout layout
  let code ← IO.ofExcept (generateGraphModule a g [1])
  let initial : RTL.InterfaceState a.storageShape := ⟨FiniteRuntime.pack a.storageShape (p.at 1),true⟩
  let some physical := SystemVerilog.runText code.text a.storageShape cycles initial
    | throw (IO.userError s!"{name}: printed execution failed")
  check (name ++ "/printed-RTL") (physical.core.done && physical.core.error == fail &&
    (fail || physical.core.decode.data.arrays 1 == result.data.arrays 1))
  IO.FS.writeFile s!"artifacts/rolled-pipeline/{name}.sv" code.text

def main : IO Unit := do
  IO.FS.createDirAll "artifacts/rolled-pipeline"
  exercise "copy" copyLoop (input 8) true
  exercise "gather" (copyLoop (.memory 0 (.bin .sub (.lit 7) (.wire 2)))) (input 8) true
  exercise "zero" copyLoop (input 0)
  exercise "one" copyLoop (input 1)
  exercise "head-error" (copyLoop (.memory 0 (.lit 9))) (input 8) false true
  exercise "tail-error" copyLoop {input 8 with data := { (input 8).data with arrays := fun a => if a = 1 then #[] else (input 8).data.arrays a }} false true
  exercise "later-head-error" copyLoop (input 9) false true
  let badGuard : Circuit.Schedule := match copyLoop with
    | .loop _ body => .loop (.memory 0 (.lit 9)) body
    | s => s
  exercise "guard-error" badGuard (input 8) false true #[] false
  let fifoLoop : Circuit.Schedule :=
    .loop (.bin .lt (.wire 2) (.wire 1))
      (.seq (.step (.wire 3 (.wire 2)))
        (.seq (.step (.receive 0 4))
          (.seq (.step (.wire 2 (.bin .add (.wire 2) (.lit 1))))
            (.step (.store 1 (.wire 3) (.wire 4))))))
  exercise "fifo-exact" fifoLoop {input 8 with queues := fun _ => [10,20,30,40,50,60,70,80]} true false #[(0,8)]
  exercise "fifo-short" fifoLoop {input 8 with queues := fun _ => [10,20]} false true #[(0,8)]
  exercise "alias" (copyLoop (.memory 0 (.wire 2)) 0) (input 8)
  let noOverlap := scheduleStructure earliestProposal (copyLoop (.memory 0 (.wire 2)) 0)
  check "alias/keeps-loop" (match overlapLoops noOverlap with | .loop .. => true | _ => false)
  let guarded := Circuit.Schedule.branch (.wire 0) copyLoop .skip
  exercise "nested-branch" guarded {input 8 with wires := fun k => if k = 0 then 1 else (input 8).wires k} true
  -- Only the runtime bound changes; no compiler expansion or fuel is used.
  let replaceLimit (n : Int) : Circuit.Schedule := match copyLoop with
    | .loop _ body => .loop (.bin .lt (.wire 2) (.lit n)) body
    | s => s
  check "million-iterations/same-control-size"
    ((structuredTree (replaceLimit 8)).size == (structuredTree (replaceLimit 1000000)).size)
  -- End-to-end native entry: zero static-expansion fuel does not disable
  -- the default backend or weaken its theorem.
  let compiled ← IO.ofExcept (filterHLS.compile 5 0 0 1 3 supply [1] sizes layout 0)
  check "native/default-rolled-without-expansion-budget" (compiled.backend.route == "structured")
  match compiled.backend with
  | .structured b _ =>
    let generated := schedule layout (HybridUnifiedPipeline.lower compiled.plan)
    let p := wordPayload ⟨fun _ => 0,fun a => if a = 0 then #[3,6,9,12,15] else Array.replicate 5 0⟩ 0 0
    let (n,_) := runToStop ((scheduleStructure earliestProposal generated.schedule).assemble generated.build.queues) (p.at 1) 2048
    let (m,r) := runToStop b.graph (p.at 1) 2048
    check "native/output" (r.done && !r.error && r.data.arrays 1 == #[6,9,12,0,0])
    IO.println s!"NATIVE filter: clocks={n}->{m}"
  | _ => throw (IO.userError "unexpected backend")
