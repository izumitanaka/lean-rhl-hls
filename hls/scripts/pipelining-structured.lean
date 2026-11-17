import IRComparison.Circuit.Pipelining.Dispatch
import IRComparison.Examples.PipelineWorkloads
import IRComparison.Examples.WordFrontendExamples

open IRComparison IRComparison.Circuit IRComparison.Circuit.Pipelining
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def check (label : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"FAIL {label}")
  IO.println s!"PASS\t{label}"

def view (r : Circuit.Runtime) := (r.done,r.error,r.data.regs 0,r.data.arrays 0,r.data.arrays 1)

def runToStop (g : ClockGraph) (r : Circuit.Runtime) : Nat → Nat × Circuit.Runtime
  | 0 => (0,r)
  | n+1 => if r.done then (0,r) else let (k,t) := runToStop g (g.tick r) n; (k+1,t)

def compare (name : String) (s : Circuit.Schedule) (p : Payload) (caps : Array (Nat × Nat) := #[]) : IO Unit := do
  let graph := (scheduleStructure earliestProposal s).assemble caps
  let serial := (scheduleStructure sequential s).assemble caps
  let (n,r) := runToStop graph (p.at 1) 2048
  let (ns,rs) := runToStop serial (p.at 1) 2048
  check (name ++ "/terminates") (r.done && rs.done)
  let observation (r : Circuit.Runtime) := r.result.map (Option.map (fun t => (t.regs 0,t.arrays 0,t.arrays 1)))
  check (name ++ "/same-observation") (observation r == observation rs)
  let source := (s.assemble caps).run 2048 (p.at 1)
  check (name ++ "/original-control") (observation r == observation source)
  IO.println s!"CONTROL\t{name}\tclocks={ns}->{n}"

def state : HybridWord.State := ⟨fun _ => 0,fun _ => #[0,0,0,0]⟩

def emit (name : String) (k : HybridWord.Kernel) (output : Nat) (cases : List (Nat × Nat)) : IO Unit := do
  let some p := HybridWord.compileProgram [output] (fun _ => 4) [k] | throw (IO.userError s!"{name}: no memory plan")
  let built ← IO.ofExcept (compileStructured p #[(0,4),(1,4)])
  let integrated ← IO.ofExcept (integrate p #[(0,4),(1,4)])
  check (name ++ "/integrated-structured") (integrated.route == "structured")
  IO.FS.writeFile s!"artifacts/pipelining/structured/{name}.sv" built.module.text
  for (x,y) in cases do
    let p := wordPayload state (BitVec.ofNat 32 x) (BitVec.ofNat 32 y)
    let (clocks,actual) := runToStop built.graph (p.at 1) 2048
    let native := k.source (BitVec.ofNat 32 x) (BitVec.ofNat 32 y) state
    check s!"{name}/{x}/{y}/native" (actual.result.map (Option.map (fun s => s.arrays output)) ==
      some (native.map (fun s => s.encode.arrays output)))
    let rtl := built.graph.rtl.run built.artifact.storageShape.wireRange clocks (p.at 1)
    check s!"{name}/{x}/{y}/rtl" (view rtl == view actual)
    IO.println s!"NATIVE\t{name}\tx={x}\ty={y}\tclocks={clocks}"

def main : IO Unit := do
  IO.FS.createDirAll "artifacts/pipelining/structured"
  let pair : Circuit.Schedule := .seq (.step (.wire 2 (.lit 11))) (.step (.wire 3 (.lit 22)))
  let output : Circuit.Schedule := .seq (.step (.store 0 (.lit 0) (.wire 2))) (.step (.store 1 (.lit 0) (.wire 3)))
  let body := pair.seq output
  let p := wordPayload state 0 0
  compare "branch-false" (.branch (.wire 0) body .skip) p
  compare "branch-true" (.branch (.wire 0) body .skip) (wordPayload state 1 0)
  compare "unselected-oob" (.branch (.wire 0) (.step (.wire 2 (.memory 0 (.lit 9)))) body) p
  compare "failed-guard" (.branch (.memory 0 (.lit 9)) body .skip) p
  let increment : Circuit.Schedule := .step (.wire 4 (.bin .add (.wire 4) (.lit 1)))
  let loopBody := body.seq increment
  let loop : Circuit.Schedule := .loop (.bin .lt (.wire 4) (.wire 1)) loopBody
  compare "loop-zero" loop p
  compare "loop-multiple" loop (wordPayload state 0 4)
  compare "nested-branch-loop" (.branch (.wire 0) loop .skip) (wordPayload state 1 3)
  let inner : Circuit.Schedule := .seq (.step (.wire 5 (.lit 0)))
    (.loop (.bin .lt (.wire 5) (.lit 2))
      (body.seq (.step (.wire 5 (.bin .add (.wire 5) (.lit 1))))))
  let nested : Circuit.Schedule := .loop (.bin .lt (.wire 4) (.wire 1))
    ((Circuit.Schedule.branch (.wire 0) inner body).seq increment)
  compare "nested-loops" nested (wordPayload state 1 3)
  compare "nested-loops-other-branch" nested (wordPayload state 0 3)
  let graph := (scheduleStructure earliestProposal nested).assemble #[]
  let artifact := graph.artifact #[⟨0,4294967295⟩,⟨0,4294967295⟩,⟨0,22⟩,⟨0,22⟩,⟨0,4294967295⟩,⟨0,2⟩]
    #[(0,4),(1,4)] #[(0,4),(1,4)]
  let code ← IO.ofExcept (generateGraphModule artifact graph [0,1])
  IO.FS.writeFile "artifacts/pipelining/structured/nested.sv" code.text
  for (x,y) in [(1,3),(0,3),(1,0)] do
    let (clocks,r) := runToStop graph ((wordPayload state x y).at 1) 2048
    check s!"nested/{x}/{y}/rtl" (view r == view (graph.rtl.run artifact.storageShape.wireRange clocks ((wordPayload state x y).at 1)))
    IO.println s!"NESTED\tx={x}\ty={y}\tclocks={clocks}"
  compare "loop-body-failure" (.loop (.wire 0) (.step (.wire 2 (.memory 0 (.lit 8))))) (wordPayload state 1 0)
  let send : Circuit.Schedule := .branch (.wire 0) (.step (.send 0 (.lit 7))) .skip
  let full := {p with queues := fun _ => [8]}
  compare "fifo-unselected-full" send full #[(0,1)]
  compare "fifo-selected-full" send {full with wires := fun _ => 1} #[(0,1)]
  compare "fifo-empty" (.step (.receive 2 0)) p #[(0,1)]
  emit "conditional" (WordFrontendExamples.conditionalCode.kernel 4 0 0 1 1 (fun _ => [])) 0 [(7,0),(7,1)]
  emit "dynamic-loop" (WordFrontendExamples.loopCode.kernel 4 0 0 1 1 (fun _ => [])) 0 [(7,0),(7,1),(7,4),(7,5)]
  -- The worklist proposes intervals, but a separately proved validator is mandatory.
  let graph := (scheduleStructure earliestProposal loop).assemble #[]
  let artifact := graph.artifact #[⟨0,4294967295⟩,⟨0,4294967295⟩,⟨0,22⟩,⟨0,22⟩,⟨0,4294967295⟩] #[(0,4),(1,4)] #[(0,4),(1,4)]
  check "invariant/missing-entry-rejected" (!(validClockInvariant artifact graph (Array.replicate graph.nodes.size none)))
