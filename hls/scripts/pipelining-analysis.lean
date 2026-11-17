-- Current diagnostic. The pre-correction log is retained in artifacts/pipeline-analysis.
import IRComparison.Examples.CertifiedHLSExamples
import IRComparison.Examples.PipeliningExamples

open IRComparison Circuit Circuit.Pipelining CertifiedHLS CertifiedHLSExamples
set_option maxRecDepth 32768
set_option maxHeartbeats 32000000

def short (s : String) : String := if s.length > 130 then (s.take 130).toString ++ "..." else s

def actionName : Action → String
  | .wire n _ => s!"wire{n}"
  | .assign n _ => s!"reg{n}"
  | .store a _ _ => s!"store{a}"
  | .receive q n => s!"receive{q}->wire{n}"
  | .send q _ => s!"send{q}"
  | .snapshot a b => s!"snapshot{a}<-{b}"
  | .clear q => s!"clear{q}"
  | .erase a => s!"erase{a}"

def describe (indent : String) : ClockTree → List String
  | .block bs => [s!"{indent}block {bs.length} clocks"] ++
      bs.zipIdx.map (fun (actions,i) => s!"{indent}  {i}: {actions.map actionName}")
  | .seq a b => describe indent a ++ describe indent b
  | .branch e a b => [s!"{indent}if {short (reprStr e)}"] ++ describe (indent++"  T ") a ++ describe (indent++"  F ") b
  | .loop e body =>
      let reason := match body with
        | .block bs => match bs.reverse with
          | tail::revPrefix => match revPrefix.reverse with
            | head::_ => s!"straight; boundarySafe={decide (BundleSafe (tail++head))}; guardStable={decide (∀ a ∈ tail, Apart (actionWrites a) (reads e))}"
            | _ => "one/zero batch"
          | _ => "empty"
        | _ => "not a block: structural eligibility fails before dependency checks"
      [s!"{indent}LOOP {short (reprStr e)} [{reason}]"] ++ describe (indent++"  ") body

structure Profile where
  cycles : Nat := 0
  batch : Nat := 0
  branch : Nat := 0
  branchTrue : Nat := 0
  jump : Nat := 0
  halt : Nat := 0
  visits : Array Nat
  deriving Repr

def profile (g : ClockGraph) (r : Circuit.Runtime) (v : Profile) : Nat → Profile × Circuit.Runtime
  | 0 => (v,r)
  | n+1 => if r.done then (v,r) else
      let v := {v with cycles := v.cycles+1, visits := v.visits.modify r.pc (·+1)}
      let v := match g.nodes[r.pc]? with
        | some (.batch ..) => {v with batch := v.batch+1}
        | some (.branch e ..) => {v with branch := v.branch+1, branchTrue := v.branchTrue + (if (e.eval r.data r.wires).any (· != 0) then 1 else 0)}
        | some (.jump ..) => {v with jump := v.jump+1}
        | some .halt => {v with halt := v.halt+1}
        | none => v
      profile g (g.tick r) v n

def measureGraph (g : ClockGraph) (p : Payload) := profile g (p.at 1) {visits := Array.replicate g.nodes.size 0} 100000

def sample (size : Nat) : HybridWord.State :=
  ⟨fun _ => 0,fun a => if a = 0 then (List.range size).toArray.map (fun i => BitVec.ofNat 32 (3*(i+1))) else Array.replicate size 0⟩

def planKind {outputs : List Nat} {sizes : Nat → Nat} {ks : List HybridIR.Kernel} (p : HybridUnifiedPipeline.Plan outputs sizes ks) : String :=
  match p with | .regions => "regions" | .expanded _ => "expanded" | .compact _ => "compact"

def exercise (name : String) (entry : BodyEntry native) (n : Nat) (fifo : Bool) : IO Unit := do
  let size := n+2
  let sizes := fun _ => size
  let layout := #[(0,size),(1,size),(2,size)]
  let supplier := fun _ => if fifo then (List.range size).map Int.ofNat else []
  let source := entry.program size 0 0 1 n supplier
  let compiled ← IO.ofExcept (CertifiedHLS.compile source [1] sizes layout 0)
  let generated := schedule layout (HybridUnifiedPipeline.lower compiled.plan)
  let tree := scheduleStructure earliestProposal generated.schedule
  let optimized := structuredTree generated.schedule
  let p := wordPayload (sample size) 0 0
  let (before,_) := measureGraph (tree.assemble generated.build.queues) p
  let (after,r) := measureGraph (optimized.assemble generated.build.queues) p
  let expected := CertifiedHLS.runSource [entry.stage size 0 0 1 n supplier] 0 0 (sample size)
  unless r.result.map (Option.map (fun s => s.arrays 1)) == some (expected.map (fun s => s.encode.arrays 1)) do
    throw (IO.userError s!"{name}: native mismatch")
  let form := planKind compiled.plan
  IO.println s!"CASE {name} n={n} supplierHint={fifo} plan={form} route={compiled.backend.route} nodes={tree.size+1}->{optimized.size+1} clocks={before.cycles}->{after.cycles} batch={after.batch} branch={after.branch} branchTrue={after.branchTrue} jump={after.jump} halt={after.halt}"
  if n = 8 then
    let expanded ← IO.ofExcept (compileOptimizedScheduled compiled.plan layout 4096)
    IO.println s!"EXPLICIT-STATIC {name}: clocks={expanded.realization.batches.length+1}"
    let g := tree.assemble generated.build.queues
    let details := String.intercalate "\n" (describe "" tree)
    IO.FS.writeFile s!"artifacts/symbolic-memory/analysis/{name}-tree.txt" details
    let visits := String.intercalate "\n" ((List.range g.nodes.size).map fun i =>
      s!"pc={i}, visits={before.visits[i]?.getD 0}: {short (reprStr (g.nodes[i]?))}")
    IO.FS.writeFile s!"artifacts/symbolic-memory/analysis/{name}-visits.txt" visits

def chainExercise (n : Nat) : IO Unit := do
  let size := n+2
  let src := [producerHLS.entry.stage size 0 0 1 n (fun _ => []),
    consumerHLS.entry.stage size 1 0 1 n (fun _ => [])]
  let entry : Entry src := .cons producerHLS.entry (.cons consumerHLS.entry .nil)
  let compiled ← IO.ofExcept (CertifiedHLS.compile entry [2] (fun _ => size) #[(0,size),(1,size),(2,size)] 0)
  let generated := schedule #[(0,size),(1,size),(2,size)] (HybridUnifiedPipeline.lower compiled.plan)
  let tree := scheduleStructure earliestProposal generated.schedule
  let optimized := overlapLoops tree
  let p := wordPayload (sample size) 0 0
  let (a,_) := measureGraph (tree.assemble generated.build.queues) p
  let (b,r) := measureGraph (optimized.assemble generated.build.queues) p
  unless r.result.map (Option.map (fun s => s.arrays 2)) == some ((CertifiedHLS.runSource src 0 0 (sample size)).map (fun s => s.encode.arrays 2)) do
    throw (IO.userError "chain source mismatch")
  let form := planKind compiled.plan
  IO.println s!"CHAIN n={n} plan={form} nodes={tree.size+1}->{optimized.size+1} clocks={a.cycles}->{b.cycles}"
  if n = 8 then IO.FS.writeFile "artifacts/symbolic-memory/analysis/chain-tree.txt" (String.intercalate "\n" (describe "" tree))

-- Three-stage data path with ordinary state reuse. This isolates whether
-- boundary-only overlap is sufficient, independently of lowering details.
def pathBody : List Action :=
  [.wire 3 (.wire 2),
   .wire 4 (.memory 0 (.wire 2)),
   .wire 2 (.bin .add (.wire 2) (.lit 1)),
   .wire 5 (.bin .add (.wire 4) (.lit 7)),
   .store 1 (.wire 3) (.wire 5)]

def toSchedule : List Action → Circuit.Schedule
  | [] => .skip
  | a::actions => .seq (.step a) (toSchedule actions)

def pathLoop : Circuit.Schedule := .loop (.bin .lt (.wire 2) (.wire 1)) (toSchedule pathBody)

def main : IO Unit := do
  IO.FS.createDirAll "artifacts/symbolic-memory/analysis"
  for n in [0,1,3,8,32] do
    exercise "filter-memory" filterHLS.entry n false
    exercise "filter-supplier-hint" filterHLS.entry n true
    exercise "map-memory" producerHLS.entry n false
  for n in [3,8,32] do chainExercise n
  let before := scheduleStructure earliestProposal pathLoop
  IO.FS.writeFile "artifacts/symbolic-memory/analysis/three-stage-tree.txt" (String.intercalate "\n" (describe "" before))
  for n in [3,8,32] do
    let p := wordPayload (sample n) 0 (BitVec.ofNat 32 n)
    let (a,ra) := measureGraph (before.assemble #[]) p
    let (b,rb) := measureGraph ((overlapLoops before).assemble #[]) p
    unless ra.done && rb.done && !ra.error && !rb.error && ra.data.arrays 1 == rb.data.arrays 1 do
      throw (IO.userError "rolled path mismatch")
    IO.println s!"PATH n={n} bodyClocks=3 baseline={a.cycles} boundary={b.cycles}"

  -- Explicit finite instantiation is used ONLY as a feasibility experiment.
  -- This is not a new rolled multi-stage compiler or a proof of its lowering.
  let probe : Loop := ⟨8,3,fun i k => match k with
    | 0 => .wire (2*i+2) (.memory 0 (.lit i))
    | 1 => .wire (2*i+3) (.bin .add (.wire (2*i+2)) (.lit 7))
    | _ => .store 1 (.lit i) (.wire (2*i+3))⟩
  let scheduled := probe.pipeline 1
  unless scheduled.accepted do throw (IO.userError "three-stage probe rejected")
  let p := wordPayload (sample 8) 0 8
  let output := runCycles (fun _ => 0) probe.code scheduled.cycles p
  unless output.map (fun s => s.data.arrays 1) == some #[10,13,16,19,22,25,28,31] do
    throw (IO.userError "three-stage probe output mismatch")
  IO.println s!"THREE-STAGE-FEASIBILITY II=1 accepted={scheduled.accepted} activeClocks={scheduled.cycles.length} (excludes rolled control)"
  for ii in [1,2,3] do
    IO.println s!"RECURRENCE II={ii} accepted={((PipeliningExamples.recurrence 8).pipeline ii).accepted}"
