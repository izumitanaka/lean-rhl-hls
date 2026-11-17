import IRComparison.Examples.PipeliningExamples

open IRComparison IRComparison.Circuit IRComparison.Circuit.Pipelining
open IRComparison.PipeliningExamples

def check (label : String) (condition : Bool) : IO Unit := do
  if !condition then throw (IO.userError s!"FAIL {label}")
  IO.println s!"PASS\t{label}"

def view (p : Option Payload) (regs wires arrays queues : Nat := 8) :=
  p.map fun s => ((List.range regs).map s.data.regs, (List.range wires).map s.wires,
    (List.range arrays).map s.data.arrays, (List.range queues).map s.queues)

def loopCheck (label : String) (l : Loop) (ii : Nat) (expected : Bool)
    (p : Payload := emptyPayload) (cap : Nat → Nat := fun _ => 16) : IO Unit := do
  let plan := l.pipeline ii
  check (label ++ "/selection") (plan.accepted == expected)
  check (label ++ "/result")
    (view (runCycles cap l.code plan.cycles p) 8 (l.count*l.stages+2) ==
      view (l.eval cap p) 8 (l.count*l.stages+2))
  IO.println s!"SCHEDULE\t{label}\tactions={l.code.size}\tclocks={plan.cycles.length}\t{repr plan.cycles}"

def filterCheck (label : String) (input : Array HybridWord.Word) (expected : Option (Array Int))
    (n ii : Nat) (start : Int := 0) (stride : Int := 1) : IO Unit := do
  let s := initial input n
  let (t,_) := filterPipeline n ii start stride
  match t with
  | .original _ => throw (IO.userError s!"{label}: expected accepted clock schedule")
  | .scheduled code plan =>
      check (label ++ "/accepted") plan.accepted
      let p := wordPayload s 0 0
      let out := runCycles (fun _ => 0) code plan.cycles p
      check (label ++ "/independent-expected") (out.map (fun p => p.data.arrays 1) == expected)
      check (label ++ "/native")
        (out.map (fun p => p.data.arrays 1) == ((filterKernel n start stride).source 0 0 s).map (fun s => s.encode.arrays 1))
      check (label ++ "/clock-machine")
        ((t.execute #[] plan.cycles.length p).map (fun r => r.map (fun s => s.arrays 1)) == some expected)
      IO.println s!"SCHEDULE\t{label}\tactions={code.size}\tclocks={plan.cycles.length}\t{repr plan.cycles}"

def main : IO Unit := do
  filterCheck "lean-filter" #[10,20,30,40,50] (some #[15,25,35,45]) 4 1
  filterCheck "lean-filter-II2" #[10,20,30,40,50] (some #[15,25,35,45]) 4 2
  filterCheck "lean-filter-reverse" #[10,20,30,40,50] (some #[15,25,35,45]) 4 1 3 (-1)
  filterCheck "lean-filter-overflow" #[4294967295,1,4294967295,1,4294967295] (some #[0,0,0,0]) 4 1
  filterCheck "lean-filter-out-of-bounds" #[10,20,30,40] none 4 1
  filterCheck "lean-filter-empty" #[] (some #[]) 0 1
  let gatherState : HybridWord.State := ⟨fun _ => 0, fun a => match a with
    | 0 => #[2,0,3,1] | 1 => #[10,20,30,40] | 2 => #[0,0,0,0] | _ => #[]⟩
  let gatherKernel := gatherCode.kernel 4 0 0 1 4 (fun _ => [])
  let gatherTarget := (pipelineWord gatherKernel {} 1).1
  check "lean-gather/accepted" (match gatherTarget with | .scheduled _ plan => plan.accepted | _ => false)
  check "lean-gather/expected"
    ((gatherTarget.execute #[] 6 (wordPayload gatherState 0 0)).map (fun r => r.map (fun s => s.arrays 2)) ==
      some (some #[31,11,41,21]))
  loopCheck "wave-3" (wave 4 3) 1 true
  loopCheck "wave-5" (wave 7 5) 1 true
  loopCheck "wave-II2" (wave 4 3) 2 true
  loopCheck "wave-II0-normalized" (wave 4 3) 0 true
  loopCheck "wave-empty" (wave 0 3) 1 true
  loopCheck "wave-no-stages" (wave 4 0) 1 true
  loopCheck "recurrence-II1-fallback" (recurrence 4) 1 false
  loopCheck "recurrence-II3" (recurrence 4) 3 true
  let q : Payload := { emptyPayload with queues := fun n => if n = 0 then [10,20,30,40] else [] }
  loopCheck "fifo" (fifoLoop 4) 1 true q
  check "fifo/independent-expected"
    ((runCycles (fun _ => 16) (fifoLoop 4).code ((fifoLoop 4).pipeline 1).cycles q).map (fun p => (p.queues 0,p.queues 1)) ==
      some ([],[11,21,31,41]))
  loopCheck "fifo-underflow" (fifoLoop 5) 1 true q
  loopCheck "fifo-overflow" (fifoLoop 4) 1 true q (fun _ => 2)
  check "fifo-underflow/expected" (runCycles (fun _ => 16) (fifoLoop 5).code ((fifoLoop 5).pipeline 1).cycles q).isNone
  check "fifo-overflow/expected" (runCycles (fun _ => 2) (fifoLoop 4).code ((fifoLoop 4).pipeline 1).cycles q).isNone
  let code := (wave 1 2).code
  for (name,candidate) in [
      ("same-clock-RAW",[[0,1]]),("reverse-RAW",[[1],[0]]),
      ("duplicate",[[0],[0],[1]]),("omitted",[[0]]),("invalid-ID",[[0],[1],[99]])] do
    let plan := compile code candidate
    check (name ++ "/rejected") (!plan.accepted)
    check (name ++ "/fallback") (plan.cycles == sequential code)
  let a : Action := .assign 0 (.lit 7)
  let b : Action := .assign 0 (.lit 8)
  check "WAW" (!independent a b)
  check "WAR" (!independent (.wire 3 (.reg 0)) a)
  check "whole-array-conservative"
    (!independent (.store 0 (.lit 0) (.lit 7)) (.wire 0 (.memory 0 (.lit 1))))
  let selects : Array Action := #[.assign 0 (.select (.lit 0) .fail (.lit 7)),.wire 2 (.lit 9)]
  let selection := compile selects [[0,1]]
  check "select/short-circuit" selection.accepted
  check "select/unselected-failure-not-evaluated"
    ((runCycles (fun _ => 0) selects selection.cycles emptyPayload).map (fun p => p.data.regs 0) == some 7)
  let mustFail : Array Action := #[.wire 2 (.seq .fail (.lit 7)),.assign 0 (.lit 9)]
  check "seq/unused-failure-preserved"
    (runCycles (fun _ => 0) mustFail (compile mustFail [[0,1]]).cycles emptyPayload).isNone
  let guarded : Circuit.Schedule := .branch (.reg 0) (.step a) (.step b)
  let t := transform guarded (fun _ => [])
  check "dynamic-control-retained" (match t with | .original _ => true | _ => false)
  check "dynamic-control-executes"
    ((t.execute #[] 8 emptyPayload).map (fun r => r.map (fun s => s.regs 0)) == some (some 8))
  -- Vary stage count/trip count/II, including idle drain cycles. No fixed
  -- three-stage circuit is hidden in the implementation or its proof.
  for count in List.range 7 do
    for depth in List.range 7 do
      for ii in [1,2,4] do
        let l := wave count depth
        let plan := l.pipeline ii
        unless plan.accepted do throw (IO.userError s!"wave rejected {count}/{depth}/{ii}")
        unless view (runCycles (fun _ => 0) l.code plan.cycles emptyPayload) 1 (count*depth+1) ==
          view (l.eval (fun _ => 0) emptyPayload) 1 (count*depth+1) do
            throw (IO.userError s!"wave mismatch {count}/{depth}/{ii}")
  IO.println "PASS\t147 generic wave configurations"

