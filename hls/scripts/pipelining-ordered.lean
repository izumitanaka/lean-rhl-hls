import IRComparison.Circuit.Pipelining.Optimized

open IRComparison IRComparison.Circuit IRComparison.Circuit.Pipelining
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def check (name : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"FAIL {name}")
  IO.println s!"PASS\t{name}"

def sample : Payload := ⟨⟨fun n => if n = 0 then 10 else 20,
  fun n => if n = 0 then #[10,20,30] else #[0,0,0]⟩,
  fun n => if n = 2 then 10 else 20,
  fun n => if n = 1 then [30,40] else []⟩

def visible (p : Payload) := ((List.range 6).map p.data.regs,
  (List.range 6).map p.wires, (List.range 4).map p.data.arrays,
  (List.range 4).map p.queues)

def bundleCheck (name : String) (as : List Action) (p : Payload := sample)
    (capacity : Nat := 4) : IO Unit := do
  check (name ++ "/new-rule") (decide (BundleSafe as))
  check (name ++ "/old-rule-rejects") (!(decide (as.Pairwise Independent)))
  let plan := compile as.toArray [(List.range as.length)]
  check (name ++ "/compiler-accepts") plan.accepted
  check (name ++ "/preserves-result-or-failure")
    ((runCycles (fun _ => capacity) as.toArray plan.cycles p).map visible ==
     (evalList (Action.eval (fun _ => capacity)) as p).map visible)

/-- Previous heuristic, kept only as a comparison baseline in this test. -/
def strictProposal (code : Array Action) : Cycles := Id.run do
  let mut times : List (Nat × Nat) := []
  for i in List.range code.size do
    let t := times.foldl (fun n (j,t) =>
      if independent (actionAt code j) (actionAt code i) then n else max n (t+1)) 0
    times := times ++ [(i,t)]
  return groupTimes times

def add32 (a b : Circuit.Expr) : Circuit.Expr :=
  let sum := Circuit.Expr.bin .add a b
  .bin .sub sum (.bin .mul (.bin .div sum (.lit 4294967296)) (.lit 4294967296))

/-- Existing Action syntax for a sliding window, with explicit initialization
and no final over-read. Used to isolate the new general scheduling rule;
the integrated regression separately exercises automatically inserted buffers. -/
def window (depth count : Nat) : Array Action :=
  let init := (List.range depth).map (fun j => Action.wire (j+2) (.memory 0 (.lit j)))
  let body := (List.range count).flatMap fun i =>
    let sum := ((List.range depth).map (fun j => Circuit.Expr.wire (j+2))).foldl add32 (.lit 0)
    let value := if depth = 2 then Circuit.Expr.bin .div sum (.lit 2) else sum
    [.store 1 (.lit i) value] ++
      (if i+1 < count then
        (List.range (depth-1)).map (fun j => Action.wire (j+2) (.wire (j+3))) ++
        [.wire (depth+1) (.memory 0 (.lit (i+depth)))]
       else [])
  (init ++ body).toArray

def windowCheck (name : String) (depth : Nat) (input : Array HybridWord.Word)
    (expected : Option (Array Int)) (emit : Bool := true) : IO Unit := do
  let code := window depth 4
  let plan := compile code (earliestProposal code)
  let old := compile code (strictProposal code)
  check (name ++ "/candidate") plan.accepted
  check (name ++ "/improved") (plan.cycles.length < old.cycles.length)
  let s : HybridWord.State := ⟨fun _ => 0, fun n => if n = 0 then input else if n = 1 then #[0,0,0,0] else #[]⟩
  let p := wordPayload s 0 0
  let result := runCycles (fun _ => 0) code plan.cycles p
  check (name ++ "/expected") (result.map (fun p => p.data.arrays 1) == expected)
  check (name ++ "/source") (result.map visible == (sourceEval (fun _ => 0) code p).map visible)
  let r := realize code plan.cycles (Array.replicate (depth+2) wordRange)
  let layout := #[(0,input.size),(1,4)]
  let a := declarationArtifact r.batches r.widths layout layout #[]
  let generated ← IO.ofExcept (generateBatchModule a r.batches [1])
  let rtl := (batchProgram r.batches #[]).run a.storageShape.wireRange
    (r.batches.length+1) (p.at 0)
  check (name ++ "/rtl") (rtl.result.map (Option.map (fun s => s.arrays 1)) == some expected)
  if emit then IO.FS.writeFile s!"artifacts/pipelining/ordered/{name}.sv" generated.text
  IO.println s!"ORDERED\t{name}\tactions={code.size}\told-clocks={old.cycles.length}\tnew-clocks={plan.cycles.length}\trtl-clocks={r.batches.length+1}"

def main : IO Unit := do
  IO.FS.createDirAll "artifacts/pipelining/ordered"
  bundleCheck "scalar-WAR" [.assign 0 (.reg 1), .assign 1 (.lit 30)]
  bundleCheck "holding-WAR" [.wire 2 (.wire 3), .wire 3 (.lit 30)]
  bundleCheck "array-read-then-store" [.wire 2 (.memory 0 (.lit 1)), .store 0 (.lit 1) (.lit 99)]
  bundleCheck "snapshot-then-erase" [.snapshot 1 0, .erase 0]
  bundleCheck "send-then-receive-other-queue" [.send 0 (.wire 2), .receive 1 2]
  bundleCheck "failed-read-before-erase" [.wire 2 (.memory 0 (.lit 99)), .erase 0]
  bundleCheck "full-fifo-failure" [.send 0 (.wire 2), .wire 2 (.lit 99)] sample 0
  bundleCheck "empty-fifo-failure" [.assign 0 (.wire 2), .receive 0 2]
  let war : Array Action := #[.assign 0 (.reg 1), .assign 1 (.lit 30)]
  check "WAR/reverse-clock-order-rejected" (!(compile war [[1],[0]]).accepted)
  check "WAR/reverse-bundle-order-rejected" (!(compile war [[1,0]]).accepted)
  let raw : Array Action := #[.assign 0 (.lit 30), .assign 1 (.reg 0)]
  check "RAW/same-clock-rejected" (!(compile raw [[0,1]]).accepted)
  check "RAW/incorrect-candidate-differs"
    ((runCycles (fun _ => 0) raw [[0,1]] sample).map visible != (sourceEval (fun _ => 0) raw sample).map visible)
  check "WAW/rejected" (!(compile #[Action.assign 0 (.lit 1), .assign 0 (.lit 2)] [[0,1]]).accepted)
  check "same-FIFO/rejected" (!(compile #[Action.send 0 (.lit 1), .receive 0 2] [[0,1]]).accepted)
  windowCheck "window2" 2 #[10,20,30,40,50] (some #[15,25,35,45])
  windowCheck "window3" 3 #[10,20,30,40,50,60] (some #[60,90,120,150])
  windowCheck "window2-wrap" 2 #[4294967295,1,4294967295,1,4294967295] (some #[0,0,0,0])
  windowCheck "window3-wrap" 3 #[4294967295,1,4294967295,1,4294967295,1]
    (some #[4294967295,1,4294967295,1])
  windowCheck "window2-oob" 2 #[10,20,30,40] none
