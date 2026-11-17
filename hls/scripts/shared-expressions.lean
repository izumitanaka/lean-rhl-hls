import IRComparison.Circuit.SharedAnalysis

open IRComparison Circuit
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

def chain : Nat → HybridWord.Expr
  | 0 => .left
  | n+1 => .add (chain n) (.lit 1)

def treeNodes : Circuit.Expr → Nat
  | .memory _ j | .natIndex j | .wrap32 j => 1 + treeNodes j
  | .bin _ a b | .seq a b => 1 + treeNodes a + treeNodes b
  | .select c a b => 1 + treeNodes c + treeNodes a + treeNodes b
  | _ => 1

def state : State := ⟨fun _ => 7,fun _ => #[10,20,30]⟩
def wires (_ : Nat) : Int := 5

def check (name : String) (code : HybridIR.ReadCode) (expected : Option Int) : IO Unit := do
  let p := Shared.compile (.lit 0) (.wire 0) (.wire 1) [] [] code
  let actual := p.eval state wires
  unless actual == expected && actual == code.eval 0 5 5 state [] [] do
    throw (IO.userError s!"{name}: changed partial-read semantics: {actual}")
  IO.println s!"PASS {name}: {actual}, nodes={p.graph.length}"

def main : IO Unit := do
  IO.FS.createDirAll "artifacts/shared-expressions"
  let mut records : Array Lean.Json := #[]
  for n in [0,1,5,8,10,100,1000] do
    let code := (chain n).lower
    let started ← IO.monoMsNow
    let p := Shared.compile (.lit 0) (.wire 0) (.wire 1) [] [] code
    let count := p.graph.length
    let lowered ← IO.monoMsNow
    let result := p.eval state wires
    let evaluated ← IO.monoMsNow
    let r := p.range (fun _ => Circuit.wordRange)
    let ranged ← IO.monoMsNow
    let refs := p.reads
    let referenced ← IO.monoMsNow
    unless refs.length == 2 do
      throw (IO.userError s!"chain {n}: duplicated external dependencies")
    unless result == some (5+(n:Int)) && count == 3+5*n do
      throw (IO.userError s!"chain {n}: {result}, nodes={count}")
    let old := if n ≤ 10 then some (treeNodes (Circuit.read (.lit 0) (.wire 0) (.wire 1) [] [] code)) else none
    IO.println s!"chain {n}: shared={count}, expanded={old}, build={lowered-started}ms eval={evaluated-lowered}ms range={ranged-evaluated}ms"
    records := records.push (Lean.Json.mkObj [
      ("additions",Lean.toJson n),("shared_nodes",Lean.toJson count),("expanded_tree_nodes",Lean.toJson old),
      ("build_ms",Lean.toJson (lowered-started)),("eval_ms",Lean.toJson (evaluated-lowered)),
      ("range_ms",Lean.toJson (ranged-evaluated)),
      ("reference_ms",Lean.toJson (referenced-ranged)),("external_references",Lean.toJson refs.length),("range",Lean.toJson [r.lo,r.hi])])
  check "unused-invalid-read" (.bind (.memory 0 (.lit 99)) (.pure (.lit 7))) none
  check "unchosen-invalid-read" (.branch (.lit 0) (.memory 0 (.lit 99)) (.pure (.lit 7))) (some 7)
  check "chosen-invalid-read" (.branch (.lit 1) (.memory 0 (.lit 99)) (.pure (.lit 7))) none
  check "missing-binding" (.pure (.temp 99)) none
  check "reused-binding" (.bind (.memory 0 (.lit 1)) (.pure (.add (.temp 0) (.temp 0)))) (some 40)
  check "nested-shadowing" (.bind (.pure (.lit 3)) (.bind (.pure (.lit 5))
    (.pure (.sub (.temp 1) (.temp 0))))) (some (-2))
  let reused := Shared.compile (.lit 0) (.wire 0) (.wire 1) [] []
    (.bind (.memory 0 (.lit 1)) (.pure (.add (.temp 0) (.temp 0))))
  unless (reused.graph.filter (fun n => match n with | .memory .. => true | _ => false)).length == 1 do
    throw (IO.userError "binding duplicated its memory node")
  IO.FS.writeFile "artifacts/shared-expressions/measurements.json" (Lean.Json.mkObj
    [("cases",Lean.toJson records),("timing_note",Lean.toJson "Single-run wall-clock ms; 0ms is below clock resolution, not zero cost. Native Lean evaluation; no expanded tree for n>10."),
     ("rtl_size",.null),("integration",Lean.toJson "This measurement covers expression lowering/range analysis only. See shared-normal-hls.lean for the normal structured HLS/RTL route.")]).pretty
