import IRComparison.Examples.CertifiedHLSExamples

open IRComparison Circuit Circuit.Pipelining HybridWord CertifiedHLS
set_option maxRecDepth 65536
set_option maxHeartbeats 32000000

-- These two ordinary Lean definitions exercise the real frontend, not an
-- expression-only adapter. An unused failed read must still fail.
def unused (i _x _y : Word) (s : HybridWord.State) : Option HybridWord.State := do
  let _ ← (s.arrays 0)[99]?
  s.write 1 i 7
hls_certified unused as unusedHLS

def conditionalRead (i _x y : Word) (s : HybridWord.State) : Option HybridWord.State :=
  if y != 0 then do
    let v ← (s.arrays 0)[99]?
    s.write 1 i v
  else s.write 1 i 7
hls_certified conditionalRead as conditionalReadHLS

def sizes (a : Nat) := if a < 2 then 1 else 0
def layout : Array (Nat × Nat) := #[(0,1),(1,1)]
def supply (_ : Unit) : List Int := []
def initial : HybridWord.State := ⟨fun _ => 0,fun a => if a = 0 then #[20] else #[0]⟩

def verify {source : List Stage} {entry : Entry source} (out : System.FilePath) (name : String)
    (c : Compiled entry [1] sizes layout 4096) (x y : Word) (expected : Option Int) : IO Lean.Json := do
  unless c.backend.route == "structured" do
    throw (IO.userError s!"{name}: shared route declined: {c.backend.fallbackReason}")
  let native := CertifiedHLS.runSource source x y initial
  unless native.map (fun s => (s.arrays 1)[0]!.toNat) == expected.map Int.toNat do
    throw (IO.userError s!"{name}: source expectation")
  let start : RTL.InterfaceState c.backend.artifact.storageShape :=
    ⟨FiniteRuntime.pack _ (c.backend.initial initial x y),true⟩
  let some result := SystemVerilog.runText c.text c.backend.artifact.storageShape 64 start
    | throw (IO.userError s!"{name}: printed module does not run")
  unless result.core.done && !result.busy && result.core.error == expected.isNone do
    throw (IO.userError s!"{name}: control result")
  if let some v := expected then
    unless (result.core.decode.data.arrays 1)[0]? == some v do
      throw (IO.userError s!"{name}: output result")
  IO.FS.writeFile (out / s!"{name}.sv") c.text
  IO.println s!"PASS {name}: structured/shared, bytes={c.text.utf8ByteSize}"
  return Lean.Json.mkObj [("name",Lean.toJson name),("expected",Lean.toJson expected),
    ("x",Lean.toJson x.toNat),("y",Lean.toJson y.toNat),("bytes",Lean.toJson c.text.utf8ByteSize)]

-- Growth is measured after the frontend, through the actual plan/dispatch/
-- lowering/emitter. Ordinary Lean source coverage above is kept separate.
def chain : Nat → HybridWord.Expr
  | 0 => .left
  | n+1 => .add (chain n) (.lit 1)
def growthCmd (n : Nat) : HybridWord.Cmd := .store 1 .index (chain n)
def growthNative (n : Nat) : Body := fun i x y s => (growthCmd n).eval i x y s []
def growthEntry (n : Nat) : BodyEntry (growthNative n) := ⟨growthCmd n,by intros; rfl⟩
def treeNodes : Circuit.Expr → Nat
  | .memory _ j | .natIndex j | .wrap32 j => 1 + treeNodes j
  | .bin _ a b | .seq a b => 1 + treeNodes a + treeNodes b
  | .select c a b => 1 + treeNodes c + treeNodes a + treeNodes b
  | _ => 1

def main : IO Unit := do
  let out : System.FilePath := "artifacts/shared-normal-hls"
  IO.FS.createDirAll out
  let unused ← IO.ofExcept (unusedHLS.compile 1 0 0 1 1 supply [1] sizes layout 4096)
  let conditional ← IO.ofExcept (conditionalReadHLS.compile 1 0 0 1 1 supply [1] sizes layout 4096)
  let mut cases := #[]
  cases := cases.push (← verify out "unused-invalid" unused 5 0 none)
  cases := cases.push (← verify out "unchosen-invalid" conditional 5 0 (some 7))
  cases := cases.push (← verify out "chosen-invalid" conditional 5 1 none)
  let mut measurements := #[]
  for n in [1,5,8,10,50,100] do
    let code := (chain n).lower
    let t0 ← IO.monoMsNow
    let shared := Shared.compile (.lit 0) (.wire 0) (.wire 1) [] [] code
    let nodes := shared.graph.length
    let t1 ← IO.monoMsNow
    let range := shared.range (fun _ => wordRange)
    let t2 ← IO.monoMsNow
    let refs := shared.reads.length
    let t3 ← IO.monoMsNow
    let c ← IO.ofExcept (CertifiedHLS.compile ((growthEntry n).program 1 0 0 1 1 supply) [1] sizes layout 4096)
    let t4 ← IO.monoMsNow
    cases := cases.push (← verify out s!"growth-{n}" c 5 0 (some (5+n)))
    let old := if n ≤ 10 then some (treeNodes (Circuit.read (.lit 0) (.wire 0) (.wire 1) [] [] code)) else none
    measurements := measurements.push (Lean.Json.mkObj [
      ("additions",Lean.toJson n),("expanded_tree_nodes",Lean.toJson old),
      ("shared_nodes",Lean.toJson nodes),("build_ms",Lean.toJson (t1-t0)),
      ("range_ms",Lean.toJson (t2-t1)),("reference_ms",Lean.toJson (t3-t2)),
      ("external_references",Lean.toJson refs),("range",Lean.toJson [range.lo,range.hi]),
      ("normal_compile_ms",Lean.toJson (t4-t3)),("rtl_bytes",Lean.toJson c.text.utf8ByteSize)])
  IO.FS.writeFile (out / "normal-cases.json") (Lean.toJson cases).pretty
  IO.FS.writeFile (out / "measurements.json") (Lean.Json.mkObj [
    ("cases",Lean.toJson measurements),
    ("note",Lean.toJson "Single-run wall-clock ms, no expanded tree for n>10. Growth begins at BV32 IR; invalid-read tests use ordinary Lean frontend. Normal compile includes plan selection, checking and actual printed RTL.")]).pretty
