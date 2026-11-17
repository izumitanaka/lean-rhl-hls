import IRComparison.Circuit.SharedEmitConnection

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
def runtime : Runtime := ⟨0,state,wires,fun _ => [],false,false⟩
-- The artifact must declare register 0 as well as the memory and holding nets.
-- Its control path is not executed in these combinational-expression tests.
def layout : Artifact := ⟨⟨0,#[.assign 0 (.lit 7) 1,.halt],#[]⟩,#[wordRange,wordRange],#[(0,3)],#[(0,3)]⟩

def emit (p : Shared.LocalRTL.Program) : IO Shared.NetEmission.Output :=
  match Shared.NetEmission.generate layout p with
  | .ok output => pure output
  | .error e => throw (IO.userError e)

def writeSV (out : System.FilePath) (name : String) (o : Shared.NetEmission.Output) (expected : Option Int) : IO Unit := do
  let check := match expected with
    | none => s!"if ({o.result.valid.name.text} !== 2'sd0) $fatal(1, \"expected invalid\");"
    | some v =>
      let literal := (SystemVerilog.Expr.literal o.result.value.width v o.result.value.positive).text
      s!"if ({o.result.valid.name.text} !== 2'sd1 || $signed({o.result.value.name.text}) !== {literal}) $fatal(1, \"wrong shared result\");"
  let header := "module shared_test;\nlogic signed [32:0] w0, w1;\nlogic [31:0] r0;\nlogic [31:0] m0 [0:2];\nwire [31:0] len0 = 32'd3;\n"
  let init := "\ninitial begin\nw0 = 33'sd5; w1 = 33'sd5; r0 = 32'd7;\nm0[0] = 32'd10; m0[1] = 32'd20; m0[2] = 32'd30;\n#1;\n"
  IO.FS.writeFile (out / "rtl" / s!"{name}.sv")
    (header ++ o.text ++ init ++ check ++ s!"\n$display(\"PASS {name}\"); $finish;\nend\nendmodule\n")

  let synthHeader := s!"module shared_synth(input wire signed [32:0] w0, w1, input wire [31:0] r0, output wire signed [{o.result.value.width-1}:0] result, output wire valid);\n"
  let mem := "wire [31:0] m0 [0:2];\nassign m0[0]=32'd10; assign m0[1]=32'd20; assign m0[2]=32'd30;\nwire [31:0] len0=32'd3;\n"
  IO.FS.writeFile (out / "rtl" / s!"{name}.design.sv")
    (synthHeader ++ mem ++ o.text ++ s!"\nassign result = {o.result.value.name.text};\nassign valid = ({o.result.valid.name.text} != 0);\nendmodule\n")

/-- Check the actual serialized declaration fragment, not only RTL.Term.eval. -/
def checkText (output : Shared.NetEmission.Output) (expected : Option Int) : IO Unit := do
  let finite := FiniteRuntime.pack layout.storageShape runtime
  let some values := Shared.NetEmission.evaluateText layout finite output.text
    | throw (IO.userError "shared declaration text failed to parse/evaluate")
  let direct := SystemVerilog.evaluateWires layout finite output.declarations
  unless direct == some values do
    throw (IO.userError "serialized and direct netlist evaluation differ")
  let env := (SystemVerilog.environment layout finite output.declarations #[]).withTemporaries values
  unless output.result.observe env == expected do
    throw (IO.userError s!"shared text observation differs: {output.result.observe env}, expected {expected}")

def check (out : System.FilePath) (name : String) (code : HybridIR.ReadCode) (expected : Option Int) : IO Unit := do
  let p := Shared.compile (.lit 0) (.wire 0) (.wire 1) [] [] code
  let rtl := Shared.LocalRTL.compile (fun _ => wordRange) p
  let actual := p.eval state wires
  unless actual == expected && actual == code.eval 0 5 5 state [] [] &&
      actual == p.bitEval (fun _ => wordRange) state wires && actual == rtl.eval runtime && actual == rtl.fullEval runtime do
    throw (IO.userError s!"{name}: changed evaluation: {actual}")
  let output ← emit rtl
  checkText output expected
  writeSV out name output expected
  IO.println s!"PASS {name}: {actual}, graph={p.graph.length}, rtl={rtl.code.length}, nets={output.declarations.size}"

def main (args : List String) : IO Unit := do
  let out : System.FilePath := args.headD "artifacts/shared-erasure"
  IO.FS.createDirAll (out / "rtl")
  let mut records : Array Lean.Json := #[]
  for n in [0,1,5,8,10,100,1000] do
    let code := (chain n).lower
    let started ← IO.monoMsNow
    let p := Shared.compile (.lit 0) (.wire 0) (.wire 1) [] [] code
    let lowered ← IO.monoMsNow
    let result := p.eval state wires
    let evaluated ← IO.monoMsNow
    let range := p.range (fun _ => wordRange)
    let ranged ← IO.monoMsNow
    let refs := p.reads
    let referenced ← IO.monoMsNow
    let bit := p.bitEval (fun _ => wordRange) state wires
    let bitDone ← IO.monoMsNow
    let rtl := Shared.LocalRTL.compile (fun _ => wordRange) p
    let rtlDone ← IO.monoMsNow
    let rtlResult := rtl.eval runtime
    let rtlEvalDone ← IO.monoMsNow
    let output ← emit rtl
    let emitted ← IO.monoMsNow
    let text := output.text
    let serialized ← IO.monoMsNow
    checkText output result
    let textChecked ← IO.monoMsNow
    unless result == some (5+(n:Int)) && bit == result && rtlResult == result && rtl.fullEval runtime == result &&
        p.graph.length == 3+5*n && rtl.code.length == p.graph.length && refs.length == 2 do
      throw (IO.userError s!"chain {n}: incorrect result or sharing")
    let old := if n ≤ 10 then some (treeNodes (Circuit.read (.lit 0) (.wire 0) (.wire 1) [] [] code)) else none
    writeSV out s!"chain{n}" output result
    records := records.push (Lean.Json.mkObj [
      ("additions",Lean.toJson n),("shared_nodes",Lean.toJson p.graph.length),("expanded_tree_nodes",Lean.toJson old),
      ("rtl_nodes",Lean.toJson rtl.code.length),("nets",Lean.toJson output.declarations.size),
      ("rtl_bytes",Lean.toJson text.utf8ByteSize),
      ("build_ms",Lean.toJson (lowered-started)),("eval_ms",Lean.toJson (evaluated-lowered)),
      ("range_ms",Lean.toJson (ranged-evaluated)),("reference_ms",Lean.toJson (referenced-ranged)),
      ("bit_eval_ms",Lean.toJson (bitDone-referenced)),("rtl_lower_ms",Lean.toJson (rtlDone-bitDone)),
      ("rtl_eval_ms",Lean.toJson (rtlEvalDone-rtlDone)),("emit_ms",Lean.toJson (emitted-rtlEvalDone)),
      ("serialize_ms",Lean.toJson (serialized-emitted)),("text_check_ms",Lean.toJson (textChecked-serialized)),("range",Lean.toJson [range.lo,range.hi])])
    IO.println s!"chain {n}: shared={p.graph.length}, expanded={old}, build={lowered-started}ms, nets={output.declarations.size}, SV={text.utf8ByteSize}bytes"
  check out "unused-invalid-read" (.bind (.memory 0 (.lit 99)) (.pure (.lit 7))) none
  check out "unchosen-invalid-read" (.branch (.lit 0) (.memory 0 (.lit 99)) (.pure (.lit 7))) (some 7)
  check out "chosen-invalid-read" (.branch (.lit 1) (.memory 0 (.lit 99)) (.pure (.lit 7))) none
  check out "unchosen-unused-invalid" (.branch (.lit 0)
    (.bind (.memory 0 (.lit 99)) (.pure (.lit 7))) (.pure (.lit 11))) (some 11)
  check out "chosen-unused-invalid" (.branch (.lit 1)
    (.bind (.memory 0 (.lit 99)) (.pure (.lit 7))) (.pure (.lit 11))) none
  check out "invalid-before-choice" (.bind (.memory 0 (.lit 99))
    (.branch (.lit 0) (.pure (.temp 0)) (.pure (.lit 7)))) none
  check out "missing-binding" (.pure (.temp 99)) none
  check out "reused-binding" (.bind (.memory 0 (.lit 1)) (.pure (.add (.temp 0) (.temp 0)))) (some 40)
  check out "nested-shadowing" (.bind (.pure (.lit 3)) (.bind (.pure (.lit 5))
    (.pure (.sub (.temp 1) (.temp 0))))) (some (-2))
  check out "register" (.register 0) (some 7)
  check out "wrap-negative" (.pure (.wrap32 (.lit (-1)))) (some 4294967295)
  check out "wrap-overflow" (.pure (.wrap32 (.add (.lit 4294967295) (.lit 1)))) (some 0)
  check out "wrap-product" (.pure (.wrap32 (.mul (.lit 4294967295) (.lit 4294967295)))) (some 1)
  check out "div-negative" (.pure (.div (.lit (-7)) (.lit 3))) (some (-3))
  check out "div-negative-denominator" (.pure (.div (.lit (-7)) (.lit (-3)))) (some 3)
  check out "div-zero" (.pure (.div (.lit 7) (.lit 0))) (some 0)
  check out "index-negative" (.memory 0 (.lit (-1))) none
  check out "index-last" (.memory 0 (.lit 2)) (some 30)
  check out "index-outside" (.memory 0 (.lit 3)) none
  check out "nat-index" (.memory 0 (.natIndex (.lit (-1)))) (some 10)
  IO.FS.writeFile (out / "measurements.json") (Lean.Json.mkObj [
    ("cases",Lean.toJson records),
    ("note",Lean.toJson "Single-run timings in ms. Old tree node counting only for n<=10; generated C checked separately for absence of old read/value construction. Standalone net emitter, NOT default HLS integration; general emission/text interpretation and evaluation-success theorems are kernel checked separately.")]).pretty
