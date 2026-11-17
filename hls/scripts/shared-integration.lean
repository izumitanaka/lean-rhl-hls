import IRComparison.Circuit.SharedStatementSound

open IRComparison Circuit
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

abbrev E := Sum RTL.Combinational Shared.Prepared

def layout : Artifact :=
  ⟨⟨1,#[.halt,.wire 2 (.memory 0 (.lit 0)) 2,.send 0 (.wire 2) 3,
    .receive 0 3 4,.store 1 (.lit 0) (.wire 3) 5,.halt],#[(0,2)]⟩,
    #[wordRange,wordRange,wordRange,wordRange],#[(0,1),(1,1)],#[(0,1),(1,1)]⟩

def ordinary (e : Circuit.Expr) : E := .inl (RTL.combinational layout.storageShape.wireRange e)
def shared (code : HybridIR.ReadCode) (left : Circuit.Expr := .wire 0) : E :=
  .inr (Shared.prepare layout.storageShape.wireRange (Shared.compile (.lit 0) left (.wire 1) [] [] code))
def advance (n : Nat) : RTL.Statement E := .assign .pc (.literal n)
def fault : RTL.Statement E := .seq (.assign .done (.literal 1)) (.assign .error (.literal 1))
def guardedCase (g : RTL.Test E) (s : RTL.Statement E) : RTL.Statement E := .branch g s fault

def cases (read : HybridIR.ReadCode) : List (RTL.Statement E) :=
  let e := shared read
  let next := shared (.pure (.wrap32 (.add .left (.lit 1)))) (.wire 2)
  let index := ordinary (.lit 0)
  let value := ordinary (.wire 3)
  [.assign .done (.literal 1),
   guardedCase (.valid e) (.seq (.assign (.wire 2) (.value e)) (advance 2)),
   guardedCase (.and (.valid next) (.room 0)) (.seq (.queue 0 (.append 0 next)) (advance 3)),
   guardedCase (.nonempty 0) (.seq (.assign (.wire 3) (.queueHead 0)) (.seq (.queue 0 (.tail 0)) (advance 4))),
   guardedCase (.and (.address 1 index) (.valid value)) (.seq (.memory 1 (.set 1 index value)) (advance 5)),
   .assign .done (.literal 1)]

/-- Exercise the all-shared statement route covered by shared_module_text_tick.
Ordinary leaf expressions become a single source graph node, without expansion. -/
def asShared : E → Shared.Prepared
  | .inl e => ⟨⟨[.source e],0⟩,e.bounds⟩
  | .inr e => e

def state (input : Int) : State := ⟨fun _ => 0,fun id => if id = 0 then #[input] else #[0]⟩
def runtime (input flag : Int) : Runtime :=
  ⟨1,state input,fun n => if n = 0 then flag else if n = 1 then 7 else 0,fun _ => [],false,false⟩

def checkModule (out : System.FilePath) (name : String) (code : HybridIR.ReadCode) (input flag : Int) (allShared : Bool := false) : IO Lean.Json := do
  let source := code.eval 0 flag 7 (state input) [] []
  let expected := source.map (fun v => (v+1) % 4294967296)
  let produced := if allShared then
    Shared.NetEmission.generateModule layout [1] ((cases code).map (fun s => s.mapExpressions asShared))
    else Shared.NetEmission.generateModule layout [1] (cases code)
  let .ok generated := produced
    | throw (IO.userError s!"{name}: module generation failed")
  let text := generated.text
  let some parsed := SystemVerilog.Concrete.parseModule text
    | throw (IO.userError s!"{name}: module parse failed")
  let initial : RTL.InterfaceState layout.storageShape := ⟨FiniteRuntime.pack layout.storageShape (runtime input flag),true⟩
  let some result := parsed.run layout.storageShape 8 initial
    | throw (IO.userError s!"{name}: module evaluation failed")
  unless result.core.done && !result.busy && result.core.error == expected.isNone do
    throw (IO.userError s!"{name}: wrong module control outcome")
  if let some v := expected then
    unless (result.core.decode.data.arrays 1)[0]? == some v do
      throw (IO.userError s!"{name}: wrong memory output")
    unless result.core.decode.queues 0 == [] do
      throw (IO.userError s!"{name}: FIFO did not consume exactly once")
  IO.FS.writeFile (out / s!"{name}.sv") text
  IO.println s!"PASS module {name}: result={expected}, wires={generated.wires.size}, bytes={text.utf8ByteSize}"
  return Lean.Json.mkObj [("name",Lean.toJson name),("input",Lean.toJson input),("flag",Lean.toJson flag),
    ("expected",Lean.toJson expected),("wires",Lean.toJson generated.wires.size),("bytes",Lean.toJson text.utf8ByteSize)]

/-- Interleave old cache entries and graph nets, then hit the old cache again.
This specifically detects allocating a fresh name from cache.size. -/
def checkInterleave : IO Unit := do
  let p := Shared.LocalRTL.compile layout.storageShape.wireRange
    (Shared.compile (.lit 0) (.wire 0) (.wire 1) [] []
      (.bind (.memory 0 (.lit 0)) (.pure (.wrap32 (.add (.temp 0) (.temp 0))))))
  let action : EmitM (Signal × Shared.NetEmission.Pair × Signal × Signal) := do
    let first ← termText layout (.literal 13)
    let graph ← Shared.NetEmission.intoPair layout p
    let hit ← termText layout (.literal 13)
    let last ← termText layout (.binary .add (.literal 13) (.literal 2))
    pure (first,graph,hit,last)
  let .ok ((first,pair,hit,last),emission) := action.run {}
    | throw (IO.userError "interleaved emission failed")
  unless first.name == hit.name && emission.cache.size < emission.text.size do
    throw (IO.userError "old cache not reused or graph manufactured old cache entries")
  let finite := FiniteRuntime.pack layout.storageShape (runtime 20 5)
  let some values := SystemVerilog.evaluateWires layout finite emission.text
    | throw (IO.userError "interleaved declarations are not ordered/evaluable")
  let env := (SystemVerilog.environment layout finite emission.text #[]).withTemporaries values
  unless env.scalar first.name == some 13 && env.scalar last.name == some 15 && pair.observe env == some 40 do
    throw (IO.userError "interleaved values changed")
  IO.println s!"PASS interleaved: cache={emission.cache.size}, declarations={emission.text.size}"

def main (args : List String) : IO Unit := do
  let out : System.FilePath := args.headD "artifacts/shared-integration"
  IO.FS.createDirAll out
  checkInterleave
  let twice : HybridIR.ReadCode := .bind (.memory 0 (.lit 0)) (.pure (.wrap32 (.add (.temp 0) (.temp 0))))
  let invalid : HybridIR.ReadCode := .bind (.memory 0 (.lit 1)) (.pure (.lit 7))
  let branch : HybridIR.ReadCode := .branch .left invalid (.pure (.lit 11))
  let mut records := #[]
  for (name,program,input,flag) in [
      ("twice",twice,20,0),("overflow",twice,4294967295,0),
      ("unused-invalid",invalid,20,0),("unchosen-invalid",branch,20,0),
      ("chosen-invalid",branch,20,1)] do
    records := records.push (← checkModule out name program input flag)
    records := records.push (← checkModule out ("shared-"++name) program input flag true)
  IO.FS.writeFile (out / "modules.json") (Lean.toJson records).pretty
