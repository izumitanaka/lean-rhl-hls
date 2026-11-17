import IRComparison.Circuit.SystemVerilog.Netlist
import IRComparison.Circuit.SystemVerilog.StatementEval

namespace IRComparison.Circuit.SystemVerilog

/-- Execute the actual AST supplied to the SystemVerilog printer, including
reset/config/start. This evaluator is independent of the abstract RTL tick.
It is used for regression checks alongside the general code-generation and
startup proofs in PhysicalRun, StartupSound, and PreparationSound. -/
def clockCode (a : Artifact) (cases : List Statement) (declarations : Array Wire)
    (ports : RTL.Ports) (r : RTL.InterfaceState a.storageShape) : Option Store := do
  let base := environment a r.core declarations #[] r.busy ports
  let action := RTL.controller.select ports r.busy
  let (env,body) ← match action with
    | .reset => pure (base,resetCode a)
    | .start => pure (base,startCode a)
    | .configure => pure (base,configureCode a)
    | .hold => pure (base,Statement.skip)
    | .execute => do
        let values ← evaluateWires a r.core declarations
        let fault := faultCode
        pure (base.withTemporaries values,(cases[r.core.pc.toNat]?).getD fault)
  body.eval env base.store

/-- Compare observable declared registers and live memory prefixes. The
abstract finite tick canonicalizes unused cells; the actual NBA code leaves
those cells alone, so comparing unused padding would be incorrect. -/
def checkClockAgainst (a : Artifact) (cases : List Statement) (declarations : Array Wire)
    (ports : RTL.Ports) (r expected : RTL.InterfaceState a.storageShape) : Except String Unit := do
  let some actual := clockCode a cases declarations ports r | throw "undefined SystemVerilog clock operation"
  let base := environment a r.core declarations #[] r.busy ports
  let scalar := fun name value =>
    let observed := (actual.scalar name).map (fun v => ((BitVec.ofInt (base.type name).width v).toNat : Int))
    unless observed == some value do
      throw s!"clock mismatch at {name.text}: {actual.scalar name} versus {value}"
  scalar .pc expected.core.pc.toNat
  scalar .busy (if expected.busy then 1 else 0)
  scalar .done (if expected.core.done then 1 else 0)
  scalar .error (if expected.core.error then 1 else 0)
  for n in [:a.wires.size] do
    let value := if h : n < a.storageShape.wires.size then (expected.core.wires ⟨n,h⟩).toNat else 0
    scalar (.holding n) value
  for n in (a.machine.nodes.toList.flatMap Node.registers).eraseDups do
    let value := if h : n < a.storageShape.registers then (expected.core.regs ⟨n,h⟩).toNat else 0
    scalar (.register n) value
  for (n,_) in a.memories do
    if h : n < a.storageShape.memories then
      let bank := expected.core.arrays ⟨n,h⟩
      scalar (.length n) bank.used.val
      for j in [:bank.used.val] do
        let value := if hj : j < a.storageShape.memorySize n then (bank.cells ⟨j,hj⟩).toNat else 0
        unless actual.cell (.memory n) j == some value do throw s!"clock mismatch at m{n}[{j}]"
  for (n,_) in a.machine.capacities do
    if h : n < a.storageShape.queues then
      let bank := expected.core.queues ⟨n,h⟩
      scalar (.used n) bank.used.val
      for j in [:bank.used.val] do
        let value := if hj : j < a.storageShape.queueSize n then (bank.cells ⟨j,hj⟩).toNat else 0
        unless actual.cell (.queue n) j == some value do throw s!"clock mismatch at q{n}[{j}]"

/-- The original checker remains available. A regression driver can supply
an equal, precomputed reference state through checkClockAgainst. -/
def checkClock (a : Artifact) (cases : List Statement) (declarations : Array Wire)
    (ports : RTL.Ports) (r : RTL.InterfaceState a.storageShape) : Except String Unit :=
  checkClockAgainst a cases declarations ports r (RTL.interfaceTick a ports r)

end IRComparison.Circuit.SystemVerilog
