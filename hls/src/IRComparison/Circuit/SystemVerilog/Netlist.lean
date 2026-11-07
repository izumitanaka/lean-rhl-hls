import IRComparison.Circuit.SystemVerilog.Scope
import IRComparison.Circuit.RTL.Interface

namespace IRComparison.Circuit.SystemVerilog

/-- Environment for the concrete emitted names. Physical bank cells are
read directly, including unused cells; live lengths are separate registers. -/
def environmentFor (shape : StorageShape) (r : FiniteRuntime shape) (declarations : Array Wire)
    (temporary : Array Int) (busy : Bool := true) (ports : RTL.Ports := {}) : Environment where
  type := fun name => match name with
    | .temporary n => ⟨(declarations[n]?.map Wire.width).getD 0,true⟩
    | .holding n => ⟨signedWidth (shape.wireRange n),true⟩
    | .register _ | .memory _ | .queue _ | .x | .y | .configData | .configAddress | .configId => ⟨32,false⟩
    | .length n => ⟨bits (shape.memorySize n),false⟩
    | .used n => ⟨bits (shape.queueSize n),false⟩
    | .pc => ⟨bits (shape.states-1),false⟩
    | .busy | .done | .error | .configRegister => ⟨1,false⟩
    | .loopIndex | .shiftIndex _ => ⟨32,true⟩
  scalar := fun name => match name with
    | .temporary n => temporary[n]?
    | .holding n => if h : n < shape.wires.size then some ((r.wires ⟨n,h⟩).toInt) else none
    | .register n => if h : n < shape.registers then some ((r.regs ⟨n,h⟩).toNat) else none
    | .length n => if h : n < shape.memories then some ((r.arrays ⟨n,h⟩).used.val : Int) else none
    | .used n => if h : n < shape.queues then some ((r.queues ⟨n,h⟩).used.val : Int) else none
    | .pc => some r.pc.toNat
    | .busy => some (if busy then 1 else 0)
    | .done => some (if r.done then 1 else 0)
    | .error => some (if r.error then 1 else 0)
    | .x => some ports.x.toNat | .y => some ports.y.toNat
    | .configData => some ports.value.toNat | .configAddress => some ports.address.toNat
    | .configId => some ports.id.toNat | .configRegister => some (if ports.register then 1 else 0)
    | .memory _ | .queue _ | .loopIndex | .shiftIndex _ => none
  cell := fun name j => match name with
    | .memory n => if h : n < shape.memories then
        if hj : j < shape.memorySize n then some (((r.arrays ⟨n,h⟩).cells ⟨j,hj⟩).toNat) else none
      else none
    | .queue n => if h : n < shape.queues then
        if hj : j < shape.queueSize n then some (((r.queues ⟨n,h⟩).cells ⟨j,hj⟩).toNat) else none
      else none
    | _ => none

def environment (a : Artifact) (r : FiniteRuntime a.storageShape) (declarations : Array Wire)
    (temporary : Array Int) (busy : Bool := true) (ports : RTL.Ports := {}) : Environment :=
  environmentFor a.storageShape r declarations temporary busy ports

def Environment.withTemporaries (env : Environment) (values : Array Int) : Environment :=
  {env with scalar := fun name => match name with
    | .temporary n => values[n]?
    | _ => env.scalar name}

/-- Execute the concrete declaration list, retaining the already evaluated
prefix. The complete declaration environment fixes reference widths. -/
def appendWires (base : Environment) : List Wire → Array Int → Option (Array Int)
  | [],values => some values
  | wire::rest,values => do
      unless wire.name == .temporary values.size do none
      let bits ← wire.value.assignment (base.withTemporaries values) wire.width
      appendWires base rest (values.push bits.toInt)

/-- Execute continuous assignments in dependency order. Forward or missing
references fail explicitly; the same function is used by regression checks. -/
def evaluateWires (a : Artifact) (r : FiniteRuntime a.storageShape) (declarations : Array Wire) : Option (Array Int) :=
  appendWires (environment a r declarations #[]) declarations.toList #[]

/-- One level of mathematical term evaluation using previously checked child
values. Avoids re-expanding shared expression DAGs in regression checks. -/
def evaluateNode (r : Runtime) (child : RTL.Term → Option Int) : RTL.Term → Option Int
  | .literal n => some n
  | .wire n => some (r.wires n)
  | .register n => some (r.data.regs n)
  | .length a => some ((r.data.arrays a).size : Int)
  | .cell a j => return ((r.data.arrays a)[(← child j).toNat]?).getD 0
  | .binary op u v => return hardwareBin op (← child u) (← child v)
  | .nonnegative v => return (← child v).toNat
  | .resize w v => return (BitVec.ofInt w (← child v)).toInt
  | .mux c yes no => do
      if (← child c) != 0 then child yes else child no

theorem evaluateNode_correct (r : Runtime) (child : RTL.Term → Option Int)
    (agrees : ∀ t, child t = some (t.eval r)) (t : RTL.Term) :
    evaluateNode r child t = some (t.eval r) := by
  cases t <;> simp [evaluateNode,agrees,RTL.Term.eval]
  split <;> rfl

/-- These checks are regression instrumentation for the new evaluator. They
are not a replacement for a general correctness proof of `generateCode`. -/
def checkCache (a : Artifact) (r : FiniteRuntime a.storageShape) (code : Emission) : Except String Unit := do
  let some values := evaluateWires a r code.text | throw "undefined generated SystemVerilog expression"
  let logical := r.decode
  let mut checked : Array (RTL.Term × Int) := #[]
  for (term,signal) in code.cache do
    let .temporary n := signal.name | throw "unexpected cached signal name"
    let some actual := values[n]? | throw "cached signal is undeclared"
    let some expected := evaluateNode logical
      (fun child => (checked.toList.find? (fun p => p.1 == child)).map Prod.snd) term
      | throw "missing checked child expression"
    unless actual == expected do throw s!"SystemVerilog expression e{n} differs: {actual} versus {expected}"
    checked := checked.push (term,expected)

end IRComparison.Circuit.SystemVerilog
