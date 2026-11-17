import IRComparison.Circuit.SystemVerilog.Syntax
import IRComparison.Circuit.SystemVerilog.Declarations
import IRComparison.Circuit.SystemVerilog.ReadPort
namespace IRComparison.Circuit.SystemVerilog

/-- Metadata-only interface validation, available before finite-state proof
infrastructure. No expression evaluation or source restriction is involved. -/
def InterfaceLayout (a : Artifact) : Prop :=
  (∀ e ∈ a.originalMemories.toList,
    ((a.originalMemories.toList.find? (fun p => p.1 == e.1)).map Prod.snd) = some e.2 ∧
    e.1 < (a.memories.toList.map Prod.fst).foldl (fun n id => max n (id+1)) 0 ∧
    e.2 ≤ ((a.memories.toList.find? (fun p => p.1 == e.1)).map Prod.snd).getD 0) ∧
  (∀ e ∈ a.memories.toList,
    e.1 < (a.memories.toList.map Prod.fst).foldl (fun n id => max n (id+1)) 0 ∧
    e.2 = ((a.memories.toList.find? (fun p => p.1 == e.1)).map Prod.snd).getD 0)

instance (a : Artifact) : Decidable (InterfaceLayout a) := by
  unfold InterfaceLayout
  infer_instance

/-- Interface actions use the same concrete assignment AST as compute cases.
All right-hand sides refer to pre-edge values. -/
def sequence (body : List Statement) : Statement := body.foldr Statement.seq .skip

def write (name : Name) (value : Expr) : Statement := .assign (.reference name) value

def resetCode (a : Artifact) : Statement := sequence <|
  [write .pc (.integer 0),write .busy (.bit false),write .done (.bit false),write .error (.bit false)] ++
  (List.range a.wires.size).map (fun n => write (.holding n) (.integer 0)) ++
  (a.machine.nodes.toList.flatMap Node.registers).eraseDups.map (fun n => write (.register n) (.integer 0)) ++
  a.memories.toList.map (fun (id,size) => .seq (write (.length id) (.integer size))
    (.forRange .loopIndex size (.assign (.index (.memory id) (.reference .loopIndex)) (.integer 0)))) ++
  a.machine.capacities.toList.map (fun (q,_) => write (.used q) (.integer 0))

def startCode (a : Artifact) : Statement := sequence <|
  [write .busy (.bit true),write .done (.bit false),write .error (.bit false),
   write .pc (.integer a.machine.entry),write (.holding 0) (.unsigned (.reference .x)),
   write (.holding 1) (.unsigned (.reference .y))] ++
  ((List.range a.wires.size).drop 2).map (fun n => write (.holding n) (.integer 0)) ++
  a.originalMemories.toList.map (fun (id,size) => write (.length id) (.integer size)) ++
  a.machine.capacities.toList.map (fun (q,_) => write (.used q) (.integer 0))

def configureCode (a : Artifact) : Statement :=
  .branch (.reference .configRegister)
    (sequence ((a.machine.nodes.toList.flatMap Node.registers).eraseDups.map fun n =>
      .branch (.binary .eq (.reference .configId) (.integer n))
        (write (.register n) (.reference .configData)) .skip))
    (sequence (a.originalMemories.toList.map fun (id,size) =>
      .branch (.binary .and (.binary .eq (.reference .configId) (.integer id))
        (.binary .lt (.reference .configAddress) (.integer size)))
        (.assign (.index (.memory id) (.reference .configAddress)) (.reference .configData)) .skip))

end IRComparison.Circuit.SystemVerilog

namespace IRComparison.Circuit.SystemVerilog

def faultCode : Statement := .seq (write .done (.bit true))
  (.seq (write .error (.bit true)) (write .busy (.bit false)))

/-- The complete module body passed to the printer, with the backend's fixed
host interface. It contains concrete declarations and statements, not a
source artifact or a callback into the source/RTL machine. -/
structure ModuleCode where
  storage : List Declaration
  wires : Array Wire
  read : ReadCode
  reset : Statement
  start : Statement
  configure : Statement
  cases : List Statement
  fault : Statement
  controller : RTL.Controller

def moduleCode (a : Artifact) (outputs : List Nat) (cases : List Statement)
    (wires : Array Wire) : ModuleCode :=
  ⟨storageDeclarations a,wires,readCode a outputs,resetCode a,startCode a,
    configureCode a,cases,faultCode,RTL.controller⟩

end IRComparison.Circuit.SystemVerilog
