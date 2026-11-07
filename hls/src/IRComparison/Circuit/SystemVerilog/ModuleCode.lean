import IRComparison.Circuit.SystemVerilog.Declarations
import IRComparison.Circuit.SystemVerilog.ReadPort
import IRComparison.Circuit.SystemVerilog.InterfaceCode

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
