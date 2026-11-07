import IRComparison.Circuit.SystemVerilog.ConcreteReadPort
import IRComparison.Circuit.SystemVerilog.ConcreteControl
import IRComparison.Circuit.SystemVerilog.ModuleCode

namespace IRComparison.Circuit.SystemVerilog.Concrete

def inputPort (n : Tree) (word : Bool := false) : List Tree :=
  [atom "input",atom "wire"] ++ (if word then [descendingRange 32] else []) ++ [n]
def outputPort (n : Tree) (word : Bool := false) : List Tree :=
  [atom "output",atom "reg"] ++ (if word then [descendingRange 32] else []) ++ [n]

/-- Fixed public interface, including directions and widths. Parsing checks
the complete header instead of assuming it from the source artifact. -/
def interface : Tree := .group .round <| List.intercalate [atom ","] [
  inputPort (atom "clk"),inputPort (atom "rst"),inputPort (atom "start"),
  inputPort (atom "x") true,inputPort (atom "y") true,
  inputPort (atom "cfg_we"),inputPort (atom "cfg_reg"),inputPort (atom "cfg_id") true,
  inputPort (atom "cfg_addr") true,inputPort (atom "cfg_data") true,
  inputPort (atom "read_reg"),inputPort (atom "read_id") true,inputPort (atom "read_addr") true,
  outputPort (atom "read_data") true,outputPort (atom "read_valid"),
  outputPort (atom "busy"),outputPort (atom "done"),outputPort (atom "error")]

def fields (code : ModuleCode) : ClockFields :=
  ⟨code.reset,code.start,code.configure,code.cases,code.fault⟩

def processes (code : ModuleCode) : List Tree := [
  atom "always",atom "@*",readPort code.read,
  atom "always",atom "@",.group .round [atom "posedge",atom "clk"],clock (fields code) code.controller]

def moduleTree (code : ModuleCode) : Tree := .group .module <|
  [atom "hls_top",interface,atom ";"] ++ code.storage.flatMap declaration ++
  code.wires.toList.flatMap wire ++ processes code

def readProcesses : List Tree → Option (ReadCode × ClockFields)
  | [.atom ⟨"always",_⟩,.atom ⟨"@*",_⟩,rp,
      .atom ⟨"always",_⟩,.atom ⟨"@",_⟩,.group .round [.atom ⟨"posedge",_⟩,.atom ⟨"clk",_⟩],cp] => do
      return (← readReadPort rp,← readClock cp)
  | _ => none

def readModuleTree : Tree → Option ModuleCode
  | .group .module (.atom ⟨"hls_top",_⟩ :: ports :: .atom ⟨";",_⟩ :: body) => do
      if ports = interface then
        let (storage,body) ← readDeclarations body
        let (wires,body) ← readWires body
        let (read,clock) ← readProcesses body
        return ⟨storage,wires.toArray,read,clock.reset,clock.start,clock.configure,
          clock.cases,clock.fault,RTL.controller⟩
      else none
  | _ => none

/-- Physical extents and literal bit patterns survive serialization; the
unbounded integer used to create a literal and a logical zero-capacity bank
do not. Neither distinction affects the module's clock/read-port execution. -/
def moduleReadback (code : ModuleCode) : ModuleCode := {code with
  storage := code.storage.map physicalDeclaration
  wires := code.wires.map wireReadback
  reset := code.reset.literalReadback
  start := code.start.literalReadback
  configure := code.configure.literalReadback
  cases := code.cases.map Statement.literalReadback
  fault := code.fault.literalReadback}

theorem processes_readback (code : ModuleCode) (standard : code.controller = RTL.controller) :
    readProcesses (processes code) = some (code.read,(fields code).readback) := by
  simp only [processes,atom,readProcesses,readPort_readback,standard,clock_readback]
  rfl

theorem wires_stop_at_processes (code : ModuleCode) :
    readWires (processes code) = some ([],processes code) := by
  unfold processes
  rw [readWires.eq_def]
  rfl

theorem module_readback (code : ModuleCode)
    (positive : ∀ d ∈ code.storage, 0 < d.width)
    (standard : code.controller = RTL.controller) :
    readModuleTree (moduleTree code) = some (moduleReadback code) := by
  unfold moduleTree
  simp only [List.cons_append,List.nil_append,List.append_assoc,atom,readModuleTree,↓reduceIte]
  have stop : readDeclarations (code.wires.toList.flatMap wire ++ processes code) =
      some ([],code.wires.toList.flatMap wire ++ processes code) := by
    unfold processes
    exact declarations_stop_at_wires _ _
  rw [declarations_readback _ _ positive stop]
  simp only [bind,Option.bind]
  rw [wires_readback _ _ (wires_stop_at_processes code)]
  simp only [bind,Option.bind]
  rw [processes_readback code standard]
  simp only [bind,Option.bind]
  cases code
  simp only [moduleReadback,fields,ClockFields.readback,← Array.toList_map,Array.toArray_toList]
  congr 1
  simp_all

def printModule (code : ModuleCode) : String := print [moduleTree code]
def parseModule (text : String) : Option ModuleCode := do
  let [tree] ← parse text | none
  readModuleTree tree

/-- Whole String round trip. The parser accepts only text, including the
header, declarations, read process, clock event, priority and all cases. -/
theorem parse_printModule (code : ModuleCode)
    (positive : ∀ d ∈ code.storage, 0 < d.width)
    (standard : code.controller = RTL.controller) :
    parseModule (printModule code) = some (moduleReadback code) := by
  unfold parseModule printModule
  rw [parse_print]
  exact module_readback code positive standard

end IRComparison.Circuit.SystemVerilog.Concrete

namespace IRComparison.Circuit.SystemVerilog

/-- The production printer uses the same concrete syntax whose independent
text decoder is covered by `Concrete.parse_printModule`. -/
def ModuleCode.text (code : ModuleCode) : String := Concrete.printModule code

end IRComparison.Circuit.SystemVerilog
