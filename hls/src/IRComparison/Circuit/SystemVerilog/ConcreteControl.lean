import IRComparison.Circuit.SystemVerilog.ConcreteStatement

namespace IRComparison.Circuit.SystemVerilog.Concrete

def caseEntries (start : Nat) : List Statement → List Tree
  | [] => []
  | s::ss => natural start :: atom ":" :: statement s :: caseEntries (start+1) ss

def readCaseEntries (start : Nat) : List Tree → Option (List Statement)
  | [] => some []
  | id :: .atom ⟨":",_⟩ :: body :: rest => do
      let index ← readNatural id
      if index = start then
        return (← readStatement body) :: (← readCaseEntries (start+1) rest)
      else none
  | _ => none

theorem cases_readback (cases : List Statement) (start : Nat) :
    readCaseEntries start (caseEntries start cases) = some (cases.map Statement.literalReadback) := by
  induction cases generalizing start with
  | nil => rfl
  | cons s ss ih =>
    simp only [caseEntries,atom,readCaseEntries,read_natural,bind,Option.bind,↓reduceIte,
      statement_readback,ih,List.map_cons]
    rfl

def execution (cases : List Statement) (fault : Statement) : Tree :=
  .group .cases <| .group .round [atom "pc"] :: atom "default" :: atom ":" :: statement fault :: caseEntries 0 cases

def readExecution : Tree → Option (List Statement × Statement)
  | .group .cases (.group .round [.atom ⟨"pc",_⟩] :: .atom ⟨"default",_⟩ ::
      .atom ⟨":",_⟩ :: fault :: entries) => do
      return (← readCaseEntries 0 entries,← readStatement fault)
  | _ => none

theorem execution_readback (cases : List Statement) (fault : Statement) :
    readExecution (execution cases fault) =
      some (cases.map Statement.literalReadback,fault.literalReadback) := by
  simp only [execution,atom,readExecution,cases_readback,statement_readback]
  rfl

def conditional (test yes no : Tree) : Tree :=
  .group .block [atom "if",.group .round [test],yes,atom "else",no]
def readConditional (test : Tree) : Tree → Option (Tree × Tree)
  | .group .block [.atom ⟨"if",_⟩,.group .round [actual],yes,.atom ⟨"else",_⟩,no] =>
      if actual = test then some (yes,no) else none
  | _ => none

@[simp] theorem conditional_readback (test yes no : Tree) :
    readConditional test (conditional test yes no) = some (yes,no) := by
  simp [conditional,readConditional,atom]

structure ClockFields where
  reset : Statement
  start : Statement
  configure : Statement
  cases : List Statement
  fault : Statement

def ClockFields.readback (f : ClockFields) : ClockFields :=
  ⟨f.reset.literalReadback,f.start.literalReadback,f.configure.literalReadback,
    f.cases.map Statement.literalReadback,f.fault.literalReadback⟩

def controller (actions : RTL.PortAction → Tree) : RTL.Controller → Tree
  | .action a => actions a
  | .branch test yes no => conditional (atom test.text (by cases test <;> decide))
      (controller actions yes) (controller actions no)

def clock (f : ClockFields) (c : RTL.Controller) : Tree :=
  controller (fun a => match a with
    | .reset => statement f.reset
    | .start => statement f.start
    | .configure => statement f.configure
    | .execute => execution f.cases f.fault
    | .hold => statement .skip) c

/-- The generated backend has a fixed reset/busy/start/configuration
priority. The parser checks that actual priority and the idle no-op. -/
def readClock (t : Tree) : Option ClockFields := do
  let (reset,next) ← readConditional (atom "rst") t
  let (execute,next) ← readConditional (atom "busy") next
  let (start,next) ← readConditional (atom "start") next
  let (configure,hold) ← readConditional (atom "cfg_we") next
  if hold = .group .block [] then
    let (cases,fault) ← readExecution execute
    return ⟨← readStatement reset,← readStatement start,← readStatement configure,cases,fault⟩
  else none

theorem clock_readback (f : ClockFields) :
    readClock (clock f RTL.controller) = some f.readback := by
  simp only [clock,RTL.controller,controller,RTL.PortTest.text,readClock,conditional_readback,
    bind,Option.bind,statement,↓reduceIte,execution_readback,statement_readback]
  rfl

end IRComparison.Circuit.SystemVerilog.Concrete
