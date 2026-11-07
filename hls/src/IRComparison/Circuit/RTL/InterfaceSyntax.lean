import IRComparison.Circuit.RTL.CombinationalSyntax

namespace IRComparison.Circuit

def Expr.registers : Expr → List Nat
  | .reg n => [n]
  | .bin _ a b => a.registers ++ b.registers
  | .select c a b => c.registers ++ a.registers ++ b.registers
  | .seq a b => a.registers ++ b.registers
  | .memory _ e | .natIndex e => e.registers
  | _ => []

def Node.registers : Node → List Nat
  | .wire _ e _ | .send _ e _ | .branch e .. => e.registers
  | .assign r e _ => r::e.registers
  | .store _ j e _ => j.registers ++ e.registers
  | _ => []

namespace RTL

/-- Clock-edge priority shared by the executable interface and the printer.
The environment may write configuration only while idle; start wins over
configuration, and reset wins over every other signal. -/
inductive PortTest where
  | reset | busy | start | configure
  deriving Repr, DecidableEq
inductive PortAction where
  | reset | start | configure | execute | hold
  deriving Repr, DecidableEq
inductive Controller where
  | action (a : PortAction)
  | branch (test : PortTest) (yes no : Controller)
  deriving Repr

def controller : Controller :=
  .branch .reset (.action .reset)
    (.branch .busy (.action .execute)
      (.branch .start (.action .start)
        (.branch .configure (.action .configure) (.action .hold))))

structure Ports where
  reset : Bool := false
  start : Bool := false
  configure : Bool := false
  register : Bool := false
  id : BitVec 32 := 0
  address : BitVec 32 := 0
  value : BitVec 32 := 0
  x : BitVec 32 := 0
  y : BitVec 32 := 0
  deriving Repr

def PortTest.eval (p : Ports) (busy : Bool) : PortTest → Bool
  | .reset => p.reset
  | .busy => busy
  | .start => p.start
  | .configure => p.configure

def Controller.select (p : Ports) (busy : Bool) : Controller → PortAction
  | .action a => a
  | .branch test yes no => if test.eval p busy then yes.select p busy else no.select p busy

def PortTest.text : PortTest → String
  | .reset => "rst"
  | .busy => "busy"
  | .start => "start"
  | .configure => "cfg_we"

def Controller.render (action : PortAction → String) : Controller → String
  | .action a => action a
  | .branch test yes no =>
    "if (" ++ test.text ++ ") begin " ++ yes.render action ++ " end else begin " ++ no.render action ++ " end"

/-- This is a grammar judgment for the controller fragment, not an evaluator
which recovers semantics by remembering the source of a generated string.
Each conditional is explicitly delimited, including its else branch. -/
inductive Controller.Prints (action : PortAction → String) : Controller → String → Prop where
  | action (a) : Prints action (.action a) (action a)
  | branch {test yes no ys ns} : Prints action yes ys → Prints action no ns →
      Prints action (.branch test yes no)
        ("if (" ++ test.text ++ ") begin " ++ ys ++ " end else begin " ++ ns ++ " end")

theorem Controller.render_prints (action : PortAction → String) (c : Controller) :
    Prints action c (c.render action) := by
  induction c with
  | action a => exact .action a
  | branch test yes no hy hn => exact .branch hy hn

theorem controller_reset (p : Ports) (busy : Bool) (h : p.reset = true) :
    controller.select p busy = .reset := by simp [controller,Controller.select,PortTest.eval,h]
theorem controller_execute (p : Ports) (h : p.reset = false) :
    controller.select p true = .execute := by simp [controller,Controller.select,PortTest.eval,h]
theorem controller_start (p : Ports) (hr : p.reset = false) (hs : p.start = true) :
    controller.select p false = .start := by simp [controller,Controller.select,PortTest.eval,hr,hs]
theorem controller_configure (p : Ports) (hr : p.reset = false) (hs : p.start = false)
    (hc : p.configure = true) : controller.select p false = .configure := by
  simp [controller,Controller.select,PortTest.eval,hr,hs,hc]

end RTL
end IRComparison.Circuit
