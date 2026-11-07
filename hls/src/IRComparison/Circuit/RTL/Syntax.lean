import IRComparison.Circuit.Lower

namespace IRComparison.Circuit.RTL

/-- Values used by nonblocking assignments. `value` is the shared checked
combinational language; separating its value and validity wires is a later
expression-lowering step, not an assumption of the statement theorem. -/
inductive Scalar (α : Type := Circuit.Expr) where
  | literal (n : Int)
  | value (e : α)
  | queueHead (q : Nat)
  deriving Repr

inductive Test (α : Type := Circuit.Expr) where
  | valid (e : α)
  | nonzero (e : α)
  | address (a : Nat) (e : α)
  | room (q : Nat)
  | nonempty (q : Nat)
  | and (a b : Test α)
  deriving Repr

inductive Register where
  | pc | done | error
  | wire (n : Nat)
  | data (n : Nat)
  deriving Repr, DecidableEq

/-- Array assignments denote the live prefix of a finite bank. The printer
expands `copy`, `set`, and the FIFO shifts into fixed-bank assignments.
The live-prefix/physical-cell correspondence is a separate obligation. -/
inductive MemoryRhs (α : Type := Circuit.Expr) where
  | empty
  | copy (source : Nat)
  | set (array : Nat) (index value : α)
  deriving Repr

inductive QueueRhs (α : Type := Circuit.Expr) where
  | empty
  | append (queue : Nat) (value : α)
  | tail (queue : Nat)
  deriving Repr

inductive Statement (α : Type := Circuit.Expr) where
  | skip
  | assign (target : Register) (rhs : Scalar α)
  | memory (target : Nat) (rhs : MemoryRhs α)
  | queue (target : Nat) (rhs : QueueRhs α)
  | seq (a b : Statement α)
  | branch (condition : Test α) (yes no : Statement α)
  deriving Repr

def advance (n : Nat) : Statement := .assign .pc (.literal n)
def fault : Statement := .seq (.assign .done (.literal 1)) (.assign .error (.literal 1))
def halt : Statement := .assign .done (.literal 1)
def guarded (g : Test) (body : Statement) : Statement := .branch g body fault

def lowerNode : Node → Statement
  | .halt => halt
  | .jump n => advance n
  | .wire k e n => guarded (.valid e) (.seq (.assign (.wire k) (.value e)) (advance n))
  | .assign k e n => guarded (.valid e) (.seq (.assign (.data k) (.value e)) (advance n))
  | .store a j e n => guarded (.and (.address a j) (.valid e)) (.seq (.memory a (.set a j e)) (advance n))
  | .branch e yes no => guarded (.valid e) (.branch (.nonzero e) (advance yes) (advance no))
  | .snapshot a b n => .seq (.memory a (.copy b)) (advance n)
  | .erase a n => .seq (.memory a .empty) (advance n)
  | .clear q n => .seq (.queue q .empty) (advance n)
  | .send q e n => guarded (.and (.valid e) (.room q)) (.seq (.queue q (.append q e)) (advance n))
  | .receive q k n => guarded (.nonempty q)
      (.seq (.assign (.wire k) (.queueHead q)) (.seq (.queue q (.tail q)) (advance n)))

structure Program (α : Type := Circuit.Expr) where
  entry : Nat
  cases : Array (Statement α)
  capacities : Array (Nat × Nat)
  deriving Repr

def lower (m : Machine) : Program := ⟨m.entry,m.nodes.map lowerNode,m.capacities⟩

end IRComparison.Circuit.RTL
