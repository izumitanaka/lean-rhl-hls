import IRComparison.Circuit.Expr

namespace IRComparison.Circuit

/-- Expression interpretation used by the existing controller semantics.
The shared representation supplies this interface without changing state or
failure observations. -/
class ExpressionEvaluation (α : Type) where
  eval : α → IRComparison.State → (Nat → Int) → Option Int
  zero : α
  zero_some : ∀ s w, eval zero s w = some 0
  invalid : α
  invalid_none : ∀ s w, eval invalid s w = none

@[default_instance] instance : ExpressionEvaluation Expr where
  eval e s w := e.eval s w
  zero := .lit 0
  zero_some := by intros; rfl
  invalid := .fail
  invalid_none := by intros; rfl

attribute [simp] ExpressionEvaluation.zero_some ExpressionEvaluation.invalid_none

@[simp] theorem expressionEvaluation_original (e : Expr) (s : IRComparison.State) (w : Nat → Int) :
    ExpressionEvaluation.eval e s w = e.eval s w := rfl

/-- One state update per clock, plus control. Arrays are finite register banks
with combinational reads. Queue receive is destructive, never peek. -/
inductive Node (α : Type := Expr) where
  | halt
  | jump (next : Nat)
  | wire (slot : Nat) (value : α) (next : Nat)
  | assign (reg : Nat) (value : α) (next : Nat)
  | store (array : Nat) (index value : α) (next : Nat)
  | branch (condition : α) (yes no : Nat)
  | snapshot (destination source : Nat) (next : Nat)
  | erase (array : Nat) (next : Nat)
  | clear (queue : Nat) (next : Nat)
  | send (queue : Nat) (value : α) (next : Nat)
  | receive (queue slot : Nat) (next : Nat)
  deriving Repr, Inhabited

structure Machine (α : Type := Expr) where
  entry : Nat
  nodes : Array (Node α)
  capacities : Array (Nat × Nat)
  deriving Repr

structure Runtime where
  pc : Nat
  data : IRComparison.State
  wires : Nat → Int
  queues : Nat → List Int
  done : Bool := false
  error : Bool := false

def Runtime.setWire (r : Runtime) (slot : Nat) (v : Int) : Runtime :=
  { r with wires := fun k => if k = slot then v else r.wires k }

def Runtime.setQueue (r : Runtime) (q : Nat) (values : List Int) : Runtime :=
  { r with queues := fun k => if k = q then values else r.queues k }

def Runtime.setArray (r : Runtime) (a : Nat) (values : Array Int) : Runtime :=
  { r with data := { r.data with arrays := fun k => if k = a then values else r.data.arrays k } }

def execute {α : Type} [ExpressionEvaluation α] (capacities : Nat → Nat) (node : Node α) (r : Runtime) : Option Runtime :=
  match node with
  | .halt => some { r with done := true }
  | .jump n => some { r with pc := n }
  | .wire slot v n => return { (r.setWire slot (← ExpressionEvaluation.eval v r.data r.wires)) with pc := n }
  | .assign slot v n => return { r with data := r.data.set slot (← ExpressionEvaluation.eval v r.data r.wires), pc := n }
  | .store a j v n => do
      let t ← r.data.write a (← ExpressionEvaluation.eval j r.data r.wires) (← ExpressionEvaluation.eval v r.data r.wires)
      return { r with data := t, pc := n }
  | .branch e yes no => return { r with pc := if (← ExpressionEvaluation.eval e r.data r.wires) != 0 then yes else no }
  | .snapshot a b n => some { (r.setArray a (r.data.arrays b)) with pc := n }
  | .erase a n => some { (r.setArray a #[]) with pc := n }
  | .clear q n => some { (r.setQueue q []) with pc := n }
  | .send q v n => do
      let x ← ExpressionEvaluation.eval v r.data r.wires
      if (r.queues q).length < capacities q then
        return { (r.setQueue q (r.queues q ++ [x])) with pc := n }
      else none
  | .receive q slot n => match r.queues q with
      | [] => none
      | x::xs => some { ((r.setQueue q xs).setWire slot x) with pc := n }

def Machine.capacity (m : Machine α) (q : Nat) : Nat :=
  ((m.capacities.toList.find? (fun p => p.1 == q)).map Prod.snd).getD 0

def Machine.tick {α : Type} [ExpressionEvaluation α] (m : Machine α) (r : Runtime) : Runtime :=
  if r.done then r else
    match m.nodes[r.pc]?.bind (fun n => execute m.capacity n r) with
    | none => { r with done := true, error := true }
    | some t => t

def Machine.run {α : Type} [ExpressionEvaluation α] (m : Machine α) : Nat → Runtime → Runtime
  | 0,r => r
  | n+1,r => m.run n (m.tick r)

def Machine.start (m : Machine α) (s : IRComparison.State) (x y : Int) : Runtime :=
  ⟨m.entry,s,(fun n => if n = 0 then x else if n = 1 then y else 0),fun _ => [],false,false⟩

def Runtime.result (r : Runtime) : Option (Option IRComparison.State) :=
  if r.done then some (if r.error then none else some r.data) else none

theorem halt_stable {α : Type} [ExpressionEvaluation α] (m : Machine α) (r : Runtime) (h : r.done = true) : m.tick r = r := by simp [Machine.tick,h]

end IRComparison.Circuit
