import IRComparison.Circuit.Expr

namespace IRComparison.Circuit

/-- One state update per clock, plus control. Arrays are finite register banks
with combinational reads. Queue receive is destructive, never peek. -/
inductive Node where
  | halt
  | jump (next : Nat)
  | wire (slot : Nat) (value : Expr) (next : Nat)
  | assign (reg : Nat) (value : Expr) (next : Nat)
  | store (array : Nat) (index value : Expr) (next : Nat)
  | branch (condition : Expr) (yes no : Nat)
  | snapshot (destination source : Nat) (next : Nat)
  | erase (array : Nat) (next : Nat)
  | clear (queue : Nat) (next : Nat)
  | send (queue : Nat) (value : Expr) (next : Nat)
  | receive (queue slot : Nat) (next : Nat)
  deriving Repr, Inhabited

structure Machine where
  entry : Nat
  nodes : Array Node
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

def execute (capacities : Nat → Nat) (node : Node) (r : Runtime) : Option Runtime :=
  match node with
  | .halt => some { r with done := true }
  | .jump n => some { r with pc := n }
  | .wire slot v n => return { (r.setWire slot (← v.eval r.data r.wires)) with pc := n }
  | .assign slot v n => return { r with data := r.data.set slot (← v.eval r.data r.wires), pc := n }
  | .store a j v n => do
      let t ← r.data.write a (← j.eval r.data r.wires) (← v.eval r.data r.wires)
      return { r with data := t, pc := n }
  | .branch e yes no => return { r with pc := if (← e.eval r.data r.wires) != 0 then yes else no }
  | .snapshot a b n => some { (r.setArray a (r.data.arrays b)) with pc := n }
  | .erase a n => some { (r.setArray a #[]) with pc := n }
  | .clear q n => some { (r.setQueue q []) with pc := n }
  | .send q v n => do
      let x ← v.eval r.data r.wires
      if (r.queues q).length < capacities q then
        return { (r.setQueue q (r.queues q ++ [x])) with pc := n }
      else none
  | .receive q slot n => match r.queues q with
      | [] => none
      | x::xs => some { ((r.setQueue q xs).setWire slot x) with pc := n }

def Machine.capacity (m : Machine) (q : Nat) : Nat :=
  ((m.capacities.toList.find? (fun p => p.1 == q)).map Prod.snd).getD 0

def Machine.tick (m : Machine) (r : Runtime) : Runtime :=
  if r.done then r else
    match m.nodes[r.pc]?.bind (fun n => execute m.capacity n r) with
    | none => { r with done := true, error := true }
    | some t => t

def Machine.run (m : Machine) : Nat → Runtime → Runtime
  | 0,r => r
  | n+1,r => m.run n (m.tick r)

def Machine.start (m : Machine) (s : IRComparison.State) (x y : Int) : Runtime :=
  ⟨m.entry,s,(fun n => if n = 0 then x else if n = 1 then y else 0),fun _ => [],false,false⟩

def Runtime.result (r : Runtime) : Option (Option IRComparison.State) :=
  if r.done then some (if r.error then none else some r.data) else none

theorem halt_stable (m : Machine) (r : Runtime) (h : r.done = true) : m.tick r = r := by simp [Machine.tick,h]

end IRComparison.Circuit
