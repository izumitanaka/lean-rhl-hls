import IRComparison.Circuit.SystemVerilog.Syntax

namespace IRComparison.Circuit.SystemVerilog

/-- The storage declarations actually printed by the backend. A zero-size
logical bank has one unused physical cell because SV array ranges are nonempty. -/
inductive Declaration where
  | scalar (name : Name) (width : Nat) (signed : Bool)
  | bank (name : Name) (width capacity : Nat)
  deriving Repr, DecidableEq

def Declaration.name : Declaration → Name
  | .scalar name .. | .bank name .. => name

def Declaration.width : Declaration → Nat
  | .scalar _ width _ | .bank _ width _ => width

def Declaration.signed : Declaration → Bool
  | .scalar _ _ signed => signed
  | .bank .. => false

def Declaration.text : Declaration → String
  | .scalar name width signed =>
    s!"  reg {if signed then "signed " else ""}[{width-1}:0] {name.text};"
  | .bank name width capacity =>
    s!"  (* mem2reg *) reg [{width-1}:0] {name.text} [0:{max 1 capacity-1}];"

def storageDeclarations (a : Artifact) : List Declaration :=
  [.scalar .pc (bits (a.machine.nodes.size-1)) false] ++
  (List.range a.wires.size).map (fun n =>
    .scalar (.holding n) (signedWidth (a.wires[n]?.getD wordRange)) true) ++
  (a.machine.nodes.toList.flatMap Node.registers).eraseDups.map
    (fun n => .scalar (.register n) 32 false) ++
  a.memories.toList.flatMap (fun (id,size) =>
    [.bank (.memory id) 32 size,.scalar (.length id) (bits size) false]) ++
  a.machine.capacities.toList.flatMap (fun (id,capacity) =>
    [.bank (.queue id) 32 capacity,.scalar (.used id) (bits capacity) false])

end IRComparison.Circuit.SystemVerilog
