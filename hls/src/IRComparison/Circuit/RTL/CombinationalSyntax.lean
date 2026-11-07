import IRComparison.Circuit.RTL.Syntax

namespace IRComparison.Circuit.RTL

/-- Expression vocabulary of the generated two-state combinational RTL.
Every circuit expression is resized explicitly; invalid loads carry a
separate validity formula, never a fabricated successful value. -/
inductive Term where
  | literal (n : Int)
  | wire (n : Nat)
  | register (n : Nat)
  | length (a : Nat)
  | cell (a : Nat) (index : Term)
  | binary (op : Circuit.Bin) (a b : Term)
  | nonnegative (a : Term)
  | resize (width : Nat) (a : Term)
  | mux (c yes no : Term)
  deriving Repr, DecidableEq

inductive Validity where
  | yes | no
  | and (a b : Validity)
  | address (array : Nat) (index : Term)
  | mux (condition : Term) (yes no : Validity)
  deriving Repr, DecidableEq

/-- Fold constant guards while constructing them, before their syntax grows.
No structural equality search or assumption about a source program is used. -/
def Validity.both : Validity → Validity → Validity
  | .yes, b => b
  | .no, _ => .no
  | a, .yes => a
  | _, .no => .no
  | a, b => .and a b

/-- Equal constant arms do not depend on the (total) condition value. -/
def Validity.choose (c : Term) : Validity → Validity → Validity
  | .yes, .yes => .yes
  | .no, .no => .no
  | a, b => .mux c a b

structure Combinational where
  value : Term
  valid : Validity
  bounds : Interval
  deriving Repr

def combinational (wr : Nat → Interval) (e : Circuit.Expr) : Combinational :=
  let width := signedWidth (range wr e)
  let raw : Term × Validity := match e with
    | .fail => ⟨.literal 0,.no⟩
    | .lit n => ⟨.literal n,.yes⟩
    | .wire n => ⟨.wire n,.yes⟩
    | .reg n => ⟨.register n,.yes⟩
    | .memory a j =>
        let p := combinational wr j
        ⟨.cell a p.value,Validity.both p.valid (.address a p.value)⟩
    | .bin op a b =>
        let p := combinational wr a
        let q := combinational wr b
        ⟨.binary op p.value q.value,Validity.both p.valid q.valid⟩
    | .natIndex a =>
        let p := combinational wr a
        ⟨.nonnegative p.value,p.valid⟩
    | .select c a b =>
        let p := combinational wr c
        let q := combinational wr a
        let t := combinational wr b
        ⟨.mux p.value q.value t.value,Validity.both p.valid (Validity.choose p.value q.valid t.valid)⟩
    | .seq a b =>
        let p := combinational wr a
        let q := combinational wr b
        ⟨q.value,Validity.both p.valid q.valid⟩
  ⟨.resize width raw.1,raw.2,range wr e⟩


def Scalar.mapExpressions (f : α → β) : Scalar α → Scalar β
  | .literal n => .literal n
  | .value e => .value (f e)
  | .queueHead q => .queueHead q
def Test.mapExpressions (f : α → β) : Test α → Test β
  | .valid e => .valid (f e)
  | .nonzero e => .nonzero (f e)
  | .address a e => .address a (f e)
  | .room q => .room q
  | .nonempty q => .nonempty q
  | .and a b => .and (a.mapExpressions f) (b.mapExpressions f)
def MemoryRhs.mapExpressions (f : α → β) : MemoryRhs α → MemoryRhs β
  | .empty => .empty
  | .copy a => .copy a
  | .set a j e => .set a (f j) (f e)
def QueueRhs.mapExpressions (f : α → β) : QueueRhs α → QueueRhs β
  | .empty => .empty
  | .append q e => .append q (f e)
  | .tail q => .tail q
def Statement.mapExpressions (f : α → β) : Statement α → Statement β
  | .skip => .skip
  | .assign k e => .assign k (e.mapExpressions f)
  | .memory a e => .memory a (e.mapExpressions f)
  | .queue q e => .queue q (e.mapExpressions f)
  | .seq a b => .seq (a.mapExpressions f) (b.mapExpressions f)
  | .branch c a b => .branch (c.mapExpressions f) (a.mapExpressions f) (b.mapExpressions f)

def lowerCombinational (wr : Nat → Interval) (m : Machine) : Program Combinational :=
  ⟨m.entry,m.nodes.map (fun n => (lowerNode n).mapExpressions (combinational wr)),m.capacities⟩

def artifactProgram (a : Artifact) : Program Combinational :=
  lowerCombinational (fun n => a.wires[n]?.getD ⟨0,0⟩) a.machine


end IRComparison.Circuit.RTL
