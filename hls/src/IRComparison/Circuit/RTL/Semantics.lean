import IRComparison.Circuit.RTL.Syntax
import IRComparison.Circuit.BitMachine

namespace IRComparison.Circuit.RTL

def Scalar.eval (wr : Nat → Interval) (old : Runtime) : Scalar → Int
  | .literal n => n
  | .value e => (e.bitEval wr old.data old.wires).getD 0
  | .queueHead q => (old.queues q).headD 0

def Test.eval (wr : Nat → Interval) (cap : Nat → Nat) (old : Runtime) : Test → Bool
  | .valid e => (e.bitEval wr old.data old.wires).isSome
  | .nonzero e => (e.bitEval wr old.data old.wires).getD 0 != 0
  | .address a e => match e.bitEval wr old.data old.wires with
      | none => false
      | some j => decide (0 ≤ j ∧ j.toNat < (old.data.arrays a).size)
  | .room q => decide ((old.queues q).length < cap q)
  | .nonempty q => !(old.queues q).isEmpty
  | .and a b => a.eval wr cap old && b.eval wr cap old

def Register.write (r : Runtime) (v : Int) : Register → Runtime
  | .pc => { r with pc := v.toNat }
  | .done => { r with done := v != 0 }
  | .error => { r with error := v != 0 }
  | .wire n => r.setWire n v
  | .data n => { r with data := r.data.set n v }

def MemoryRhs.eval (wr : Nat → Interval) (old : Runtime) : MemoryRhs → Array Int
  | .empty => #[]
  | .copy a => old.data.arrays a
  | .set a j e => (old.data.arrays a).set! ((j.bitEval wr old.data old.wires).getD 0).toNat
      ((e.bitEval wr old.data old.wires).getD 0)

def QueueRhs.eval (wr : Nat → Interval) (old : Runtime) : QueueRhs → List Int
  | .empty => []
  | .append q e => old.queues q ++ [(e.bitEval wr old.data old.wires).getD 0]
  | .tail q => (old.queues q).tail

/-- All RHSs and conditions read `old`; `pending` accumulates nonblocking
updates. Thus a later assignment cannot accidentally read an earlier write
from the same clock edge. -/
def Statement.eval (wr : Nat → Interval) (cap : Nat → Nat) (old : Runtime) : Statement → Runtime → Runtime
  | .skip,pending => pending
  | .assign target rhs,pending => target.write pending (rhs.eval wr old)
  | .memory target rhs,pending => pending.setArray target (rhs.eval wr old)
  | .queue target rhs,pending => pending.setQueue target (rhs.eval wr old)
  | .seq a b,pending => b.eval wr cap old (a.eval wr cap old pending)
  | .branch c a b,pending => if c.eval wr cap old then a.eval wr cap old pending else b.eval wr cap old pending


def Program.capacity (p : Program α) (q : Nat) := ((p.capacities.toList.find? (fun v => v.1 == q)).map Prod.snd).getD 0

def Program.tick (p : Program) (wr : Nat → Interval) (r : Runtime) : Runtime :=
  if r.done then r else (p.cases[r.pc]?.getD fault).eval wr p.capacity r r

def Program.run (p : Program) (wr : Nat → Interval) : Nat → Runtime → Runtime
  | 0,r => r
  | n+1,r => p.run wr n (p.tick wr r)

end IRComparison.Circuit.RTL
