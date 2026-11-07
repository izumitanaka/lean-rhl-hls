import IRComparison.Circuit.RTL.Combinational
import IRComparison.Circuit.RTL.LowerSound

namespace IRComparison.Circuit.RTL

def Scalar.evalWith (read : α → Runtime → Option Int) (old : Runtime) : Scalar α → Int
  | .literal n => n
  | .value e => (read e old).getD 0
  | .queueHead q => (old.queues q).headD 0
def Test.evalWith (read : α → Runtime → Option Int) (cap : Nat → Nat) (old : Runtime) : Test α → Bool
  | .valid e => (read e old).isSome
  | .nonzero e => (read e old).getD 0 != 0
  | .address a e => match read e old with
      | none => false
      | some j => decide (0 ≤ j ∧ j.toNat < (old.data.arrays a).size)
  | .room q => decide ((old.queues q).length < cap q)
  | .nonempty q => !(old.queues q).isEmpty
  | .and a b => a.evalWith read cap old && b.evalWith read cap old
def MemoryRhs.evalWith (read : α → Runtime → Option Int) (old : Runtime) : MemoryRhs α → Array Int
  | .empty => #[]
  | .copy a => old.data.arrays a
  | .set a j e => (old.data.arrays a).set! ((read j old).getD 0).toNat ((read e old).getD 0)
def QueueRhs.evalWith (read : α → Runtime → Option Int) (old : Runtime) : QueueRhs α → List Int
  | .empty => []
  | .append q e => old.queues q ++ [(read e old).getD 0]
  | .tail q => (old.queues q).tail
def Statement.evalWith (read : α → Runtime → Option Int) (cap : Nat → Nat) (old : Runtime) : Statement α → Runtime → Runtime
  | .skip,pending => pending
  | .assign k rhs,pending => k.write pending (rhs.evalWith read old)
  | .memory a rhs,pending => pending.setArray a (rhs.evalWith read old)
  | .queue q rhs,pending => pending.setQueue q (rhs.evalWith read old)
  | .seq a b,pending => b.evalWith read cap old (a.evalWith read cap old pending)
  | .branch c a b,pending => if c.evalWith read cap old then a.evalWith read cap old pending else b.evalWith read cap old pending

theorem map_scalar_correct (s : Scalar) (wr : Nat → Interval) (r : Runtime) :
    (s.mapExpressions (combinational wr)).evalWith Combinational.eval r = s.eval wr r := by
  cases s <;> simp [Scalar.mapExpressions,Scalar.evalWith,Scalar.eval,combinational_correct]
theorem map_test_correct (s : Test) (wr cap) (r : Runtime) :
    (s.mapExpressions (combinational wr)).evalWith Combinational.eval cap r = s.eval wr cap r := by
  induction s <;> simp_all [Test.mapExpressions,Test.evalWith,Test.eval,combinational_correct]
  rfl
theorem map_memory_correct (s : MemoryRhs) (wr) (r : Runtime) :
    (s.mapExpressions (combinational wr)).evalWith Combinational.eval r = s.eval wr r := by
  cases s <;> simp [MemoryRhs.mapExpressions,MemoryRhs.evalWith,MemoryRhs.eval,combinational_correct]
theorem map_queue_correct (s : QueueRhs) (wr) (r : Runtime) :
    (s.mapExpressions (combinational wr)).evalWith Combinational.eval r = s.eval wr r := by
  cases s <;> simp [QueueRhs.mapExpressions,QueueRhs.evalWith,QueueRhs.eval,combinational_correct]

theorem map_statement_correct (s : Statement) (wr cap) (old pending : Runtime) :
    (s.mapExpressions (combinational wr)).evalWith Combinational.eval cap old pending = s.eval wr cap old pending := by
  induction s generalizing pending with
  | skip => rfl
  | assign => simp only [Statement.mapExpressions,Statement.evalWith,Statement.eval,map_scalar_correct]
  | memory => simp only [Statement.mapExpressions,Statement.evalWith,Statement.eval,map_memory_correct]
  | queue => simp only [Statement.mapExpressions,Statement.evalWith,Statement.eval,map_queue_correct]
  | seq a b ia ib => simp only [Statement.mapExpressions,Statement.evalWith,Statement.eval,ia,ib]
  | branch c a b ia ib => simp only [Statement.mapExpressions,Statement.evalWith,Statement.eval,map_test_correct,ia,ib]

def Program.combinationalTick (p : Program Combinational) (r : Runtime) : Runtime :=
  if r.done then r else
    match p.cases[r.pc]? with
    | none => {r with done := true,error := true}
    | some code => code.evalWith Combinational.eval p.capacity r r

theorem lowerCombinational_tick (wr : Nat → Interval) (m : Machine) (r : Runtime) :
    (lowerCombinational wr m).combinationalTick r = m.bitTick wr r := by
  simp only [Program.combinationalTick,lowerCombinational,Machine.bitTick,Array.getElem?_map]
  split
  · rfl
  · cases hn : m.nodes[r.pc]? with
    | none => rfl
    | some node =>
      simp only [Option.map_some,Option.bind,map_statement_correct]
      have h := lowerNode_correct (wr:=wr) (cap:=m.capacity) node r
      cases he : bitExecute wr m.capacity node r <;> simp only [he,Option.getD] at h ⊢ <;> exact h

end IRComparison.Circuit.RTL
