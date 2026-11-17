import IRComparison.Circuit.SharedGraph

namespace IRComparison.Circuit.Shared
open Pipelining

theorem bitValues_storage (g : Graph) (closed : ∀ n ∈ g, n.closed shape)
    (same : StorageAgreement shape r t) :
    bitValues wr r.data r.wires g = bitValues wr t.data t.wires g := by
  induction g with
  | nil => rfl
  | cons n g ih =>
    have hn := closed n (by simp)
    have tail := ih (fun n hn => closed n (by simp [hn]))
    simp only [bitValues,tail]
    congr 2
    cases n <;> simp only [Node.bitEval,Node.bitRaw,Node.eval]
    case input e => rw [Expr.bitEval_storage_congr e hn same]
    case memory a j => rw [same.arrays a hn]

theorem prepared_storage (e : Program) (closed : ExpressionStorage.closed shape e)
    (same : StorageAgreement shape r t) :
    (prepare wr e).program.fullEval r = (prepare wr e).program.fullEval t := by
  simp only [prepare_program,LocalRTL.compile_fullEval_correct,Program.bitEval,
    bitValues_storage e.graph closed same]

def preparedRead (wr : Nat → Interval) (e : Program) (r : Runtime) : Option Int :=
  (prepare wr e).program.fullEval r

theorem preparedRead_congr (e : Program) (closed : ExpressionStorage.closed shape e)
    (same : StorageAgreement shape r t) : preparedRead wr e r = preparedRead wr e t :=
  prepared_storage e closed same

theorem ready_storage_congr (a : Action Program) (hc : (a.node 0).inStorage shape)
    (same : StorageAgreement shape r t) : (ready a).evalWith (preparedRead wr) cap r = (ready a).evalWith (preparedRead wr) cap t := by
  cases a <;> simp only [Action.node,Node.inStorage] at hc
  case wire k e | assign k e => simp [ready,RTL.Test.evalWith,preparedRead_congr e hc.2.1 same]
  case store a j e => simp [ready,RTL.Test.evalWith,preparedRead_congr j hc.2.1 same,
    preparedRead_congr e hc.2.2.1 same,same.arrays a hc.1]
  case snapshot | erase | clear => rfl
  case send q e => simp [ready,RTL.Test.evalWith,preparedRead_congr e hc.2.1 same,same.queues q hc.1]
  case receive q k => simp [ready,RTL.Test.evalWith,same.queues q hc.1]

theorem writes_storage_congr (a : Action Program) (hc : (a.node 0).inStorage shape)
    (same : StorageAgreement shape r t) (pending : StorageAgreement shape p q) :
    StorageAgreement shape ((writes a).evalWith (preparedRead wr) cap r p) ((writes a).evalWith (preparedRead wr) cap t q) := by
  cases a <;> simp only [Action.node,Node.inStorage] at hc
  case wire k e | assign k e =>
    simp only [writes,RTL.Statement.evalWith,RTL.Scalar.evalWith,RTL.Register.write,
      preparedRead_congr e hc.2.1 same]
    first | exact pending.setWire | exact pending.setReg
  case store a j e =>
    simp only [writes,RTL.Statement.evalWith,RTL.MemoryRhs.evalWith,preparedRead_congr j hc.2.1 same,
      preparedRead_congr e hc.2.2.1 same,same.arrays a hc.1]
    exact pending.setArray
  case snapshot a b =>
    simp only [writes,RTL.Statement.evalWith,RTL.MemoryRhs.evalWith,same.arrays b hc.2.1]
    exact pending.setArray
  case erase => exact pending.setArray
  case clear => exact pending.setQueue
  case send q e =>
    simp only [writes,RTL.Statement.evalWith,RTL.QueueRhs.evalWith,preparedRead_congr e hc.2.1 same,
      same.queues q hc.1]
    exact pending.setQueue
  case receive q k =>
    simp only [writes,RTL.Statement.evalWith,RTL.Scalar.evalWith,RTL.QueueRhs.evalWith,RTL.Register.write,same.queues q hc.1]
    exact pending.setWire.setQueue

theorem lowerClock_storage_congr (next : Nat) (as : List (Action Program))
    (hc : ∀ a ∈ as, (a.node 0).inStorage shape) (same : StorageAgreement shape r t) :
    StorageAgreement shape ((lowerClock next as).evalWith (preparedRead wr) cap r r) ((lowerClock next as).evalWith (preparedRead wr) cap t t) := by
  have test : (allReady as).evalWith (preparedRead wr) cap r = (allReady as).evalWith (preparedRead wr) cap t := by
    induction as with
    | nil => rfl
    | cons a as ih => simp only [allReady,RTL.Test.evalWith,
        ready_storage_congr a (hc a (by simp)) same,ih (fun a ha => hc a (by simp [ha]))]
  have body : ∀ p q, StorageAgreement shape p q →
      StorageAgreement shape ((allWrites as).evalWith (preparedRead wr) cap r p) ((allWrites as).evalWith (preparedRead wr) cap t q) := by
    clear test
    induction as with
    | nil => exact fun _ _ h => h
    | cons a as ih =>
      intro p q h
      exact ih (fun a ha => hc a (by simp [ha])) _ _ (writes_storage_congr a (hc a (by simp)) same h)
  simp only [lowerClock,RTL.Statement.evalWith,test]
  split
  · exact (body r t same).setPC
  · exact same.fault


end IRComparison.Circuit.Shared
