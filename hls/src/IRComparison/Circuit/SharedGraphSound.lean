import IRComparison.Circuit.SharedStorage

namespace IRComparison.Circuit.Shared
open Pipelining SystemVerilog

theorem statement_prepared (s : RTL.Statement Program) :
    (s.mapExpressions (prepare wr)).evalWith (fun p => p.program.fullEval) cap old pending =
      s.evalWith (preparedRead wr) cap old pending :=
  RTL.Statement.map_evalWith _ _ _ (fun _ => rfl) s

theorem node_statement_correct (n : ClockNode Program) (hb : InputsBound r.data r.wires wr) :
    n.statement.evalWith (preparedRead wr) cap r r = n.eval cap r := by
  have eq (s : RTL.Statement Program) : s.evalWith (preparedRead wr) cap r r =
      s.evalWith oldRead cap r r := by
    rw [← statement_prepared,prepare_statement_correct s hb]
    rfl
  rw [eq]
  cases n with
  | batch as next => exact lowerClock_correct next as r
  | branch e yes no =>
    cases he : e.eval r.data r.wires <;>
      simp [ClockNode.statement,RTL.lowerNode,RTL.guarded,RTL.advance,RTL.fault,
        RTL.Statement.evalWith,RTL.Test.evalWith,RTL.Scalar.evalWith,RTL.Register.write,
        oldRead,ClockNode.eval,he]
    split <;> rfl
  | jump | halt => rfl

theorem node_references (n : ClockNode Program) (hc : n.closed shape) :
    StatementReferences shape (n.statement.mapExpressions (prepare wr)) := by
  cases n with
  | batch as next => exact lowerClock_references next as hc
  | branch e yes no =>
    simp [ClockNode.statement,RTL.lowerNode,RTL.guarded,RTL.advance,RTL.fault,
      RTL.Statement.mapExpressions,RTL.Test.mapExpressions,RTL.Scalar.mapExpressions,
      StatementReferences,TestReferences,ScalarReferences,prepare_references e hc.1]
  | jump | halt => trivial

theorem node_ready (n : ClockNode Program) (hc : n.closed shape) :
    StatementReady shape old cap (n.statement.mapExpressions (prepare wr)) := by
  cases n with
  | batch as next => exact lowerClock_ready next as hc
  | branch e yes no =>
    simp [ClockNode.statement,RTL.lowerNode,RTL.guarded,RTL.advance,RTL.fault,
      RTL.Statement.mapExpressions,RTL.Test.mapExpressions,RTL.Scalar.mapExpressions,
      StatementReady,TestReady,ScalarReady,RTL.Test.evalWith]
  | jump | halt => trivial

theorem node_frame (n : ClockNode Program) (hc : n.closed shape) (hd : n.distinct) :
    StatementFrame shape old cap (n.statement.mapExpressions (prepare wr)) old := by
  cases n with
  | batch as next => exact lowerClock_frame next as hc hd
  | branch | jump | halt =>
    simp [ClockNode.statement,RTL.lowerNode,RTL.guarded,RTL.advance,RTL.fault,RTL.halt,
      RTL.Statement.mapExpressions,RTL.Test.mapExpressions,RTL.Scalar.mapExpressions,
      StatementFrame,RTL.Scalar.evalWith]

theorem node_storage_congr (n : ClockNode Program) (hc : n.closed shape)
    (same : StorageAgreement shape r t) :
    StorageAgreement shape (n.statement.evalWith (preparedRead wr) cap r r)
      (n.statement.evalWith (preparedRead wr) cap t t) := by
  cases n with
  | batch as next => exact lowerClock_storage_congr next as hc same
  | jump => exact same.setPC
  | halt => exact same.stop
  | branch e yes no =>
    have eq := preparedRead_congr e hc.1 same (wr := wr)
    simp only [ClockNode.statement,RTL.lowerNode,RTL.guarded,RTL.Statement.evalWith,
      RTL.Test.evalWith,eq]
    split
    · split <;> exact same.setPC
    · exact same.fault

end IRComparison.Circuit.Shared
