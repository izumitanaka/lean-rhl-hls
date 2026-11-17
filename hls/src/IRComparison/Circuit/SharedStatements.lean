import IRComparison.Circuit.SharedEmitInto

namespace IRComparison.Circuit
open SystemVerilog

namespace Shared

/-- Internal output adapter, not a new source language or clocked IR. Bounds
are retained from the same graph traversal that produces local RTL nodes. -/
structure Prepared where
  program : LocalRTL.Program
  bounds : Interval

def prepare (wr : Nat → Interval) (p : Program) : Prepared :=
  let lowered := LocalRTL.lowerGraph wr p.graph
  ⟨⟨lowered.code,p.result⟩,bound lowered.ranges p.result⟩

theorem lowerGraph_ranges (wr : Nat → Interval) (g : Graph) :
    (LocalRTL.lowerGraph wr g).ranges = ranges wr g := by
  induction g with
  | nil => rfl
  | cons n g ih => simp [LocalRTL.lowerGraph,ranges,ih]

theorem prepare_program (wr : Nat → Interval) (p : Program) :
    (prepare wr p).program = LocalRTL.compile wr p := rfl

theorem prepare_bounds (wr : Nat → Interval) (p : Program) :
    (prepare wr p).bounds = p.range wr := by
  simp [prepare,Program.range,lowerGraph_ranges]

theorem prepare_correct (p : Program) (hb : InputsBound r.data r.wires wr) :
    (prepare wr p).program.fullEval r = p.eval r.data r.wires := by
  rw [prepare_program,LocalRTL.compile_fullEval_correct]
  exact p.bitEval_correct hb

theorem prepare_range_correct (p : Program) (hb : InputsBound r.data r.wires wr)
    (value : (prepare wr p).program.fullEval r = some v) :
    (prepare wr p).bounds.Contains v := by
  rw [prepare_bounds]
  exact p.range_correct hb ((prepare_correct p hb).symm.trans value)

/-- Preparing expressions does not change a clock's nonblocking state updates.
The existing polymorphic RTL statement semantics is reused unchanged. -/
theorem prepare_statement_correct (s : RTL.Statement Program)
    (hb : InputsBound old.data old.wires wr) (cap : Nat → Nat) (pending : Runtime) :
    (s.mapExpressions (prepare wr)).evalWith (fun e => e.program.fullEval) cap old pending =
      s.evalWith (fun e r => e.eval r.data r.wires) cap old pending := by
  have tests : ∀ t : RTL.Test Program,
      (t.mapExpressions (prepare wr)).evalWith (fun e => e.program.fullEval) cap old =
        t.evalWith (fun e r => e.eval r.data r.wires) cap old := by
    intro t
    induction t <;> simp_all [RTL.Test.mapExpressions,RTL.Test.evalWith,prepare_correct _ hb]
  induction s generalizing pending with
  | skip => rfl
  | assign target rhs =>
    cases rhs <;> simp [RTL.Statement.mapExpressions,RTL.Statement.evalWith,
      RTL.Scalar.mapExpressions,RTL.Scalar.evalWith,prepare_correct _ hb]
  | memory target rhs =>
    cases rhs <;> simp [RTL.Statement.mapExpressions,RTL.Statement.evalWith,
      RTL.MemoryRhs.mapExpressions,RTL.MemoryRhs.evalWith,prepare_correct _ hb]
  | queue target rhs =>
    cases rhs <;> simp [RTL.Statement.mapExpressions,RTL.Statement.evalWith,
      RTL.QueueRhs.mapExpressions,RTL.QueueRhs.evalWith,prepare_correct _ hb]
  | seq a b ha hb => simp [RTL.Statement.mapExpressions,RTL.Statement.evalWith,ha,hb]
  | branch c a b ha hb => simp [RTL.Statement.mapExpressions,RTL.Statement.evalWith,tests,ha,hb]

instance : ExpressionCode Prepared where
  emit a p := NetEmission.into a p.program
  bounds := Prepared.bounds

end Shared

/-- Allows both renderers to share a declaration sequence during migration.
No runtime expression expansion is required for the shared alternative. -/
instance [ExpressionCode α] [ExpressionCode β] : ExpressionCode (Sum α β) where
  emit a
    | .inl e => ExpressionCode.emit a e
    | .inr e => ExpressionCode.emit a e
  bounds
    | .inl e => ExpressionCode.bounds e
    | .inr e => ExpressionCode.bounds e

namespace Shared.NetEmission

theorem into_preserves (a : Artifact) (p : LocalRTL.Program) : Circuit.Preserves (into a p) :=
  preserves_map _ Pair.signal (intoPair_builds a p).preserves

theorem shared_statement_preserves (a : Artifact) (s : RTL.Statement Shared.Prepared) :
    Circuit.Preserves (statementCode a s) :=
  preserves_statementCodeWith a (fun p => into_preserves a p.program) s

theorem mixed_statement_preserves (a : Artifact) (s : RTL.Statement (Sum RTL.Combinational Shared.Prepared)) :
    Circuit.Preserves (statementCode a s) := by
  apply preserves_statementCodeWith a ?_ s
  intro e
  cases e with
  | inl e => exact preserves_expression a e
  | inr e => exact into_preserves a e.program

/-- Module assembly reuses the production control, memory, FIFO and interface
writer. SharedGraph uses this adapter in the normal structured HLS path. -/
def generateModule [ExpressionCode α] (a : Artifact) (outputs : List Nat) (cases : List (RTL.Statement α)) :
    Except String ModuleCode := do
  checkModuleArtifact a
  let (body,emission) ← (cases.mapM (statementCode a)).run {}
  checkReadOutputs a outputs
  return moduleCode a outputs body emission.text

theorem module_declarations_ordered [ExpressionCode α] (a : Artifact)
    {cases : List (RTL.Statement α)} {body : List SystemVerilog.Statement} {emission : Emission}
    (safe : ∀ e : α, Circuit.Preserves (ExpressionCode.emit a e))
    (generated : (cases.mapM (statementCode a)).run {} = .ok (body,emission)) :
    SystemVerilog.Ordered 0 emission.text.toList :=
  ((preserves_mapM (statementCode a) cases (preserves_statementCodeWith a safe))
    {} Emission.empty_wellFormed body emission generated).1.ordered

theorem generateModule_components [ExpressionCode α] (a : Artifact)
    {cases : List (RTL.Statement α)}
    (generated : generateModule a outputs cases = .ok result) :
    ∃ body emission, (cases.mapM (statementCode a)).run {} = .ok (body,emission) ∧
      result = moduleCode a outputs body emission.text := by
  unfold generateModule at generated
  cases hc : checkModuleArtifact a <;> simp [hc,bind,Except.bind] at generated
  cases hg : (cases.mapM (statementCode a)).run {} <;> simp [hg,bind,Except.bind] at generated
  cases hp : checkReadOutputs a outputs <;> simp [hp,pure,Except.pure] at generated
  exact ⟨_,_,rfl,generated.symm⟩

/-- Full module serialization reuses the production printer/parser theorem.
This theorem is the text round-trip component; SharedGraphRun supplies
multiple-clock state refinement and SharedCompiler connects the source. -/
theorem generateModule_text [ExpressionCode α] (a : Artifact)
    {cases : List (RTL.Statement α)}
    (generated : generateModule a outputs cases = .ok result)
    (cycles : Nat) (r : RTL.InterfaceState a.storageShape) :
    (Concrete.parseModule result.text).bind (fun parsed => parsed.run a.storageShape cycles r) =
      result.run a.storageShape cycles r := by
  obtain ⟨body,emission,_,rfl⟩ := generateModule_components a generated
  exact printModule_run _ (moduleCode_storage _ _ _ _).positive rfl _ _ _

end Shared.NetEmission
end IRComparison.Circuit
