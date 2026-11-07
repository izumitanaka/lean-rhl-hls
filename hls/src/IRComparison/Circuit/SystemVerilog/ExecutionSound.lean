import IRComparison.Circuit.SystemVerilog.BankCodeSound

namespace IRComparison.Circuit.SystemVerilog

/-- Conditions required by concrete writes on the path actually taken.
They are supplied by the existing lowering and its guards, not by a new
source-language acceptance check. -/
def StatementReady (shape : StorageShape) (runtime : Runtime) (capacity : Nat → Nat) :
    RTL.Statement RTL.Combinational → Prop
  | .skip => True
  | .assign _ rhs => ScalarReady shape runtime rhs
  | .memory id (.copy source) => id < shape.memories ∧ source < shape.memories
  | .memory id (.set _ j v) => id < shape.memories ∧ j.valid.eval runtime = true ∧
      v.valid.eval runtime = true ∧ 0 ≤ j.value.eval runtime ∧
      (j.value.eval runtime).toNat < (runtime.data.arrays id).size
  | .memory _ .empty => True
  | .queue q (.append _ v) => q < shape.queues ∧ v.valid.eval runtime = true ∧ (runtime.queues q).length < capacity q
  | .queue q (.tail _) => q < shape.queues ∧ runtime.queues q ≠ []
  | .queue _ .empty => True
  | .seq u v => StatementReady shape runtime capacity u ∧ StatementReady shape runtime capacity v
  | .branch c u v => TestReady shape runtime capacity c ∧
      (c.evalWith RTL.Combinational.eval capacity runtime = true → StatementReady shape runtime capacity u) ∧
      (c.evalWith RTL.Combinational.eval capacity runtime = false → StatementReady shape runtime capacity v)

@[simp] theorem address_true (e : RTL.Combinational) (r : Runtime) :
    (RTL.Test.address n e).evalWith RTL.Combinational.eval cap r = true ↔
      e.valid.eval r = true ∧ 0 ≤ e.value.eval r ∧ (e.value.eval r).toNat < (r.data.arrays n).size := by
  cases valid : e.valid.eval r <;> simp [RTL.Test.evalWith,RTL.Combinational.eval,valid]

theorem lowerNode_ready (wr : Nat → Interval) (runtime : Runtime) (capacity : Nat → Nat)
    (node : Node) (closed : node.inStorage shape) :
    StatementReady shape runtime capacity ((RTL.lowerNode node).mapExpressions (RTL.combinational wr)) := by
  cases node <;>
    simp_all [Node.inStorage,StorageShape.hasMemory,RTL.lowerNode,RTL.halt,RTL.advance,RTL.guarded,RTL.fault,
      RTL.Statement.mapExpressions,RTL.Test.mapExpressions,RTL.Scalar.mapExpressions,
      RTL.MemoryRhs.mapExpressions,RTL.QueueRhs.mapExpressions,
      StatementReady,ScalarReady,TestReady]
  all_goals simp_all [RTL.Test.evalWith]
  rename_i bank j v next
  cases flag : (RTL.combinational wr j).valid.eval runtime <;> simp [RTL.Combinational.eval,flag]
  exact fun nonnegative inside _ => ⟨nonnegative,inside⟩

theorem artifact_ready (a : Artifact) (certificate : StorageCertificate a) (runtime : Runtime)
    (member : body ∈ (RTL.artifactProgram a).cases.toList) :
    StatementReady a.storageShape runtime a.machine.capacity body := by
  simp only [RTL.artifactProgram,RTL.lowerCombinational,Array.toList_map,List.mem_map] at member
  obtain ⟨node,member,rfl⟩ := member
  exact lowerNode_ready _ runtime a.machine.capacity node (certificate.closed node member)

/-- The complete statement generator is executable on every guarded path.
This theorem composes the exact atomic-update results; it does not assume
successful evaluation of the generated clocked program. -/
theorem statementCode_total (a : Artifact) (r : FiniteRuntime a.storageShape)
    (final : Emission) (values : Array Int) (body : RTL.Statement RTL.Combinational)
    (closed : StatementReferences a.storageShape body)
    (ready : StatementReady a.storageShape r.decode a.machine.capacity body)
    (good : before.WellFormed) (success : statementCode a body before = .ok (code,after))
    (grows : after.Extends final)
    (meaning : CacheMeaning ((environment a r final.text #[]).withTemporaries values) r.decode final)
    (pending : Store) :
    ∃ writes, code.eval ((environment a r final.text #[]).withTemporaries values) pending = some writes := by
  induction body generalizing before after code pending with
  | skip =>
    obtain ⟨rfl,_⟩ := pure_success Statement.skip success
    exact ⟨pending,rfl⟩
  | assign target rhs =>
    exact ⟨_,statementCode_assign_correct a r final values target rhs closed ready good success grows meaning pending⟩
  | memory id rhs =>
    cases rhs with
    | empty => exact ⟨_,statementCode_erase_correct a success _ pending⟩
    | copy source => exact ⟨_,statementCode_copy_correct a r final values ready.1 ready.2 success pending⟩
    | set source j v =>
      exact ⟨_,statementCode_store_correct a r final values j v ready.1 closed.1 closed.2
        ready.2.2.2.1 ready.2.2.2.2 good success grows meaning pending⟩
  | queue q rhs =>
    cases rhs with
    | empty => exact ⟨_,statementCode_clear_correct a success _ pending⟩
    | append source v => exact ⟨_,statementCode_send_correct a r final values v ready.1 ready.2.2 closed good success grows meaning pending⟩
    | tail source => exact ⟨_,statementCode_tail_correct a r final values ready.1 ready.2 success pending⟩
  | seq u v ihU ihV =>
    rw [statementCode] at success
    obtain ⟨first,middle,firstStep,rest⟩ := bind_success _ _ success
    obtain ⟨second,lastStep,rfl⟩ := map_success _ _ rest
    obtain ⟨middleGood,_,_⟩ := preserves_statementCode a u before good first middle firstStep
    obtain ⟨_,more,_⟩ := preserves_statementCode a v middle middleGood second after lastStep
    obtain ⟨midWrites,firstEval⟩ := ihU closed.1 ready.1 good firstStep (more.trans grows) pending
    obtain ⟨writes,lastEval⟩ := ihV closed.2 ready.2 middleGood lastStep grows midWrites
    exact ⟨writes,by rw [Statement.seq_eval,firstEval]; exact lastEval⟩
  | branch test yes no ihYes ihNo =>
    rw [statementCode] at success
    obtain ⟨condition,s0,compiledTest,rest0⟩ := bind_success _ _ success
    obtain ⟨yesCode,s1,compiledYes,rest1⟩ := bind_success _ _ rest0
    obtain ⟨noCode,compiledNo,rfl⟩ := map_success _ _ rest1
    obtain ⟨s0Good,_,_⟩ := preserves_testCode a test before good condition s0 compiledTest
    obtain ⟨s1Good,more,_⟩ := preserves_statementCode a yes s0 s0Good yesCode s1 compiledYes
    obtain ⟨_,latest,_⟩ := preserves_statementCode a no s1 s1Good noCode after compiledNo
    have testMeaning := testCode_correct a r final values test closed.1 ready.1 good compiledTest
      (more.trans (latest.trans grows)) meaning
    rw [Statement.branch_boolean testMeaning]
    cases taken : test.evalWith RTL.Combinational.eval a.machine.capacity r.decode with
    | true => exact ihYes closed.2.1 (ready.2.1 taken) s0Good compiledYes (latest.trans grows) pending
    | false => exact ihNo closed.2.2 (ready.2.2 taken) s1Good compiledNo grows pending

theorem statementCodes_total (a : Artifact) (r : FiniteRuntime a.storageShape)
    (final : Emission) (values : Array Int) (bodies : List (RTL.Statement RTL.Combinational))
    (closed : ∀ body ∈ bodies, StatementReferences a.storageShape body)
    (ready : ∀ body ∈ bodies, StatementReady a.storageShape r.decode a.machine.capacity body)
    (good : before.WellFormed) (success : bodies.mapM (statementCode a) before = .ok (codes,after))
    (grows : after.Extends final)
    (meaning : CacheMeaning ((environment a r final.text #[]).withTemporaries values) r.decode final) :
    ∀ code ∈ codes, ∀ pending, ∃ writes,
      code.eval ((environment a r final.text #[]).withTemporaries values) pending = some writes := by
  induction bodies generalizing before after codes with
  | nil =>
    obtain ⟨rfl,_⟩ := pure_success ([] : List Statement) success
    simp
  | cons body bodies ih =>
    rw [List.mapM_cons] at success
    obtain ⟨code,middle,compiled,rest⟩ := bind_success _ _ success
    obtain ⟨tail,compiledTail,rfl⟩ := return_success (bodies.mapM (statementCode a)) (fun tail => code::tail) rest
    obtain ⟨middleGood,_,_⟩ := preserves_statementCode a body before good code middle compiled
    have more : middle.Extends after :=
      (preserves_mapM (statementCode a) bodies (preserves_statementCode a)
        middle middleGood tail after compiledTail).2.1
    intro selected member pending
    rcases List.mem_cons.mp member with rfl | member
    · exact statementCode_total a r final values body (closed body (by simp)) (ready body (by simp))
        good compiled (more.trans grows) meaning pending
    · exact ih (fun b hb => closed b (by simp [hb])) (fun b hb => ready b (by simp [hb]))
        middleGood compiledTail grows selected member pending

/-- For every accepted layout and arbitrary finite physical state, all
generated continuous wires and every selected compute case execute. No
successful wire/statement-evaluation premise or zero-padding assumption is
needed. Exact atomic effects are proved in ScalarSound and BankCodeSound;
whole-clock state refinement is a distinct subsequent theorem. -/
theorem generateCode_execution_total (a : Artifact) (certificate : StorageCertificate a)
    (r : FiniteRuntime a.storageShape)
    (generated : generateCode a = .ok (codes,emission)) :
    ∃ values, evaluateWires a r emission.text = some values ∧
      CacheMeaning ((environment a r emission.text #[]).withTemporaries values) r.decode emission ∧
      ∀ code ∈ codes, ∀ pending, ∃ writes,
        code.eval ((environment a r emission.text #[]).withTemporaries values) pending = some writes := by
  obtain ⟨values,evaluated,meaning⟩ := generateCode_total a certificate r generated
  refine ⟨values,evaluated,meaning,?_⟩
  apply statementCodes_total a r emission values (RTL.artifactProgram a).cases.toList
    ?_ (fun body member => artifact_ready a certificate r.decode member)
    Emission.empty_wellFormed generated (Emission.Extends.refl _) meaning
  intro body member
  simp only [RTL.artifactProgram,RTL.lowerCombinational,Array.toList_map,List.mem_map] at member
  obtain ⟨node,member,rfl⟩ := member
  exact lowerNode_references _ node (certificate.closed node member)

end IRComparison.Circuit.SystemVerilog
