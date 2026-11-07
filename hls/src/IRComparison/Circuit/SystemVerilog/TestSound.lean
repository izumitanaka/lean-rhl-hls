import IRComparison.Circuit.SystemVerilog.BooleanSound
import IRComparison.Circuit.RTL.ExpressionMapping
import IRComparison.Circuit.SystemVerilog.StatementEval

namespace IRComparison.Circuit.SystemVerilog

/-- Conditions at an executed test. In particular `nonzero` reads a value
only inside the validity guard already emitted by RTL.lowerNode. This is a
path condition of generated RTL, not a new source-language restriction. -/
def TestReady (shape : StorageShape) (runtime : Runtime) (capacity : Nat → Nat) : RTL.Test RTL.Combinational → Prop
  | .nonzero e => e.valid.eval runtime = true
  | .room q | .nonempty q => q < shape.queues
  | .and u v => TestReady shape runtime capacity u ∧
      (u.evalWith RTL.Combinational.eval capacity runtime = true → TestReady shape runtime capacity v)
  | _ => True

theorem finite_used (a : Artifact) (r : FiniteRuntime a.storageShape) (final : Emission) (values : Array Int)
    (inside : q < a.storageShape.queues) :
    let env := (environment a r final.text #[]).withTemporaries values
    env.type (.used q) = ⟨bits (a.machine.capacity q),false⟩ ∧
    env.scalar (.used q) = some ((r.decode.queues q).length : Int) ∧
    (r.decode.queues q).length < 2^bits (a.machine.capacity q) := by
  refine ⟨rfl,?_,?_⟩
  · simp [Environment.withTemporaries,environment,environmentFor,FiniteRuntime.decode,inside,WordBuffer.contents]
  · have used : (r.queues ⟨q,inside⟩).used.val < a.machine.capacity q+1 := (r.queues ⟨q,inside⟩).used.isLt
    have := bits_fits (a.machine.capacity q)
    simp only [FiniteRuntime.decode,inside,↓reduceDIte,WordBuffer.contents,Array.length_toList,Array.size_ofFn]
    omega

/-- The real condition generator preserves value-validity checks, addresses,
FIFO capacity/emptiness and short-circuit conjunction on executed paths. -/
theorem testCode_correct (a : Artifact) (r : FiniteRuntime a.storageShape) (final : Emission) (values : Array Int)
    (test : RTL.Test RTL.Combinational) (closed : TestReferences a.storageShape test)
    (ready : TestReady a.storageShape r.decode a.machine.capacity test)
    (good : before.WellFormed) (success : testCode a test before = .ok (expr,after))
    (grows : after.Extends final)
    (meaning : CacheMeaning ((environment a r final.text #[]).withTemporaries values) r.decode final) :
    BooleanMeaning ((environment a r final.text #[]).withTemporaries values) expr
      (test.evalWith RTL.Combinational.eval a.machine.capacity r.decode) := by
  induction test generalizing before after expr with
  | valid e =>
    rw [testCode] at success
    obtain ⟨signal,compiled,rfl⟩ := map_success _ _ success
    have h := (expression_correct a r final values e closed good compiled grows meaning).2
    cases flag : e.valid.eval r.decode <;> simpa [RTL.Test.evalWith,RTL.Combinational.eval,flag] using h
  | nonzero e =>
    rw [testCode] at success
    obtain ⟨signal,compiled,rfl⟩ := return_success (expression a e)
      (fun signal => Expr.binary .ne (.reference signal.name) (.integer 0)) success
    have h := (expression_correct a r final values e closed good compiled grows meaning).1
    have result := h.boolean_comparison (SignedMeaning.integer 0) (op:=.ne) rfl
      (result:=e.value.eval r.decode != 0) (by simp [arithmetic])
    simpa only [RTL.Test.evalWith,RTL.Combinational.eval,show e.valid.eval r.decode = true from ready,↓reduceIte,
      Option.getD_some] using result
  | address n e =>
    rw [testCode] at success
    obtain ⟨size,middle,found,remaining⟩ := bind_success _ _ success
    obtain ⟨known,rfl⟩ := lift_success (memorySize a n) found
    obtain ⟨signal,compiled,rfl⟩ := return_success (expression a e)
      (fun j => Expr.binary .and j.valid (.binary .and (.binary .ge (.reference j.name) (.integer 0))
        (.binary .lt (.reference j.name) (.unsigned (.reference (.length n)))))) remaining
    obtain ⟨data,valid⟩ := expression_correct a r final values e closed.2 good compiled grows meaning
    have address := address_meaning data (finite_length_meaning a r final.text values closed.1 known)
    have result := valid.and address
    cases flag : e.valid.eval r.decode <;> simpa [RTL.Test.evalWith,RTL.Combinational.eval,flag] using result
  | room q =>
    rw [testCode] at success
    obtain ⟨ignored,middle,required,remaining⟩ := bind_success _ _ success
    obtain ⟨rfl,_⟩ := pure_success (Expr.binary .lt (.reference (.used q)) (.integer (a.machine.capacity q))) remaining
    obtain ⟨typed,stored,fits⟩ := finite_used a r final values ready
    exact count_lt_integer typed stored fits (a.machine.capacity q)
  | nonempty q =>
    rw [testCode] at success
    obtain ⟨ignored,middle,required,remaining⟩ := bind_success _ _ success
    obtain ⟨rfl,_⟩ := pure_success (Expr.binary .lt (.integer 0) (.reference (.used q))) remaining
    obtain ⟨typed,stored,fits⟩ := finite_used a r final values ready
    have result := integer_lt_count typed stored fits 0
    cases queue : r.decode.queues q <;> simpa [RTL.Test.evalWith,queue] using result
  | and u v ihU ihV =>
    rw [testCode] at success
    obtain ⟨left,middle,first,remaining⟩ := bind_success _ _ success
    obtain ⟨right,last,rfl⟩ := map_success _ _ remaining
    obtain ⟨middleGood,_,_⟩ := preserves_testCode a u before good left middle first
    obtain ⟨_,more,_⟩ := preserves_testCode a v middle middleGood right after last
    exact (ihU closed.1 ready.1 good first (more.trans grows)).and_lazy
      (fun taken => ihV closed.2 (ready.2 taken) middleGood last grows)


@[simp] theorem combinational_isSome (e : RTL.Combinational) (runtime : Runtime) :
    (e.eval runtime).isSome = e.valid.eval runtime := by
  cases flag : e.valid.eval runtime <;> simp [RTL.Combinational.eval,flag]

/-- Readiness only along executed branches. This follows from the existing
validity guards; branches that are not taken need no value-definedness premise. -/
def StatementTestsReady (shape : StorageShape) (runtime : Runtime) (capacity : Nat → Nat) :
    RTL.Statement RTL.Combinational → Prop
  | .seq u v => StatementTestsReady shape runtime capacity u ∧ StatementTestsReady shape runtime capacity v
  | .branch c u v => TestReady shape runtime capacity c ∧
      (c.evalWith RTL.Combinational.eval capacity runtime = true → StatementTestsReady shape runtime capacity u) ∧
      (c.evalWith RTL.Combinational.eval capacity runtime = false → StatementTestsReady shape runtime capacity v)
  | _ => True

theorem lowerNode_tests_ready (wr : Nat → Interval) (runtime : Runtime) (capacity : Nat → Nat)
    (node : Node) (closed : node.inStorage shape) :
    StatementTestsReady shape runtime capacity ((RTL.lowerNode node).mapExpressions (RTL.combinational wr)) := by
  cases node <;>
    simp_all [Node.inStorage,RTL.lowerNode,RTL.halt,RTL.advance,RTL.guarded,RTL.fault,
      RTL.Statement.mapExpressions,RTL.Test.mapExpressions,RTL.Scalar.mapExpressions,
      RTL.MemoryRhs.mapExpressions,RTL.QueueRhs.mapExpressions,
      StatementTestsReady,TestReady,RTL.Test.evalWith]

/-- The original storage certificate and lowering provide all executed-test
premises used above. No extra acceptance check is attached to the source. -/
theorem artifact_tests_ready (a : Artifact) (certificate : StorageCertificate a) (runtime : Runtime)
    (member : body ∈ (RTL.artifactProgram a).cases.toList) :
    StatementTestsReady a.storageShape runtime a.machine.capacity body := by
  simp only [RTL.artifactProgram,RTL.lowerCombinational,Array.toList_map,List.mem_map] at member
  obtain ⟨node,member,rfl⟩ := member
  exact lowerNode_tests_ready _ runtime a.machine.capacity node (certificate.closed node member)


theorem Statement.branch_boolean (condition : BooleanMeaning env test b) (yes no : Statement) (pending : Store) :
    (Statement.branch test yes no).eval env pending =
      if b then yes.eval env pending else no.eval env pending := by
  rw [Statement.eval]
  simp only [condition.evaluated,bind,Option.bind,truth_integer]
  cases b <;> rfl

/-- The branch selected by an actual generated statement is exactly the
reference RTL branch. The substatements remain the compiler's own results;
this theorem does not assume their pending writes are already correct. -/
theorem statementCode_branch_decision (a : Artifact) (r : FiniteRuntime a.storageShape)
    (final : Emission) (values : Array Int) (test : RTL.Test RTL.Combinational)
    (yes no : RTL.Statement RTL.Combinational) (closed : TestReferences a.storageShape test)
    (ready : TestReady a.storageShape r.decode a.machine.capacity test)
    (good : before.WellFormed)
    (success : statementCode a (.branch test yes no) before = .ok (code,after))
    (grows : after.Extends final)
    (meaning : CacheMeaning ((environment a r final.text #[]).withTemporaries values) r.decode final) :
    ∃ yesCode noCode middle last,
      statementCode a yes middle = .ok (yesCode,last) ∧
      statementCode a no last = .ok (noCode,after) ∧
      ∀ pending, code.eval ((environment a r final.text #[]).withTemporaries values) pending =
        if test.evalWith RTL.Combinational.eval a.machine.capacity r.decode then
          yesCode.eval ((environment a r final.text #[]).withTemporaries values) pending
        else noCode.eval ((environment a r final.text #[]).withTemporaries values) pending := by
  rw [statementCode] at success
  obtain ⟨condition,middle,first,remaining⟩ := bind_success _ _ success
  obtain ⟨yesCode,last,second,remaining⟩ := bind_success _ _ remaining
  obtain ⟨noCode,third,rfl⟩ := map_success _ _ remaining
  obtain ⟨middleGood,_,_⟩ := preserves_testCode a test before good condition middle first
  obtain ⟨lastGood,more,_⟩ := preserves_statementCode a yes middle middleGood yesCode last second
  obtain ⟨_,latest,_⟩ := preserves_statementCode a no last lastGood noCode after third
  have conditionMeaning := testCode_correct a r final values test closed ready good first
    (more.trans (latest.trans grows)) meaning
  exact ⟨yesCode,noCode,middle,last,second,third,fun pending => Statement.branch_boolean conditionMeaning _ _ pending⟩

end IRComparison.Circuit.SystemVerilog
