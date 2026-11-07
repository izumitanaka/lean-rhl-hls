import IRComparison.Circuit.SystemVerilog.StateSound

namespace IRComparison.Circuit.SystemVerilog

/-- Frame facts at an executed operation. Whole-array RHSs read the old
state, whereas emitted cell writes accumulate pending updates. The actual
lowering performs one bank operation per clock, so its pending bank still
equals the old bank whenever an incremental update occurs. -/
def StatementFrame (shape : StorageShape) (old : Runtime) (capacity : Nat → Nat) :
    RTL.Statement RTL.Combinational → Runtime → Prop
  | .assign target rhs,_ => target = .pc → 0 ≤ rhs.evalWith RTL.Combinational.eval old
  | .memory id (.copy source),_ => shape.memorySize source ≤ shape.memorySize id
  | .memory id (.set source _ _),pending => source = id ∧ pending.data.arrays id = old.data.arrays source
  | .queue q (.append source _),pending => source = q ∧ pending.queues q = old.queues source
  | .queue q (.tail source),_ => source = q
  | .seq u v,pending => StatementFrame shape old capacity u pending ∧
      StatementFrame shape old capacity v (u.evalWith RTL.Combinational.eval capacity old pending)
  | .branch c u v,pending =>
      if c.evalWith RTL.Combinational.eval capacity old then StatementFrame shape old capacity u pending
      else StatementFrame shape old capacity v pending
  | _,_ => True

theorem lowerNode_frame (wr : Nat → Interval) (runtime : Runtime) (capacity : Nat → Nat)
    (node : Node) (closed : node.inStorage shape) :
    StatementFrame shape runtime capacity ((RTL.lowerNode node).mapExpressions (RTL.combinational wr)) runtime := by
  cases node <;>
    simp_all [Node.inStorage,RTL.lowerNode,RTL.halt,RTL.advance,RTL.guarded,RTL.fault,
      RTL.Statement.mapExpressions,RTL.Test.mapExpressions,RTL.Scalar.mapExpressions,
      RTL.MemoryRhs.mapExpressions,RTL.QueueRhs.mapExpressions,StatementFrame,RTL.Scalar.evalWith]

/-- General state refinement of the actual statement output pass. The
path/frame premises are separately derived for every lowered machine node;
they are not additional checks imposed on source programs. -/
def BusyMatches (store : Store) (runtime : Runtime) : Prop :=
  store.scalar .busy = some (if runtime.done then 0 else 1)

theorem statementCode_refines_control (a : Artifact) (r : FiniteRuntime a.storageShape)
    (final : Emission) (values : Array Int) (body : RTL.Statement RTL.Combinational)
    (closed : StatementReferences a.storageShape body)
    (ready : StatementReady a.storageShape r.decode a.machine.capacity body)
    (good : before.WellFormed) (success : statementCode a body before = .ok (code,after))
    (grows : after.Extends final)
    (meaning : CacheMeaning ((environment a r final.text #[]).withTemporaries values) r.decode final)
    (pending : Store) (logical : Runtime)
    (related : pending.Matches ((environment a r final.text #[]).withTemporaries values) a.storageShape logical)
    (frame : StatementFrame a.storageShape r.decode a.machine.capacity body logical) :
    ∃ writes, code.eval ((environment a r final.text #[]).withTemporaries values) pending = some writes ∧
      writes.Matches ((environment a r final.text #[]).withTemporaries values) a.storageShape
        (body.evalWith RTL.Combinational.eval a.machine.capacity r.decode logical) ∧
      (BusyMatches pending logical → BusyMatches writes
        (body.evalWith RTL.Combinational.eval a.machine.capacity r.decode logical)) := by
  have oldRelated := finite_store_matches a r final values
  induction body generalizing before after code pending logical with
  | skip =>
    obtain ⟨rfl,_⟩ := pure_success Statement.skip success
    exact ⟨pending,rfl,related,fun h => h⟩
  | assign target rhs =>
    refine ⟨_,statementCode_assign_correct a r final values target rhs closed ready good success grows meaning pending,
      related.writeRegister target _ frame,?_⟩
    cases target <;> simp [BusyMatches,Store.writeRegister,Store.setScalar,RTL.Statement.evalWith,
      RTL.Register.write,Runtime.setWire,State.set]
    all_goals first | exact fun h => h | (by_cases zero : rhs.evalWith RTL.Combinational.eval r.decode = 0 <;> simp [zero])
  | memory id rhs =>
    cases rhs with
    | empty => exact ⟨_,statementCode_erase_correct a success _ pending,related.erase,by simp [BusyMatches,Store.setScalar,RTL.Statement.evalWith,Runtime.setArray]; exact fun h => h⟩
    | copy source =>
      have sourceFit : (r.decode.data.arrays source).size ≤ a.storageShape.memorySize id := by
        have used : (r.arrays ⟨source,ready.2⟩).used.val < a.storageShape.memorySize source+1 := (r.arrays ⟨source,ready.2⟩).used.isLt
        simp only [FiniteRuntime.decode,ready.2,↓reduceDIte,WordBuffer.contents,Array.size_ofFn]
        change a.storageShape.memorySize source ≤ a.storageShape.memorySize id at frame
        omega
      exact ⟨_,statementCode_copy_correct a r final values ready.1 ready.2 success pending,
        related.copy oldRelated ready.2 sourceFit,by simp [BusyMatches,Store.setScalar,RTL.Statement.evalWith,Runtime.setArray]; exact fun h => h⟩
    | set source j v =>
      obtain ⟨same,bankFrame⟩ := frame
      subst source
      refine ⟨_,statementCode_store_correct a r final values j v ready.1 closed.1 closed.2
        ready.2.2.2.1 ready.2.2.2.2 good success grows meaning pending,?_,?_⟩
      · have updated := related.store ready.1 (j.value.eval r.decode).toNat (v.value.eval r.decode)
        simpa only [RTL.Statement.evalWith,RTL.MemoryRhs.evalWith,RTL.Combinational.eval,ready.2.1,ready.2.2.1,
          ↓reduceIte,Option.getD_some,bankFrame] using updated
      · simp [BusyMatches,Store.setCell,RTL.Statement.evalWith,Runtime.setArray]; exact fun h => h
  | queue q rhs =>
    cases rhs with
    | empty => exact ⟨_,statementCode_clear_correct a success _ pending,related.clear,by simp [BusyMatches,Store.setScalar,RTL.Statement.evalWith,Runtime.setQueue]; exact fun h => h⟩
    | append source v =>
      obtain ⟨same,bankFrame⟩ := frame
      subst source
      refine ⟨_,statementCode_send_correct a r final values v ready.1 ready.2.2 closed good success grows meaning pending,?_,?_⟩
      · have updated := related.push ready.1 (v.value.eval r.decode)
        simpa only [RTL.Statement.evalWith,RTL.QueueRhs.evalWith,RTL.Combinational.eval,ready.2.1,
          ↓reduceIte,Option.getD_some,bankFrame] using updated
      · simp [BusyMatches,Store.setScalar,Store.setCell,RTL.Statement.evalWith,Runtime.setQueue]; exact fun h => h
    | tail source =>
      change source = q at frame
      subst source
      have bound : (r.decode.queues q).length ≤ a.machine.capacity q := by
        have used : (r.queues ⟨q,ready.1⟩).used.val < a.storageShape.queueSize q+1 := (r.queues ⟨q,ready.1⟩).used.isLt
        simp only [FiniteRuntime.decode,ready.1,↓reduceDIte,WordBuffer.contents,Array.length_toList,Array.size_ofFn]
        exact Nat.le_of_lt_succ used
      exact ⟨_,statementCode_tail_correct a r final values ready.1 ready.2 success pending,related.shift oldRelated ready.1 bound,by simp [BusyMatches,Store.setScalar,RTL.Statement.evalWith,Runtime.setQueue]; exact fun h => h⟩
  | seq u v ihU ihV =>
    rw [statementCode] at success
    obtain ⟨first,middle,firstStep,rest⟩ := bind_success _ _ success
    obtain ⟨second,lastStep,rfl⟩ := map_success _ _ rest
    obtain ⟨middleGood,_,_⟩ := preserves_statementCode a u before good first middle firstStep
    obtain ⟨_,more,_⟩ := preserves_statementCode a v middle middleGood second after lastStep
    obtain ⟨midWrites,firstEval,midRelated,midBusy⟩ := ihU closed.1 ready.1 good firstStep (more.trans grows) pending logical related frame.1
    obtain ⟨writes,lastEval,lastRelated,lastBusy⟩ := ihV closed.2 ready.2 middleGood lastStep grows midWrites _ midRelated frame.2
    exact ⟨writes,by rw [Statement.seq_eval,firstEval]; exact lastEval,lastRelated,fun h => lastBusy (midBusy h)⟩
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
    | true =>
      simpa only [RTL.Statement.evalWith,taken,↓reduceIte] using ihYes closed.2.1 (ready.2.1 taken) s0Good compiledYes
        (latest.trans grows) pending logical related (by simpa only [StatementFrame,taken,↓reduceIte] using frame)
    | false =>
      simpa only [RTL.Statement.evalWith,taken,Bool.false_eq_true,↓reduceIte] using ihNo closed.2.2 (ready.2.2 taken) s1Good compiledNo
        grows pending logical related (by simpa only [StatementFrame,taken,Bool.false_eq_true,↓reduceIte] using frame)

theorem statementCode_refines (a : Artifact) (r : FiniteRuntime a.storageShape)
    (final : Emission) (values : Array Int) (body : RTL.Statement RTL.Combinational)
    (closed : StatementReferences a.storageShape body)
    (ready : StatementReady a.storageShape r.decode a.machine.capacity body)
    (good : before.WellFormed) (success : statementCode a body before = .ok (code,after))
    (grows : after.Extends final)
    (meaning : CacheMeaning ((environment a r final.text #[]).withTemporaries values) r.decode final)
    (pending : Store) (logical : Runtime)
    (related : pending.Matches ((environment a r final.text #[]).withTemporaries values) a.storageShape logical)
    (frame : StatementFrame a.storageShape r.decode a.machine.capacity body logical) :
    ∃ writes, code.eval ((environment a r final.text #[]).withTemporaries values) pending = some writes ∧
      writes.Matches ((environment a r final.text #[]).withTemporaries values) a.storageShape
        (body.evalWith RTL.Combinational.eval a.machine.capacity r.decode logical) := by
  obtain ⟨writes,executed,related,_⟩ := statementCode_refines_control a r final values body closed ready good success grows meaning pending logical related frame
  exact ⟨writes,executed,related⟩

theorem artifact_frame (a : Artifact) (certificate : StorageCertificate a) (runtime : Runtime)
    (member : body ∈ (RTL.artifactProgram a).cases.toList) :
    StatementFrame a.storageShape runtime a.machine.capacity body runtime := by
  simp only [RTL.artifactProgram,RTL.lowerCombinational,Array.toList_map,List.mem_map] at member
  obtain ⟨node,member,rfl⟩ := member
  exact lowerNode_frame _ runtime a.machine.capacity node (certificate.closed node member)

theorem mapM_related (action : α → EmitM β) (items : List α) (stable : ∀ item, Preserves (action item))
    (correct : ∀ item ∈ items, ∀ before, before.WellFormed → ∀ result after,
      action item before = .ok (result,after) → after.Extends final → relation item result)
    (good : before.WellFormed) (success : items.mapM action before = .ok (results,after))
    (grows : after.Extends final) : Paired relation items results := by
  induction items generalizing before after results with
  | nil =>
    obtain ⟨rfl,_⟩ := pure_success ([] : List β) success
    exact .nil
  | cons item items ih =>
    rw [List.mapM_cons] at success
    obtain ⟨result,middle,compiled,rest⟩ := bind_success _ _ success
    obtain ⟨tail,compiledTail,rfl⟩ := return_success (items.mapM action) (fun tail => result::tail) rest
    obtain ⟨middleGood,_,_⟩ := stable item before good result middle compiled
    have more := (preserves_mapM action items stable middle middleGood tail after compiledTail).2.1
    exact .cons (correct item (by simp) before good result middle compiled (more.trans grows))
      (ih (fun i hi => correct i (by simp [hi])) middleGood compiledTail grows)

theorem Paired.lookup {k : Nat} (paired : Paired relation left right) (found : left[k]? = some item) :
    ∃ result, right[k]? = some result ∧ relation item result := by
  induction paired generalizing k with
  | nil => simp at found
  | cons related paired ih =>
    cases k with
    | zero => simp only [List.getElem?_cons_zero,Option.some.injEq] at found; subst item; exact ⟨_,rfl,related⟩
    | succ k => exact ih found

/-- Complete generated compute cases preserve the reference RTL state.
All closure, validity, physical-allocation and pending-bank frame conditions
come from the existing layout certificate and actual node lowering. -/
theorem generateCode_refines (a : Artifact) (certificate : StorageCertificate a)
    (r : FiniteRuntime a.storageShape) (generated : generateCode a = .ok (codes,emission)) :
    ∃ values, evaluateWires a r emission.text = some values ∧
      Paired (fun body code => ∃ writes,
        code.eval ((environment a r emission.text #[]).withTemporaries values)
          ((environment a r emission.text #[]).withTemporaries values).store = some writes ∧
        writes.Matches ((environment a r emission.text #[]).withTemporaries values) a.storageShape
          (body.evalWith RTL.Combinational.eval a.machine.capacity r.decode r.decode))
        (RTL.artifactProgram a).cases.toList codes := by
  obtain ⟨values,evaluated,meaning⟩ := generateCode_total a certificate r generated
  refine ⟨values,evaluated,?_⟩
  apply mapM_related (statementCode a) (RTL.artifactProgram a).cases.toList (preserves_statementCode a)
    ?_ Emission.empty_wellFormed generated (Emission.Extends.refl _)
  intro body member before good code after compiled grows
  have closed : StatementReferences a.storageShape body := by
    simp only [RTL.artifactProgram,RTL.lowerCombinational,Array.toList_map,List.mem_map] at member
    obtain ⟨node,member,rfl⟩ := member
    exact lowerNode_references _ node (certificate.closed node member)
  exact statementCode_refines a r emission values body closed (artifact_ready a certificate r.decode member)
    good compiled grows meaning _ r.decode (finite_store_matches a r emission values)
    (artifact_frame a certificate r.decode member)

/-- One compute clock, including the selected control-flow successor,
refines the pre-existing bit-level machine transition. This covers the actual
generated statement AST; reset/start/config and module text are separate. -/
theorem generateCode_tick_refines (a : Artifact) (certificate : StorageCertificate a)
    (r : FiniteRuntime a.storageShape) (running : r.done = false)
    (found : (RTL.artifactProgram a).cases[r.pc.toNat]? = some body)
    (generated : generateCode a = .ok (codes,emission)) :
    ∃ values code writes, evaluateWires a r emission.text = some values ∧
      codes[r.pc.toNat]? = some code ∧
      code.eval ((environment a r emission.text #[]).withTemporaries values)
        ((environment a r emission.text #[]).withTemporaries values).store = some writes ∧
      writes.Matches ((environment a r emission.text #[]).withTemporaries values) a.storageShape
        (a.machine.bitTick a.storageShape.wireRange r.decode) := by
  obtain ⟨values,evaluated,paired⟩ := generateCode_refines a certificate r generated
  obtain ⟨code,codeFound,writes,executed,related⟩ := paired.lookup (by simpa using found)
  refine ⟨values,code,writes,evaluated,codeFound,executed,?_⟩
  have transition : (a.machine.bitTick a.storageShape.wireRange r.decode) =
      body.evalWith RTL.Combinational.eval a.machine.capacity r.decode r.decode := by
    rw [← RTL.lowerCombinational_tick]
    change (RTL.artifactProgram a).combinationalTick r.decode = _
    simp only [RTL.Program.combinationalTick,show r.decode.done = false from running,Bool.false_eq_true,↓reduceIte]
    change (match (RTL.artifactProgram a).cases[r.pc.toNat]? with | none => _ | some b => _) = _
    rw [found]
    rfl
  rw [transition]
  exact related

end IRComparison.Circuit.SystemVerilog
