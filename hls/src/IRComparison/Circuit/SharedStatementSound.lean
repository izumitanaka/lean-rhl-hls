import IRComparison.Circuit.SharedStatements
import IRComparison.Circuit.SystemVerilog.RefinementSound

namespace IRComparison.Circuit
open SystemVerilog

namespace Shared

/-- The proof interpretation reads cached graph nodes, not reconstructed trees.
Value and validity are separate even on failed source computations. -/
instance : ExpressionSemantics Prepared where
  value p r := (LocalRTL.fullValues r p.program.code)[2*p.program.result]?.getD 0
  valid p r := (LocalRTL.fullValues r p.program.code)[2*p.program.result+1]?.getD 0 != 0
  references shape p := ∀ c ∈ p.program.code, NetEmission.CodeReferences shape c

@[simp] theorem prepared_eval (p : Prepared) (r : Runtime) :
    ExpressionSemantics.eval p r = p.program.fullEval r := rfl

end Shared

instance [ExpressionSemantics α] [ExpressionSemantics β] : ExpressionSemantics (Sum α β) where
  value e := match e with
    | .inl e => ExpressionSemantics.value e
    | .inr e => ExpressionSemantics.value e
  valid e := match e with
    | .inl e => ExpressionSemantics.valid e
    | .inr e => ExpressionSemantics.valid e
  references shape e := match e with
    | .inl e => ExpressionSemantics.references shape e
    | .inr e => ExpressionSemantics.references shape e

namespace Shared.NetEmission

/-- Actual continuous assignment equations supply the graph writer's contract.
No old cache entry or expanded expression is needed for a shared program. -/
theorem shared_codeSound (a : Artifact) (r : FiniteRuntime a.storageShape)
    (final : Emission) (values : Array Int)
    (realized : Realizes ((environment a r final.text #[]).withTemporaries values) final) :
    ExpressionCodeSound (α:=Prepared) a r final values := by
  refine ⟨fun p => into_preserves a p.program,?_⟩
  intro p closed before good signal after success grows
  exact into_signal_correct a r.decode p.program
    (fun c hc => codePhysical_from_refs a r final.text values c (closed c hc))
    good success (realized.restrict grows)

theorem sum_codeSound {a : Artifact} {r : FiniteRuntime a.storageShape}
    {final : Emission} {values : Array Int} [ExpressionCode α] [ExpressionCode β]
    [ExpressionSemantics α] [ExpressionSemantics β]
    (left : ExpressionCodeSound (α:=α) a r final values)
    (right : ExpressionCodeSound (α:=β) a r final values) :
    ExpressionCodeSound (α:=Sum α β) a r final values := by
  constructor
  · intro e; cases e with
    | inl e => exact left.preserves e
    | inr e => exact right.preserves e
  · intro e; cases e with
    | inl e => exact left.correct e
    | inr e => exact right.correct e

theorem shared_keeps_trace (a : Artifact) (r : FiniteRuntime a.storageShape)
    (declarations : Wires) (p : Prepared)
    (closed : ExpressionSemantics.references a.storageShape p) :
    Keeps (fun st => NetTrace (environment a r declarations #[]) st.text)
      (ExpressionCode.emit a p) := by
  refine ⟨into_preserves a p.program,?_⟩
  intro before good previous signal after success
  obtain ⟨pair,built,rfl⟩ := map_success (intoPair a p.program) Pair.signal success
  exact intoPair_trace a r.decode p.program
    (fun c hc values => codePhysical_from_refs a r declarations values c (closed c hc))
    good previous built

/-- All shared declarations of all cases evaluate successfully, including the
ones belonging to a branch not taken this clock. Invalid source reads remain
represented by false validity, not failed SystemVerilog wire evaluation. -/
theorem shared_cases_total (a : Artifact) (r : FiniteRuntime a.storageShape)
    (cases : List (RTL.Statement Prepared)) (codes : List SystemVerilog.Statement) (emission : Emission)
    (closed : ∀ s ∈ cases, StatementReferences a.storageShape s)
    (generated : (cases.mapM (statementCode a)).run {} = .ok (codes,emission)) :
    ∃ values, evaluateWires a r emission.text = some values ∧
      Realizes ((environment a r emission.text #[]).withTemporaries values) emission := by
  have each := fun s hs => keeps_statementCode a (shared_keeps_trace a r emission.text) s (closed s hs)
  have trace := (keeps_mapM cases (statementCode a) each).2
    {} Emission.empty_wellFormed NetTrace.empty codes emission generated
  have ordered := module_declarations_ordered a (fun p => into_preserves a p.program) generated
  obtain ⟨values,evaluated,_⟩ := trace.total (declared_environment a r emission ordered)
  exact ⟨values,evaluated,evaluateWires_realizes a r emission ordered evaluated⟩

/-- State refinement for all shared-expression statement syntax, including
memory/FIFO operations, nested branches and nonblocking sequential writes.
Readiness and frame facts are obligations of lowering, as on the old route.
Netlist evaluation success is derived separately, not hidden in this theorem. -/
theorem shared_statement_refines_control (a : Artifact) (r : FiniteRuntime a.storageShape)
    (final : Emission) (values : Array Int) (body : RTL.Statement Prepared)
    {code : SystemVerilog.Statement}
    (closed : StatementReferences a.storageShape body)
    (ready : StatementReady a.storageShape r.decode a.machine.capacity body)
    (good : before.WellFormed) (success : statementCode a body before = .ok (code,after))
    (grows : after.Extends final)
    (realized : Realizes ((environment a r final.text #[]).withTemporaries values) final)
    (pending : Store) (logical : Runtime)
    (related : pending.Matches ((environment a r final.text #[]).withTemporaries values) a.storageShape logical)
    (frame : StatementFrame a.storageShape r.decode a.machine.capacity body logical) :
    ∃ writes, code.eval ((environment a r final.text #[]).withTemporaries values) pending = some writes ∧
      writes.Matches ((environment a r final.text #[]).withTemporaries values) a.storageShape
        (body.evalWith (fun p => p.program.fullEval) a.machine.capacity r.decode logical) ∧
      (BusyMatches pending logical → BusyMatches writes
        (body.evalWith (fun p => p.program.fullEval) a.machine.capacity r.decode logical)) :=
  statementCode_refines_controlWith a r final values body closed ready good success grows
    (shared_codeSound a r final values realized) pending logical related frame

/-- An arbitrary selected compute case, with evaluation success concluded.
The result is the physical pending state of this clock; reset/start/config,
commit, and repeated module clocks remain separate interface obligations. -/
theorem shared_cases_refine (a : Artifact) (r : FiniteRuntime a.storageShape)
    (cases : List (RTL.Statement Prepared)) (codes : List SystemVerilog.Statement) (emission : Emission)
    (closed : ∀ s ∈ cases, StatementReferences a.storageShape s)
    (ready : ∀ s ∈ cases, StatementReady a.storageShape r.decode a.machine.capacity s)
    (frame : ∀ s ∈ cases, StatementFrame a.storageShape r.decode a.machine.capacity s r.decode)
    (generated : (cases.mapM (statementCode a)).run {} = .ok (codes,emission)) :
    ∃ values, evaluateWires a r emission.text = some values ∧
      Paired (fun body code => ∀ pending,
        pending.Matches ((environment a r emission.text #[]).withTemporaries values) a.storageShape r.decode →
        BusyMatches pending r.decode → ∃ writes,
        code.eval ((environment a r emission.text #[]).withTemporaries values) pending = some writes ∧
        writes.Matches ((environment a r emission.text #[]).withTemporaries values) a.storageShape
          (body.evalWith (fun p => p.program.fullEval) a.machine.capacity r.decode r.decode) ∧
        BusyMatches writes (body.evalWith (fun p => p.program.fullEval) a.machine.capacity r.decode r.decode))
        cases codes := by
  obtain ⟨values,evaluated,realized⟩ := shared_cases_total a r cases codes emission closed generated
  refine ⟨values,evaluated,?_⟩
  apply mapM_related (statementCode a) cases (shared_statement_preserves a)
    ?_ Emission.empty_wellFormed generated (Emission.Extends.refl _)
  intro body member before good code after compiled grows pending related busy
  obtain ⟨writes,executed,matched,control⟩ := shared_statement_refines_control a r emission values body
    (closed body member) (ready body member) good compiled grows realized pending r.decode related (frame body member)
  exact ⟨writes,executed,matched,control busy⟩

/-- A complete compute clock of the generated shared module, including physical
nonblocking commit. The observed state is compared with finite encoding of the
RTL statement semantics. Source-to-case lowering remains a separate boundary. -/
theorem shared_module_tick (a : Artifact) (r : RTL.InterfaceState a.storageShape)
    (cases : List (RTL.Statement Prepared)) {result : ModuleCode} {selected : RTL.Statement Prepared}
    (closed : ∀ s ∈ cases, StatementReferences a.storageShape s)
    (ready : ∀ s ∈ cases, StatementReady a.storageShape r.core.decode a.machine.capacity s)
    (frame : ∀ s ∈ cases, StatementFrame a.storageShape r.core.decode a.machine.capacity s r.core.decode)
    (generated : generateModule a outputs cases = .ok result)
    (active : r.busy = true) (notDone : r.core.done = false)
    (found : cases[r.core.pc.toNat]? = some selected) :
    ∃ next, result.tick a.storageShape {} r = some next ∧
      StorageAgreement a.storageShape next.core.decode
        (FiniteRuntime.pack a.storageShape
          (selected.evalWith (fun p => p.program.fullEval) a.machine.capacity r.core.decode r.core.decode)).decode ∧
      next.busy = !(selected.evalWith (fun p => p.program.fullEval) a.machine.capacity r.core.decode r.core.decode).done := by
  obtain ⟨codes,emission,compiled,rfl⟩ := generateModule_components a generated
  obtain ⟨values,evaluated,paired⟩ := shared_cases_refine a r.core cases codes emission closed ready frame compiled
  obtain ⟨code,codeFound,correct⟩ := paired.lookup found
  obtain ⟨writes,executed,related,busy⟩ := correct (environment a r.core emission.text #[]).store
    (base_store_matches a r.core emission values)
    (by simp [BusyMatches,Environment.store,environment,environmentFor,FiniteRuntime.decode,notDone])
  refine ⟨⟨writes.commit a.storageShape,writes.busy⟩,?_,related.commit_packed a r.core emission values,?_⟩
  · rw [moduleCode_tick]
    simp only [physicalTick,clockCode,active,RTL.controller_execute ({} : RTL.Ports) rfl,evaluated,
      bind,Option.bind,pure,codeFound,Option.getD_some]
    rw [executed]
  · unfold BusyMatches at busy
    simp only [Store.busy,busy,Option.getD_some]
    cases (selected.evalWith (fun p => p.program.fullEval) a.machine.capacity r.core.decode r.core.decode).done <;> rfl

/-- The same clock guarantee starts from the actual printed module String,
using the existing concrete parser, not an assumed interpretation of text. -/
theorem shared_module_text_tick (a : Artifact) (r : RTL.InterfaceState a.storageShape)
    (cases : List (RTL.Statement Prepared)) {result : ModuleCode} {selected : RTL.Statement Prepared}
    (closed : ∀ s ∈ cases, StatementReferences a.storageShape s)
    (ready : ∀ s ∈ cases, StatementReady a.storageShape r.core.decode a.machine.capacity s)
    (frame : ∀ s ∈ cases, StatementFrame a.storageShape r.core.decode a.machine.capacity s r.core.decode)
    (generated : generateModule a outputs cases = .ok result)
    (active : r.busy = true) (notDone : r.core.done = false)
    (found : cases[r.core.pc.toNat]? = some selected) :
    ∃ next, (Concrete.parseModule result.text).bind (fun parsed => parsed.tick a.storageShape {} r) = some next ∧
      StorageAgreement a.storageShape next.core.decode
        (FiniteRuntime.pack a.storageShape
          (selected.evalWith (fun p => p.program.fullEval) a.machine.capacity r.core.decode r.core.decode)).decode ∧
      next.busy = !(selected.evalWith (fun p => p.program.fullEval) a.machine.capacity r.core.decode r.core.decode).done := by
  obtain ⟨next,executed,related,busy⟩ := shared_module_tick a r cases closed ready frame generated active notDone found
  refine ⟨next,?_,related,busy⟩
  obtain ⟨codes,emission,_,rfl⟩ := generateModule_components a generated
  rw [ModuleCode.text,Concrete.parse_printModule _ (moduleCode_storage _ _ _ _).positive rfl]
  exact (moduleReadback_tick _ _ _ _).trans executed

end Shared.NetEmission
end IRComparison.Circuit
