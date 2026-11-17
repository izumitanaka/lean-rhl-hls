import IRComparison.Circuit.Pipelining.EmitSafety

namespace IRComparison.Circuit.Pipelining
open SystemVerilog

def BatchesClosed (shape : StorageShape) (bs : Batches) : Prop :=
  ∀ as ∈ bs, ∀ a ∈ as, (a.node 0).inStorage shape

theorem batchStatements_references (bs : Batches) (hc : BatchesClosed shape bs) (pc : Nat)
    (hm : body ∈ batchStatements pc bs) :
    StatementReferences shape (body.mapExpressions (RTL.combinational wr)) := by
  induction bs generalizing pc with
  | nil => simp [batchStatements] at hm; subst body; trivial
  | cons as rest ih =>
    rcases List.mem_cons.mp hm with rfl | hm
    · exact lowerClock_references _ as (hc as (by simp))
    · exact ih (fun as ha => hc as (by simp [ha])) (pc+1) hm

theorem batchStatements_ready (bs : Batches) (hc : BatchesClosed shape bs) (pc : Nat)
    (hm : body ∈ batchStatements pc bs) :
    StatementReady shape old cap (body.mapExpressions (RTL.combinational wr)) := by
  induction bs generalizing pc with
  | nil => simp [batchStatements] at hm; subst body; trivial
  | cons as rest ih =>
    rcases List.mem_cons.mp hm with rfl | hm
    · exact lowerClock_ready _ as (hc as (by simp))
    · exact ih (fun as ha => hc as (by simp [ha])) (pc+1) hm

theorem batchStatements_frame (bs : Batches) (hc : BatchesClosed shape bs)
    (hn : ∀ as ∈ bs, BanksDistinct as) (pc : Nat)
    (hm : body ∈ batchStatements pc bs) :
    StatementFrame shape old cap (body.mapExpressions (RTL.combinational wr)) old := by
  induction bs generalizing pc with
  | nil => simp [batchStatements] at hm; subst body; simp [RTL.halt,RTL.Statement.mapExpressions,StatementFrame]
  | cons as rest ih =>
    rcases List.mem_cons.mp hm with rfl | hm
    · exact lowerClock_frame _ as (hc as (by simp)) (hn as (by simp))
    · exact ih (fun as ha => hc as (by simp [ha])) (fun as ha => hn as (by simp [ha])) (pc+1) hm

theorem generateBatches_total (a : Artifact) (bs : Batches) (hc : BatchesClosed a.storageShape bs)
    (r : FiniteRuntime a.storageShape) (generated : generateBatches a bs = .ok (codes,emission)) :
    ∃ values, evaluateWires a r emission.text = some values ∧
      CacheMeaning ((environment a r emission.text #[]).withTemporaries values) r.decode emission := by
  have closed : CacheAll (ReferencesIn a.storageShape) emission := by
    have each : ∀ body ∈ combinationalCases a bs,
        CachePreserves (ReferencesIn a.storageShape) (statementCode a body) := by
      intro body member
      obtain ⟨s,hs,rfl⟩ := List.mem_map.mp member
      exact cache_statementCode a _ (batchStatements_references bs hc 0 hs)
    exact (cache_mapM _ _ each).2 {} Emission.empty_wellFormed
      (by intro entry member; simp at member) codes emission generated
  have physical : PhysicalFor a r.decode (environment a r emission.text #[]) emission := by
    intro entry member values
    exact physicalNode_finite a r emission.text values entry.1 (closed entry member)
  have trace : EmissionTrace a emission :=
    (trace_mapM (combinationalCases a bs) (statementCode a) (fun item _ => trace_statementCode a item)).2
      {} Emission.empty_wellFormed .empty codes emission generated
  have ordered : Ordered 0 emission.text.toList :=
    ((preserves_mapM (statementCode a) (combinationalCases a bs) (preserves_statementCode a))
      {} Emission.empty_wellFormed codes emission generated).1.ordered
  obtain ⟨values,evaluated,_,meaning⟩ := trace.total (declared_environment a r emission ordered) physical
  exact ⟨values,evaluated,meaning⟩

theorem generated_batch_cases_control (a : Artifact) (bs : Batches)
    (hc : BatchesClosed a.storageShape bs) (hn : ∀ as ∈ bs, BanksDistinct as)
    (r : FiniteRuntime a.storageShape)
    (generated : generateBatches a bs = .ok (codes,emission)) :
    ∃ values, evaluateWires a r emission.text = some values ∧
      Paired (fun body code => ∀ pending,
        pending.Matches ((environment a r emission.text #[]).withTemporaries values) a.storageShape r.decode →
        BusyMatches pending r.decode →
        ∃ writes, code.eval ((environment a r emission.text #[]).withTemporaries values) pending = some writes ∧
          writes.Matches ((environment a r emission.text #[]).withTemporaries values) a.storageShape
            (body.evalWith RTL.Combinational.eval a.machine.capacity r.decode r.decode) ∧
          BusyMatches writes (body.evalWith RTL.Combinational.eval a.machine.capacity r.decode r.decode))
        (combinationalCases a bs) codes := by
  obtain ⟨values,evaluated,meaning⟩ := generateBatches_total a bs hc r generated
  refine ⟨values,evaluated,?_⟩
  apply mapM_related (statementCode a) (combinationalCases a bs) (preserves_statementCode a)
    ?_ Emission.empty_wellFormed generated (Emission.Extends.refl _)
  intro body member before good code after compiled grows pending related busy
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp member
  obtain ⟨writes,executed,result,control⟩ := statementCode_refines_control a r emission values _
    (batchStatements_references bs hc 0 hs) (batchStatements_ready bs hc 0 hs) good compiled grows meaning
    pending r.decode related (batchStatements_frame bs hc hn 0 hs)
  exact ⟨writes,executed,result,control busy⟩

/-- One physical clock of the actual generated SystemVerilog assignments,
including pending nonblocking writes and physical bit-vector commit. This
is a digital clock theorem; no propagation-delay model is assumed. -/
theorem physical_batch_tick (a : Artifact) (bs : Batches)
    (hc : BatchesClosed a.storageShape bs) (hn : ∀ as ∈ bs, BanksDistinct as)
    (generated : generateBatches a bs = .ok (codes,emission))
    (r : RTL.InterfaceState a.storageShape) (active : r.busy = true) (notDone : r.core.done = false)
    (inside : r.core.pc.toNat < (batchStatements 0 bs).length) :
    ∃ result, physicalTick a codes emission.text {} r = some result ∧
      StorageAgreement a.storageShape result.core.decode
        (FiniteRuntime.pack a.storageShape
          ((batchProgram bs a.machine.capacities).tick a.storageShape.wireRange r.core.decode)).decode ∧
      result.busy = !((batchProgram bs a.machine.capacities).tick a.storageShape.wireRange r.core.decode).done := by
  let source := (batchStatements 0 bs)[r.core.pc.toNat]'inside
  have found : (batchStatements 0 bs)[r.core.pc.toNat]? = some source := List.getElem?_eq_getElem inside
  obtain ⟨values,evaluated,paired⟩ := generated_batch_cases_control a bs hc hn r.core generated
  have mapped : (combinationalCases a bs)[r.core.pc.toNat]? =
      some (source.mapExpressions (RTL.combinational a.storageShape.wireRange)) := by
    simp only [combinationalCases,List.getElem?_map,found,Option.map_some]
  obtain ⟨code,codeFound,correct⟩ := paired.lookup mapped
  obtain ⟨writes,executed,related,busy⟩ := correct (environment a r.core emission.text #[]).store
    (base_store_matches a r.core emission values)
    (by simp [BusyMatches,Environment.store,environment,environmentFor,FiniteRuntime.decode,notDone])
  have reference : (source.mapExpressions (RTL.combinational a.storageShape.wireRange)).evalWith
      RTL.Combinational.eval a.machine.capacity r.core.decode r.core.decode =
      (batchProgram bs a.machine.capacities).tick a.storageShape.wireRange r.core.decode := by
    rw [RTL.map_statement_correct]
    simp only [batchProgram,RTL.Program.tick,FiniteRuntime.decode,notDone,Bool.false_eq_true,ite_false,
      List.getElem?_toArray,found,Option.getD_some]
    rfl
  rw [reference] at related busy
  refine ⟨⟨writes.commit a.storageShape,writes.busy⟩,?_,related.commit_packed a r.core emission values,?_⟩
  · simp only [physicalTick,clockCode,active,RTL.controller_execute ({} : RTL.Ports) rfl,evaluated,
      bind,Option.bind,pure,codeFound,Option.getD_some]
    rw [executed]
  · unfold BusyMatches at busy
    simp only [Store.busy,busy,Option.getD_some]
    cases ((batchProgram bs a.machine.capacities).tick a.storageShape.wireRange r.core.decode).done <;> rfl

end IRComparison.Circuit.Pipelining
