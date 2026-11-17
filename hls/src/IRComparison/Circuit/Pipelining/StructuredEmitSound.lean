import IRComparison.Circuit.Pipelining.StructuredEmit

namespace IRComparison.Circuit.Pipelining
open SystemVerilog

theorem generateGraph_total (a : Artifact) (g : ClockGraph) (hc : ∀ n ∈ g.nodes.toList, n.closed a.storageShape)
    (r : FiniteRuntime a.storageShape) (generated : generateGraph a g = .ok (codes,emission)) :
    ∃ values, evaluateWires a r emission.text = some values ∧
      CacheMeaning ((environment a r emission.text #[]).withTemporaries values) r.decode emission := by
  have closed : CacheAll (ReferencesIn a.storageShape) emission := by
    have each : ∀ body ∈ graphCases a g,
        CachePreserves (ReferencesIn a.storageShape) (statementCode a body) := by
      intro body member
      obtain ⟨s,hs,rfl⟩ := List.mem_map.mp member
      exact cache_statementCode a _ (graphStatements_references hc hs)
    exact (cache_mapM _ _ each).2 {} Emission.empty_wellFormed
      (by intro entry member; simp at member) codes emission generated
  have physical : PhysicalFor a r.decode (environment a r emission.text #[]) emission := by
    intro entry member values
    exact physicalNode_finite a r emission.text values entry.1 (closed entry member)
  have trace : EmissionTrace a emission :=
    (trace_mapM (graphCases a g) (statementCode a) (fun item _ => trace_statementCode a item)).2
      {} Emission.empty_wellFormed .empty codes emission generated
  have ordered : Ordered 0 emission.text.toList :=
    ((preserves_mapM (statementCode a) (graphCases a g) (preserves_statementCode a))
      {} Emission.empty_wellFormed codes emission generated).1.ordered
  obtain ⟨values,evaluated,_,meaning⟩ := trace.total (declared_environment a r emission ordered) physical
  exact ⟨values,evaluated,meaning⟩

theorem generated_graph_cases_control (a : Artifact) (g : ClockGraph)
    (hc : ∀ n ∈ g.nodes.toList, n.closed a.storageShape) (hn : ∀ n ∈ g.nodes.toList, n.distinct)
    (r : FiniteRuntime a.storageShape)
    (generated : generateGraph a g = .ok (codes,emission)) :
    ∃ values, evaluateWires a r emission.text = some values ∧
      Paired (fun body code => ∀ pending,
        pending.Matches ((environment a r emission.text #[]).withTemporaries values) a.storageShape r.decode →
        BusyMatches pending r.decode →
        ∃ writes, code.eval ((environment a r emission.text #[]).withTemporaries values) pending = some writes ∧
          writes.Matches ((environment a r emission.text #[]).withTemporaries values) a.storageShape
            (body.evalWith RTL.Combinational.eval a.machine.capacity r.decode r.decode) ∧
          BusyMatches writes (body.evalWith RTL.Combinational.eval a.machine.capacity r.decode r.decode))
        (graphCases a g) codes := by
  obtain ⟨values,evaluated,meaning⟩ := generateGraph_total a g hc r generated
  refine ⟨values,evaluated,?_⟩
  apply mapM_related (statementCode a) (graphCases a g) (preserves_statementCode a)
    ?_ Emission.empty_wellFormed generated (Emission.Extends.refl _)
  intro body member before good code after compiled grows pending related busy
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp member
  obtain ⟨writes,executed,result,control⟩ := statementCode_refines_control a r emission values _
    (graphStatements_references hc hs) (graphStatements_ready hc hs) good compiled grows meaning
    pending r.decode related (graphStatements_frame hc hn hs)
  exact ⟨writes,executed,result,control busy⟩

/-- One physical clock of the actual generated SystemVerilog assignments,
including pending nonblocking writes and physical bit-vector commit. This
is a digital clock theorem; no propagation-delay model is assumed. -/
theorem physical_graph_tick (a : Artifact) (g : ClockGraph)
    (caps : g.capacities = a.machine.capacities)
    (hc : ∀ n ∈ g.nodes.toList, n.closed a.storageShape) (hn : ∀ n ∈ g.nodes.toList, n.distinct)
    (generated : generateGraph a g = .ok (codes,emission))
    (r : RTL.InterfaceState a.storageShape) (active : r.busy = true) (notDone : r.core.done = false)
    (inside : r.core.pc.toNat < (graphStatements g).length) :
    ∃ result, physicalTick a codes emission.text {} r = some result ∧
      StorageAgreement a.storageShape result.core.decode
        (FiniteRuntime.pack a.storageShape
          (g.rtl.tick a.storageShape.wireRange r.core.decode)).decode ∧
      result.busy = !(g.rtl.tick a.storageShape.wireRange r.core.decode).done := by
  let source := (graphStatements g)[r.core.pc.toNat]'inside
  have found : (graphStatements g)[r.core.pc.toNat]? = some source := List.getElem?_eq_getElem inside
  obtain ⟨values,evaluated,paired⟩ := generated_graph_cases_control a g hc hn r.core generated
  have mapped : (graphCases a g)[r.core.pc.toNat]? =
      some (source.mapExpressions (RTL.combinational a.storageShape.wireRange)) := by
    simp only [graphCases,List.getElem?_map,found,Option.map_some]
  obtain ⟨code,codeFound,correct⟩ := paired.lookup mapped
  obtain ⟨writes,executed,related,busy⟩ := correct (environment a r.core emission.text #[]).store
    (base_store_matches a r.core emission values)
    (by simp [BusyMatches,Environment.store,environment,environmentFor,FiniteRuntime.decode,notDone])
  have reference : (source.mapExpressions (RTL.combinational a.storageShape.wireRange)).evalWith
      RTL.Combinational.eval a.machine.capacity r.core.decode r.core.decode =
      g.rtl.tick a.storageShape.wireRange r.core.decode := by
    rw [RTL.map_statement_correct]
    have fields : g.rtl.cases.toList = graphStatements g := by simp [ClockGraph.rtl,graphStatements]
    have selected : g.rtl.cases[r.core.pc.toNat]? = some source := by
      simpa [← fields] using found
    simp only [RTL.Program.tick,FiniteRuntime.decode,notDone,Bool.false_eq_true,ite_false,
      selected,Option.getD_some]
    simp only [ClockGraph.rtl,caps]
    rfl
  rw [reference] at related busy
  refine ⟨⟨writes.commit a.storageShape,writes.busy⟩,?_,related.commit_packed a r.core emission values,?_⟩
  · simp only [physicalTick,clockCode,active,RTL.controller_execute ({} : RTL.Ports) rfl,evaluated,
      bind,Option.bind,pure,codeFound,Option.getD_some]
    rw [executed]
  · unfold BusyMatches at busy
    simp only [Store.busy,busy,Option.getD_some]
    cases (g.rtl.tick a.storageShape.wireRange r.core.decode).done <;> rfl


end IRComparison.Circuit.Pipelining
