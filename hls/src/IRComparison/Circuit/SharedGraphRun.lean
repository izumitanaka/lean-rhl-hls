import IRComparison.Circuit.SharedGraphSound

namespace IRComparison.Circuit.Shared
open Pipelining SystemVerilog

theorem graph_cases_references (checks : GraphChecks a g table) :
    ∀ body ∈ graphCases a g, StatementReferences a.storageShape body := by
  intro body member
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp member
  obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hs
  exact node_references n (checks.closed n hn)

theorem graph_cases_ready (checks : GraphChecks a g table) (r : Runtime) :
    ∀ body ∈ graphCases a g, StatementReady a.storageShape r a.machine.capacity body := by
  intro body member
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp member
  obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hs
  exact node_ready n (checks.closed n hn)

theorem graph_cases_frame (checks : GraphChecks a g table) (r : Runtime) :
    ∀ body ∈ graphCases a g, StatementFrame a.storageShape r a.machine.capacity body r := by
  intro body member
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp member
  obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hs
  exact node_frame n (checks.closed n hn) (checks.distinct n hn)

theorem generated_idle {cases : List (RTL.Statement Prepared)} (generated : NetEmission.generateModule a outputs cases = .ok code)
    (r : RTL.InterfaceState a.storageShape) (inactive : r.busy = false) :
    code.tick a.storageShape {} r = some r := by
  obtain ⟨codes,emission,_,rfl⟩ := NetEmission.generateModule_components a generated
  rw [moduleCode_tick]
  simp only [physicalTick,clockCode,inactive,RTL.controller,
    RTL.Controller.select,RTL.PortTest.eval,Bool.false_eq_true,ite_false,bind,Option.bind,pure,Statement.eval]
  change some ⟨(environmentFor a.storageShape r.core emission.text #[] false {}).store.commit _,_⟩ = some r
  rw [commit_environment]
  cases r with | mk core busy => dsimp at inactive; subst busy; rfl

/-- The checked shared circuit, including all control and state, refines one
physical compute clock. All emission readiness/frame premises are derived. -/
theorem generated_tick (generated : generateGraphModule a g outputs = .ok code)
    (checks : GraphChecks a g table) (bound : ClockBound a g table logical)
    (r : RTL.InterfaceState a.storageShape) (running : r.Running)
    (same : StorageAgreement a.storageShape r.core.decode logical) :
    ∃ next, code.tick a.storageShape {} r = some next ∧
      StorageAgreement a.storageShape next.core.decode (g.tick logical) ∧ next.Running := by
  obtain ⟨_,_,compiled⟩ := generateGraphModule_components generated
  cases active : r.busy with
  | false =>
    have stopped : logical.done = true := by
      have hh := same.done
      change r.core.done = logical.done at hh
      unfold RTL.InterfaceState.Running at running
      cases h : r.core.done <;> simp_all
    exact ⟨r,generated_idle compiled r active,by simpa [ClockGraph.tick,stopped] using same,running⟩
  | true =>
    have notDone : r.core.done = false := by
      unfold RTL.InterfaceState.Running at running
      rw [active] at running
      cases h : r.core.done <;> simp_all
    have live : logical.done = false := by rw [← same.done]; exact notDone
    have inside : r.core.pc.toNat < g.nodes.size := by
      change r.core.decode.pc < _
      rw [same.pc]; exact bound.pc
    let node := g.nodes[r.core.pc.toNat]'inside
    have found : g.nodes[r.core.pc.toNat]? = some node := Array.getElem?_eq_getElem inside
    have member : node ∈ g.nodes.toList := by simp [node]
    have selected : (graphCases a g)[r.core.pc.toNat]? =
        some (node.statement.mapExpressions (prepare a.storageShape.wireRange)) := by
      simp [graphCases,graphStatements,List.getElem?_map,found]
    obtain ⟨next,executed,related,busy⟩ := NetEmission.shared_module_tick a r (graphCases a g)
      (graph_cases_references checks) (graph_cases_ready checks _) (graph_cases_frame checks _)
      compiled active notDone selected
    have reference : g.tick logical = node.eval g.capacity logical := by
      simp [ClockGraph.tick,live,← same.pc,FiniteRuntime.decode,found]
    have congr := node_storage_congr node (checks.closed node member) same
      (wr := a.storageShape.wireRange) (cap := a.machine.capacity)
    have numeric : InputsBound logical.data logical.wires a.storageShape.wireRange := by
      rw [shape_frame]; exact bound.numeric.inputs
    have caps : g.capacity = a.machine.capacity := by
      change capacityOf g.capacities = capacityOf a.machine.capacities
      rw [checks.capacity]
    rw [← caps,node_statement_correct node numeric,← reference] at congr
    rw [statement_prepared,← caps] at related busy
    rw [FiniteRuntime.pack_congr congr] at related
    have same' := related.trans (FiniteRuntime.pack_correct ((clockGraph_tick_bound checks bound).storage checks.size))
    refine ⟨next,executed,same',?_⟩
    change next.busy = !next.core.decode.done
    rw [busy,same'.done,congr.done]

/-- Arbitrarily many clocks of the emitted SystemVerilog preserve the shared
controller state. This is not a bounded test or a single-clock-only result. -/
theorem generated_run (generated : generateGraphModule a g outputs = .ok code)
    (checks : GraphChecks a g table) (bound : ClockBound a g table logical)
    (r : RTL.InterfaceState a.storageShape) (running : r.Running)
    (same : StorageAgreement a.storageShape r.core.decode logical) (cycles : Nat) :
    ∃ result, code.run a.storageShape cycles r = some result ∧
      StorageAgreement a.storageShape result.core.decode (g.run cycles logical) ∧ result.Running := by
  induction cycles generalizing r logical with
  | zero => exact ⟨r,rfl,same,running⟩
  | succ n ih =>
    obtain ⟨next,executed,agrees,active⟩ := generated_tick generated checks bound r running same
    obtain ⟨result,rest,finalSame,finalRunning⟩ := ih (clockGraph_tick_bound checks bound) next active agrees
    refine ⟨result,?_,finalSame,finalRunning⟩
    simp only [ModuleCode.run,executed,bind,Option.bind]
    exact rest

theorem generated_text_run (generated : generateGraphModule a g outputs = .ok code)
    (checks : GraphChecks a g table) (bound : ClockBound a g table logical)
    (r : RTL.InterfaceState a.storageShape) (running : r.Running)
    (same : StorageAgreement a.storageShape r.core.decode logical) (cycles : Nat) :
    ∃ result, (Concrete.parseModule code.text).bind (fun parsed => parsed.run a.storageShape cycles r) = some result ∧
      StorageAgreement a.storageShape result.core.decode (g.run cycles logical) ∧ result.Running := by
  obtain ⟨result,executed,agrees,active⟩ := generated_run generated checks bound r running same cycles
  refine ⟨result,?_,agrees,active⟩
  obtain ⟨_,_,compiled⟩ := generateGraphModule_components generated
  obtain ⟨codes,emission,_,rfl⟩ := NetEmission.generateModule_components a compiled
  rw [ModuleCode.text,printModule_run _ (moduleCode_storage _ _ _ _).positive rfl]
  exact executed

end IRComparison.Circuit.Shared
