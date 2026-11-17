import IRComparison.Circuit.Pipelining.StructuredEmitSound

namespace IRComparison.Circuit.Pipelining

theorem ClockNode.storage_congr (n : ClockNode) (hc : n.closed shape)
    (same : StorageAgreement shape r t) :
    StorageAgreement shape (n.statement.eval wr cap r r) (n.statement.eval wr cap t t) := by
  cases n with
  | batch as next => exact lowerClock_storage_congr next as hc same
  | jump next => exact same.setPC
  | halt => exact same.stop
  | branch e yes no =>
    have eq := Expr.bitEval_storage_congr e hc.1 same (wr := wr)
    simp only [ClockNode.statement,RTL.lowerNode,RTL.guarded,RTL.Statement.eval,
      RTL.Test.eval,eq]
    split
    · split <;> exact same.setPC
    · exact same.fault

theorem clockGraph_tick_storage {g : ClockGraph} (hc : ∀ n ∈ g.nodes.toList, n.closed shape)
    (same : StorageAgreement shape r t) :
    StorageAgreement shape (g.rtl.tick wr r) (g.rtl.tick wr t) := by
  simp only [ClockGraph.rtl,RTL.Program.tick,same.done,same.pc,Array.getElem?_map]
  split
  · exact same
  · cases hn : g.nodes[t.pc]? with
    | none => exact same.fault
    | some n =>
      exact n.storage_congr (hc n (by simpa using Array.mem_of_getElem? hn)) same

theorem physical_graph_run (a : Artifact) (g : ClockGraph)
    (caps : g.capacities = a.machine.capacities)
    (hc : ∀ n ∈ g.nodes.toList, n.closed a.storageShape) (hn : ∀ n ∈ g.nodes.toList, n.distinct)
    (generated : generateGraph a g = .ok (codes,emission))
    (logical : Circuit.Runtime)
    (bounded : ∀ n, StorageBound a.storageShape
      (g.rtl.run a.storageShape.wireRange n logical))
    (pcBound : ∀ n, (g.rtl.run a.storageShape.wireRange n logical).done = false →
      (g.rtl.run a.storageShape.wireRange n logical).pc < (graphStatements g).length)
    (r : RTL.InterfaceState a.storageShape) (running : r.Running)
    (same : StorageAgreement a.storageShape r.core.decode logical) (cycles : Nat) :
    ∃ result, SystemVerilog.physicalRun a codes emission.text cycles r = some result ∧
      StorageAgreement a.storageShape result.core.decode
        (g.rtl.run a.storageShape.wireRange cycles logical) ∧ result.Running := by
  induction cycles generalizing r logical with
  | zero => exact ⟨r,rfl,same,running⟩
  | succ n ih =>
    let program := g.rtl
    have one : ∃ next, SystemVerilog.physicalTick a codes emission.text {} r = some next ∧
        StorageAgreement a.storageShape next.core.decode (program.tick a.storageShape.wireRange logical) ∧ next.Running := by
      cases active : r.busy with
      | false =>
        have stopped : logical.done = true := by
          have hh := same.done
          change r.core.done = logical.done at hh
          unfold RTL.InterfaceState.Running at running
          cases h : r.core.done <;> simp_all
        refine ⟨r,?_,?_,running⟩
        · simp only [SystemVerilog.physicalTick,SystemVerilog.clockCode,active,RTL.controller,
            RTL.Controller.select,RTL.PortTest.eval,Bool.false_eq_true,ite_false,bind,Option.bind,pure,SystemVerilog.Statement.eval]
          change some ⟨(SystemVerilog.environmentFor a.storageShape r.core emission.text #[] false {}).store.commit _,_⟩ = some r
          rw [SystemVerilog.commit_environment]
          cases r with | mk core busy => dsimp at active; subst busy; rfl
        · simpa [program,RTL.Program.tick,stopped] using same
      | true =>
        have notDone : r.core.done = false := by
          unfold RTL.InterfaceState.Running at running
          rw [active] at running
          cases h : r.core.done <;> simp_all
        have logicalLive : logical.done = false := by rw [← same.done]; exact notDone
        have inside : r.core.pc.toNat < (graphStatements g).length := by
          change r.core.decode.pc < _
          rw [same.pc]
          exact pcBound 0 logicalLive
        obtain ⟨next,executed,related,busy⟩ := physical_graph_tick a g caps hc hn generated r active notDone inside
        have congr := clockGraph_tick_storage hc same (wr := a.storageShape.wireRange)
        rw [FiniteRuntime.pack_congr congr] at related
        have same' := related.trans (FiniteRuntime.pack_correct (bounded 1))
        refine ⟨next,executed,same',?_⟩
        change next.busy = !next.core.decode.done
        rw [busy,same'.done,congr.done]
    obtain ⟨next,executed,nextSame,nextRunning⟩ := one
    obtain ⟨result,rest,finalSame,finalRunning⟩ := ih (program.tick a.storageShape.wireRange logical)
      (fun k => bounded (k+1)) (fun k => pcBound (k+1)) next nextRunning nextSame
    exact ⟨result,by rw [SystemVerilog.physicalRun,executed]; exact rest,finalSame,finalRunning⟩


end IRComparison.Circuit.Pipelining
