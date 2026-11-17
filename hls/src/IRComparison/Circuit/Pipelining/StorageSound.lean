import IRComparison.Circuit.Pipelining.EmitSound

namespace IRComparison.Circuit.Pipelining

theorem ready_storage_congr (a : Action) (hc : (a.node 0).inStorage shape)
    (same : StorageAgreement shape r t) : (ready a).eval wr cap r = (ready a).eval wr cap t := by
  cases a <;> simp only [Action.node,Node.inStorage] at hc
  case wire k e | assign k e => simp [ready,RTL.Test.eval,Expr.bitEval_storage_congr e hc.2.1 same]
  case store a j e => simp [ready,RTL.Test.eval,Expr.bitEval_storage_congr j hc.2.1 same,
    Expr.bitEval_storage_congr e hc.2.2.1 same,same.arrays a hc.1]
  case snapshot | erase | clear => rfl
  case send q e => simp [ready,RTL.Test.eval,Expr.bitEval_storage_congr e hc.2.1 same,same.queues q hc.1]
  case receive q k => simp [ready,RTL.Test.eval,same.queues q hc.1]

theorem writes_storage_congr (a : Action) (hc : (a.node 0).inStorage shape)
    (same : StorageAgreement shape r t) (pending : StorageAgreement shape p q) :
    StorageAgreement shape ((writes a).eval wr cap r p) ((writes a).eval wr cap t q) := by
  cases a <;> simp only [Action.node,Node.inStorage] at hc
  case wire k e | assign k e =>
    simp only [writes,RTL.Statement.eval,RTL.Scalar.eval,RTL.Register.write,
      Expr.bitEval_storage_congr e hc.2.1 same]
    first | exact pending.setWire | exact pending.setReg
  case store a j e =>
    simp only [writes,RTL.Statement.eval,RTL.MemoryRhs.eval,Expr.bitEval_storage_congr j hc.2.1 same,
      Expr.bitEval_storage_congr e hc.2.2.1 same,same.arrays a hc.1]
    exact pending.setArray
  case snapshot a b =>
    simp only [writes,RTL.Statement.eval,RTL.MemoryRhs.eval,same.arrays b hc.2.1]
    exact pending.setArray
  case erase => exact pending.setArray
  case clear => exact pending.setQueue
  case send q e =>
    simp only [writes,RTL.Statement.eval,RTL.QueueRhs.eval,Expr.bitEval_storage_congr e hc.2.1 same,
      same.queues q hc.1]
    exact pending.setQueue
  case receive q k =>
    simp only [writes,RTL.Statement.eval,RTL.Scalar.eval,RTL.QueueRhs.eval,RTL.Register.write,same.queues q hc.1]
    exact pending.setWire.setQueue

theorem lowerClock_storage_congr (next : Nat) (as : List Action)
    (hc : ∀ a ∈ as, (a.node 0).inStorage shape) (same : StorageAgreement shape r t) :
    StorageAgreement shape ((lowerClock next as).eval wr cap r r) ((lowerClock next as).eval wr cap t t) := by
  have test : (allReady as).eval wr cap r = (allReady as).eval wr cap t := by
    induction as with
    | nil => rfl
    | cons a as ih => simp only [allReady,RTL.Test.eval,
        ready_storage_congr a (hc a (by simp)) same,ih (fun a ha => hc a (by simp [ha]))]
  have body : ∀ p q, StorageAgreement shape p q →
      StorageAgreement shape ((allWrites as).eval wr cap r p) ((allWrites as).eval wr cap t q) := by
    clear test
    induction as with
    | nil => exact fun _ _ h => h
    | cons a as ih =>
      intro p q h
      exact ih (fun a ha => hc a (by simp [ha])) _ _ (writes_storage_congr a (hc a (by simp)) same h)
  simp only [lowerClock,RTL.Statement.eval,test]
  split
  · exact (body r t same).setPC
  · exact same.fault

theorem batchStatement_storage_congr (bs : Batches) (hc : BatchesClosed shape bs)
    (pc : Nat) (hm : body ∈ batchStatements pc bs) (same : StorageAgreement shape r t) :
    StorageAgreement shape (body.eval wr cap r r) (body.eval wr cap t t) := by
  induction bs generalizing pc with
  | nil => simp [batchStatements] at hm; subst body; exact same.stop
  | cons as rest ih =>
    rcases List.mem_cons.mp hm with rfl | hm
    · exact lowerClock_storage_congr _ as (hc as (by simp)) same
    · exact ih (fun as ha => hc as (by simp [ha])) (pc+1) hm

theorem batchTick_storage_congr (bs : Batches) (hc : BatchesClosed shape bs)
    (same : StorageAgreement shape r t) :
    StorageAgreement shape ((batchProgram bs capacities).tick wr r) ((batchProgram bs capacities).tick wr t) := by
  simp only [RTL.Program.tick,same.done,same.pc]
  split
  · exact same
  · cases hf : (batchProgram bs capacities).cases[t.pc]? with
    | none => exact same.fault
    | some body =>
      apply batchStatement_storage_congr bs hc 0 _ same
      exact List.mem_of_getElem? (by simpa [batchProgram] using hf)

/-- Complete execution of the emitted cases, with the real physical state
threaded through clocks. Numeric/storage bounds are separate from emitter
correctness and can be supplied by the static invariant checker. -/
theorem physical_batches_run (a : Artifact) (bs : Batches)
    (hc : BatchesClosed a.storageShape bs) (hn : ∀ as ∈ bs, BanksDistinct as)
    (generated : generateBatches a bs = .ok (codes,emission))
    (logical : Circuit.Runtime)
    (bounded : ∀ n, StorageBound a.storageShape
      ((batchProgram bs a.machine.capacities).run a.storageShape.wireRange n logical))
    (pcBound : ∀ n, ((batchProgram bs a.machine.capacities).run a.storageShape.wireRange n logical).done = false →
      ((batchProgram bs a.machine.capacities).run a.storageShape.wireRange n logical).pc < (batchStatements 0 bs).length)
    (r : RTL.InterfaceState a.storageShape) (running : r.Running)
    (same : StorageAgreement a.storageShape r.core.decode logical) (cycles : Nat) :
    ∃ result, SystemVerilog.physicalRun a codes emission.text cycles r = some result ∧
      StorageAgreement a.storageShape result.core.decode
        ((batchProgram bs a.machine.capacities).run a.storageShape.wireRange cycles logical) ∧ result.Running := by
  induction cycles generalizing r logical with
  | zero => exact ⟨r,rfl,same,running⟩
  | succ n ih =>
    let program := batchProgram bs a.machine.capacities
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
        have inside : r.core.pc.toNat < (batchStatements 0 bs).length := by
          change r.core.decode.pc < _
          rw [same.pc]
          exact pcBound 0 logicalLive
        obtain ⟨next,executed,related,busy⟩ := physical_batch_tick a bs hc hn generated r active notDone inside
        have congr := batchTick_storage_congr bs hc same (wr := a.storageShape.wireRange) (capacities := a.machine.capacities)
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
