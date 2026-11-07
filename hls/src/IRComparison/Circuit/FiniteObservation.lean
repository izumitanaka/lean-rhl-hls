import IRComparison.Circuit.StorageCheck

namespace IRComparison.Circuit

theorem execute_register_frame (node : Node) (closed : node.inStorage shape)
    (outside : shape.registers ≤ k) (he : execute cap node r = some t) : t.data.regs k = r.data.regs k := by
  cases node <;> simp only [execute] at he
  case halt | jump | snapshot | erase | clear => cases he; rfl
  case wire slot e n =>
    cases hv : e.eval r.data r.wires <;> simp [hv] at he
    cases he; rfl
  case assign slot e n =>
    cases hv : e.eval r.data r.wires <;> simp [hv] at he
    cases he
    have ne : k ≠ slot := by have := closed.1; omega
    simp [State.set,ne]
  case store a j e n =>
    cases hj : j.eval r.data r.wires <;> simp [hj] at he
    next index =>
      cases hv : e.eval r.data r.wires <;> simp [hv] at he
      next value =>
        cases hs : r.data.write a index value <;> simp [hs] at he
        next data =>
          cases he
          unfold State.write at hs
          split at hs
          · cases hs
          · split at hs
            · cases hs; rfl
            · cases hs
  case branch e yes no =>
    cases hv : e.eval r.data r.wires <;> simp [hv] at he
    cases he; rfl
  case send q e n =>
    cases hv : e.eval r.data r.wires <;> simp [hv] at he
    next value => obtain ⟨_,rfl⟩ := he; rfl
  case receive q slot n =>
    cases hq : r.queues q <;> simp [hq] at he
    cases he; rfl

theorem tick_register_frame {m : Machine} (closed : ∀ node ∈ m.nodes.toList, node.inStorage shape)
    (outside : shape.registers ≤ k) : (m.tick r).data.regs k = r.data.regs k := by
  by_cases hd : r.done = true
  · simp [Machine.tick,hd]
  · cases hn : m.nodes[r.pc]? with
    | none => simp [Machine.tick,hd,hn]
    | some node =>
      have hc := closed node (by simpa using Array.mem_of_getElem? hn)
      cases he : execute m.capacity node r with
      | none => simp [Machine.tick,hd,hn,he]
      | some t => simpa [Machine.tick,hd,hn,he] using execute_register_frame node hc outside he

theorem run_register_frame {m : Machine} (closed : ∀ node ∈ m.nodes.toList, node.inStorage shape)
    (outside : shape.registers ≤ k) (cycles : Nat) : (m.run cycles r).data.regs k = r.data.regs k := by
  induction cycles generalizing r with
  | zero => rfl
  | succ n ih => exact ih.trans (tick_register_frame closed outside)

/-- Proof-only reconstruction of the untouched complement of the finite
register interface. `initial` is not stored in hardware or consulted by tick.
This lets the full source-state observation retain arbitrary unused registers. -/
def FiniteRuntime.readback (initial : State) (r : FiniteRuntime shape) : State where
  regs := fun n => if n < shape.registers then r.decode.data.regs n else initial.regs n
  arrays := r.decode.data.arrays

def FiniteRuntime.result (initial : State) (r : FiniteRuntime shape) : Option (Option State) :=
  if r.done then some (if r.error then none else some (r.readback initial)) else none

/-- Observation depends on live storage agreement, not on unused physical
cells or the particular constructor used for the initial finite state. -/
theorem observation_from_agreement {m : Machine}
    (closed : ∀ node ∈ m.nodes.toList, node.inStorage shape)
    (initial : Runtime) (cycles : Nat) (finite : FiniteRuntime shape)
    (same : StorageAgreement shape finite.decode (m.run cycles initial))
    (outputsSafe : ∀ n ∈ outputs, shape.hasMemory n) :
    (finite.result initial.data).map (Option.map (PipelineUse.observe outputs)) =
      (m.run cycles initial).result.map (Option.map (PipelineUse.observe outputs)) := by
  let logical := m.run cycles initial
  have regs : (finite.readback initial.data).regs = logical.data.regs := by
    funext n
    by_cases hn : n < shape.registers
    · exact (if_pos hn).trans (same.regs n hn)
    · change (if n < shape.registers then _ else _) = _
      rw [if_neg hn]
      exact (run_register_frame (r:=initial) closed (by omega : shape.registers ≤ n) cycles).symm
  have arrays : outputs.map (finite.readback initial.data).arrays = outputs.map logical.data.arrays := by
    apply List.map_congr_left
    intro n hn
    exact same.arrays n (outputsSafe n hn)
  change (finite.result initial.data).map _ = logical.result.map _
  have hd : finite.done = logical.done := same.done
  have he : finite.error = logical.error := same.error
  simp only [FiniteRuntime.result,Runtime.result,hd,he]
  split
  · split
    · rfl
    · simp only [Option.map_some,PipelineUse.observe,regs,arrays]
  · rfl

theorem finite_observation_from_initial (certificate : StorageCertificate a)
    (valid : validInvariant a table = true) (inputs : 2 ≤ a.wires.size)
    (s : HybridWord.State) (x y : HybridWord.Word) (fits : a.InputFits s.encode)
    (physical : FiniteRuntime a.storageShape)
    (initial : StorageAgreement a.storageShape physical.decode
      (a.machine.start s.encode (HybridWord.encode x) (HybridWord.encode y)))
    (outputsSafe : ∀ n ∈ outputs, a.storageShape.hasMemory n) (cycles : Nat) :
    ((FiniteRuntime.run a.machine a.storageShape cycles physical).result s.encode).map
      (Option.map (PipelineUse.observe outputs)) =
      (a.machine.run cycles (a.machine.start s.encode (HybridWord.encode x) (HybridWord.encode y))).result.map
        (Option.map (PipelineUse.observe outputs)) := by
  apply observation_from_agreement certificate.closed
    (a.machine.start s.encode (HybridWord.encode x) (HybridWord.encode y)) cycles _ _ outputsSafe
  exact finiteRun_from_agreement certificate.closed
    (storage_reachable certificate valid inputs s x y fits)
    (fun n => reachable_widths valid inputs s x y n) physical initial cycles

theorem finite_observation (certificate : StorageCertificate a)
    (valid : validInvariant a table = true) (inputs : 2 ≤ a.wires.size)
    (s : HybridWord.State) (x y : HybridWord.Word) (fits : a.InputFits s.encode)
    (outputsSafe : ∀ n ∈ outputs, a.storageShape.hasMemory n) (cycles : Nat) :
    let finite := FiniteRuntime.run a.machine a.storageShape cycles
      (FiniteRuntime.pack a.storageShape (a.machine.start s.encode (HybridWord.encode x) (HybridWord.encode y)))
    (finite.result s.encode).map (Option.map (PipelineUse.observe outputs)) =
      (a.machine.run cycles (a.machine.start s.encode (HybridWord.encode x) (HybridWord.encode y))).result.map
        (Option.map (PipelineUse.observe outputs)) := by
  exact finite_observation_from_initial certificate valid inputs s x y fits _
    (FiniteRuntime.pack_correct (storage_reachable certificate valid inputs s x y fits 0)) outputsSafe cycles

end IRComparison.Circuit
