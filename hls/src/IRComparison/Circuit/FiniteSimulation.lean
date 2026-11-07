import IRComparison.Circuit.StorageCongruence

namespace IRComparison.Circuit

theorem FiniteRuntime.pack_congr (h : StorageAgreement s r t) : FiniteRuntime.pack s r = FiniteRuntime.pack s t := by
  unfold pack
  congr 1
  · rw [h.pc]
  · funext n; rw [h.regs n.val n.isLt]
  · funext a
    by_cases live : s.memoryLive a.val = true
    · simp only [live,↓reduceIte,h.arrays a.val ⟨a.isLt,live⟩]
    · simp [live]
  · funext n; rw [h.wires n.val n.isLt]
  · funext q; rw [h.queues q.val q.isLt]
  · exact h.done
  · exact h.error

theorem finiteTick_correct (closed : ∀ node ∈ m.nodes.toList, node.inStorage s)
    (bounded : StorageBound s r)
    (widths : r.done = false → InputsBound r.data r.wires s.wireRange) :
    FiniteRuntime.tick m s (FiniteRuntime.pack s r) = FiniteRuntime.pack s (m.tick r) := by
  unfold FiniteRuntime.tick
  have same := bitTick_storage_congr (wr:=s.wireRange) closed (FiniteRuntime.pack_correct bounded)
  rw [FiniteRuntime.pack_congr same,bitTick_correct widths]

/-- Clock-by-clock refinement of all finite banks together. The subsequent
storage-safety theorem discharges the reachable-bound premise statically. -/
theorem finiteRun_correct {m : Machine} (closed : ∀ node ∈ m.nodes.toList, node.inStorage s)
    (bounded : ∀ n, StorageBound s (m.run n r))
    (widths : ∀ n, (m.run n r).done = false →
      InputsBound (m.run n r).data (m.run n r).wires s.wireRange) (cycles : Nat) :
    FiniteRuntime.run m s cycles (FiniteRuntime.pack s r) = FiniteRuntime.pack s (m.run cycles r) := by
  induction cycles generalizing r with
  | zero => rfl
  | succ n ih =>
    rw [FiniteRuntime.run,finiteTick_correct (r:=r) closed (bounded 0) (widths 0)]
    exact ih (fun k => bounded (k+1)) (fun k => widths (k+1))

theorem finiteRun_agrees {m : Machine} (closed : ∀ node ∈ m.nodes.toList, node.inStorage s)
    (bounded : ∀ n, StorageBound s (m.run n r))
    (widths : ∀ n, (m.run n r).done = false →
      InputsBound (m.run n r).data (m.run n r).wires s.wireRange) (cycles : Nat) :
    StorageAgreement s (FiniteRuntime.run m s cycles (FiniteRuntime.pack s r)).decode (m.run cycles r) := by
  rw [finiteRun_correct closed bounded widths]
  exact FiniteRuntime.pack_correct (bounded cycles)

/-- The initial physical state need not be the canonical zero-padded `pack`.
Only observable, declared storage must agree with the logical initial state.
In particular, unused memory/FIFO cells may contain arbitrary fixed words. -/
theorem finiteTick_from_agreement {m : Machine} (closed : ∀ node ∈ m.nodes.toList, node.inStorage s)
    (initial : StorageAgreement s physical.decode r)
    (widths : r.done = false → InputsBound r.data r.wires s.wireRange) :
    FiniteRuntime.tick m s physical = FiniteRuntime.pack s (m.tick r) := by
  unfold FiniteRuntime.tick
  rw [FiniteRuntime.pack_congr (bitTick_storage_congr (wr:=s.wireRange) closed initial),
    bitTick_correct widths]

theorem finiteRun_from_agreement {m : Machine} (closed : ∀ node ∈ m.nodes.toList, node.inStorage s)
    (bounded : ∀ n, StorageBound s (m.run n r))
    (widths : ∀ n, (m.run n r).done = false →
      InputsBound (m.run n r).data (m.run n r).wires s.wireRange)
    (physical : FiniteRuntime s) (initial : StorageAgreement s physical.decode r) (cycles : Nat) :
    StorageAgreement s (FiniteRuntime.run m s cycles physical).decode (m.run cycles r) := by
  cases cycles with
  | zero => exact initial
  | succ n =>
    rw [FiniteRuntime.run,finiteTick_from_agreement closed initial (widths 0)]
    exact finiteRun_agrees closed (fun k => bounded (k+1)) (fun k => widths (k+1)) n

end IRComparison.Circuit
