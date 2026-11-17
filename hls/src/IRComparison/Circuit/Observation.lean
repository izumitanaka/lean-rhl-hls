import IRComparison.Circuit.StorageShape

namespace IRComparison.Circuit

/-- Common successful/failed final observation. The array relation selects
which arrays are public; intermediate storage and failure-state data are not
observable. Different frontends specialize this relation, not its semantics. -/
def ResultObservation (registers : Nat) (arrays : State → State → Prop)
    (r : Runtime) (expected : Option State) : Prop :=
  r.done = true ∧ match expected with
    | none => r.error = true
    | some s => r.error = false ∧
        (∀ n, n < registers → r.data.regs n = s.regs n) ∧ arrays r.data s

theorem ResultObservation.of_agreement
    (same : StorageAgreement shape r logical) (h : logical.result = some expected)
    (select : ∀ a b : State,
      (∀ n, shape.hasMemory n → a.arrays n = b.arrays n) → arrays a b) :
    ResultObservation shape.registers arrays r expected := by
  unfold Runtime.result at h
  cases hd : logical.done <;> simp [hd] at h
  cases he : logical.error <;> simp [he] at h
  · subst expected
    exact ⟨same.done.trans hd,same.error.trans he,same.regs,select _ _ same.arrays⟩
  · subst expected
    exact ⟨same.done.trans hd,same.error.trans he⟩

end IRComparison.Circuit
