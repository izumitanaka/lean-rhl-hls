import IRComparison.Circuit.Machine

namespace IRComparison.Circuit

/-- Finite execution, with the exact number of cycles available separately. -/
inductive Steps (m : Machine) : Runtime → Runtime → Prop where
  | refl (r) : Steps m r r
  | next : Steps m (m.tick r) t → Steps m r t

namespace Steps

theorem trans (h : Steps m r s) (k : Steps m s t) : Steps m r t := by
  induction h with
  | refl => exact k
  | next _ ih => exact .next (ih k)

theorem finite (h : Steps m r t) : ∃ cycles, m.run cycles r = t := by
  induction h with
  | refl => exact ⟨0,rfl⟩
  | next _ ih => obtain ⟨n,hn⟩ := ih; exact ⟨n+1,hn⟩

theorem one (h : m.tick r = t) : Steps m r t := by
  rw [← h]; exact .next (.refl _)

end Steps

theorem tick_node {m : Machine} {r : Runtime} {instruction : Node}
    (hd : r.done = false) (hn : m.nodes[r.pc]? = some instruction)
    (he : execute m.capacity instruction r = some t) : m.tick r = t := by
  simp [Machine.tick,hd,hn,he]

theorem tick_failure {m : Machine} {r : Runtime} {instruction : Node}
    (hd : r.done = false) (hn : m.nodes[r.pc]? = some instruction)
    (he : execute m.capacity instruction r = none) :
    m.tick r = { r with done := true, error := true } := by
  simp [Machine.tick,hd,hn,he]

/-- A statement fragment ends at a continuation on success. Evaluation failure
must reach the explicit error terminal; it is not a divergence assumption. -/
def Outcome (next : Nat) (result : Option Runtime) (actual : Runtime) : Prop :=
  match result with
  | none => actual.done = true ∧ actual.error = true
  | some t => actual = { t with pc := next }

def Implements (m : Machine) (entry next : Nat) (sem : Runtime → Option Runtime) : Prop :=
  ∀ r, r.pc = entry → r.done = false →
    ∃ t, Steps m r t ∧ Outcome next (sem r) t

/-- Single-node fragments include an explicit failure edge. -/
theorem implements_node {m : Machine} {entry next : Nat} {instruction : Node}
    (hn : m.nodes[entry]? = some instruction)
    (hpc : ∀ r t, execute m.capacity instruction r = some t → t.pc = next) :
    Implements m entry next (execute m.capacity instruction) := by
  intro r hp hd
  have hn' : m.nodes[r.pc]? = some instruction := by simpa [hp] using hn
  cases he : execute m.capacity instruction r with
  | none =>
    refine ⟨{ r with done := true, error := true },Steps.one (tick_failure hd hn' he),?_⟩
    simp [Outcome,he]
  | some t =>
    refine ⟨t,Steps.one (tick_node hd hn' he),?_⟩
    simp only [Outcome,he]
    have ht := hpc r t he
    cases t
    simp_all

/-- Fragment composition. The second fragment receives the intermediate
architectural state and holding registers produced by the first one. -/
theorem implements_seq {m : Machine} {entry mid next : Nat} {first second : Runtime → Option Runtime}
    (ha : Implements m entry mid first) (hb : Implements m mid next second)
    (halive : ∀ r s, r.done = false → first r = some s → s.done = false) :
    Implements m entry next (fun r => (first r).bind (fun s => second { s with pc := mid })) := by
  intro r hp hd
  obtain ⟨s,hs,ho⟩ := ha r hp hd
  cases he : first r with
  | none => exact ⟨s,hs,by simpa [he,Outcome] using ho⟩
  | some u =>
      have hu : s = { u with pc := mid } := by simpa [Outcome,he] using ho
      subst s
      obtain ⟨t,ht,hot⟩ := hb { u with pc := mid } rfl (halive r u hd he)
      exact ⟨t,hs.trans ht,by simpa [he] using hot⟩

end IRComparison.Circuit
