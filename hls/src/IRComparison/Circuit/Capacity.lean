import IRComparison.Circuit.CommandSound

namespace IRComparison.Circuit

/-- A fold of successful source steps preserves a monotone measure and can be
replayed by capacity-checked steps if the final measure fits. -/
theorem fold_capacity {f g : α → β → Option α} {measure : α → Nat} {capacity : Nat}
    (h : ∀ s a t, f s a = some t → measure s ≤ measure t ∧ (measure t ≤ capacity → g s a = some t))
    (xs : List β) (s t : α) (he : xs.foldlM f s = some t) :
    measure s ≤ measure t ∧ (measure t ≤ capacity → xs.foldlM g s = some t) := by
  induction xs generalizing s with
  | nil => change some s = some t at he; cases he; exact ⟨Nat.le_refl _,fun _ => rfl⟩
  | cons a xs ih =>
    simp only [List.foldlM_cons] at he
    cases hf : f s a with
    | none => simp [hf] at he
    | some u =>
      simp only [hf,bind,Option.bind] at he
      have tail := ih u he
      have head := h s a u hf
      refine ⟨Nat.le_trans head.1 tail.1,fun bound => ?_⟩
      simp only [List.foldlM_cons,head.2 (Nat.le_trans tail.1 bound),bind,Option.bind]
      exact tail.2 bound

/-- A successful source command only appends to its output queue. If the final
queue fits, no intermediate send can overflow. -/
theorem bounded_complete (c : HybridIR.Cmd) (s : State) (q ls : List Int) (t : State) (qs : List Int)
    (he : c.eval i x y s q ls = some (t,qs)) :
    q.length ≤ qs.length ∧ (qs.length ≤ capacity → bounded capacity i x y c s q ls = some (t,qs)) := by
  induction c generalizing s q ls t qs with
  | skip => cases he; exact ⟨Nat.le_refl _,fun _ => rfl⟩
  | assign r e =>
    cases hv : e.eval i x y s ls [] <;> simp [HybridIR.Cmd.eval,hv] at he
    obtain ⟨rfl,rfl⟩ := he
    exact ⟨Nat.le_refl _,fun _ => by simp [bounded,hv]⟩
  | store a j e =>
    cases hj : j.eval i x y s ls [] <;> simp [HybridIR.Cmd.eval,hj] at he
    next k =>
      cases hv : e.eval i x y s ls [] <;> simp [hv] at he
      next v =>
        cases hw : s.write a k v <;> simp [hw] at he
        obtain ⟨rfl,rfl⟩ := he
        exact ⟨Nat.le_refl _,fun _ => by simp [bounded,hj,hv,hw]⟩
  | send e =>
    cases hv : e.eval i x y s ls [] <;> simp [HybridIR.Cmd.eval,hv] at he
    obtain ⟨rfl,rfl⟩ := he
    refine ⟨by simp,fun hc => ?_⟩
    have hq : q.length < capacity := by simpa using hc
    simp [bounded,hv,hq]
  | letValue e b ih =>
    cases hv : e.eval i x y s ls [] <;> simp [HybridIR.Cmd.eval,hv] at he
    next v =>
      have hh := ih s q (v::ls) t qs he
      exact ⟨hh.1,fun hcap => by simpa [bounded,hv] using hh.2 hcap⟩
  | seq a b ia ib =>
    cases ha : a.eval i x y s q ls <;> simp [HybridIR.Cmd.eval,ha] at he
    next pair =>
      obtain ⟨u,qu⟩ := pair
      have hb := ib u qu ls t qs he
      have hh := ia s q ls u qu ha
      refine ⟨Nat.le_trans hh.1 hb.1,fun hc => ?_⟩
      simp only [bounded,hh.2 (Nat.le_trans hb.1 hc),bind,Option.bind]
      exact hb.2 hc
  | branch e a b ia ib =>
    cases hv : e.eval i x y s ls [] <;> simp [HybridIR.Cmd.eval,hv] at he
    next v =>
      by_cases hz : v = 0
      · simp [hz] at he
        have hh := ib s q ls t qs he
        exact ⟨hh.1,fun hc => by simpa [bounded,hv,hz] using hh.2 hc⟩
      · simp [hz] at he
        have hh := ia s q ls t qs he
        exact ⟨hh.1,fun hc => by simpa [bounded,hv,hz] using hh.2 hc⟩
  | «repeat» n b ih =>
    exact fold_capacity (measure:=fun p : State × List Int => p.2.length)
      (fun u _ v hv => ih u.1 u.2 ls v.1 v.2 hv) (List.range n) (s,q) (t,qs) he
  | forRange e b ih =>
    cases hv : e.eval i x y s ls [] <;> simp [HybridIR.Cmd.eval,hv] at he
    next n =>
      have hh := fold_capacity (measure:=fun p : State × List Int => p.2.length)
        (fun u (j : Nat) v hv => ih u.1 u.2 ((j:Int)::ls) v.1 v.2 hv) (List.range n.toNat) (s,q) (t,qs) he
      exact ⟨hh.1,fun hc => by simpa [bounded,hv] using hh.2 hc⟩

theorem fold_refines {f g : α → β → Option α}
    (h : ∀ s a t, g s a = some t → f s a = some t)
    (xs : List β) (he : xs.foldlM g s = some t) : xs.foldlM f s = some t := by
  induction xs generalizing s with
  | nil => exact he
  | cons a xs ih =>
    simp only [List.foldlM_cons] at he ⊢
    cases hg : g s a with
    | none => simp [hg] at he
    | some u =>
      simp only [hg,bind,Option.bind] at he
      simp only [h s a u hg,bind,Option.bind]
      exact ih he

theorem bounded_refines (c : HybridIR.Cmd) (s : State) (q ls : List Int) (t : State) (qs : List Int)
    (he : bounded capacity i x y c s q ls = some (t,qs)) : c.eval i x y s q ls = some (t,qs) := by
  induction c generalizing s q ls t qs with
  | skip | assign | store => exact he
  | send e =>
    cases hv : e.eval i x y s ls [] <;> simp [bounded,hv] at he
    next v =>
      obtain ⟨_,h⟩ := he
      simpa [HybridIR.Cmd.eval,hv] using h
  | letValue e b ih =>
    cases hv : e.eval i x y s ls [] <;> simp [bounded,hv] at he
    next v => simpa [HybridIR.Cmd.eval,hv] using ih s q (v::ls) t qs he
  | seq a b ia ib =>
    cases ha : bounded capacity i x y a s q ls <;> simp [bounded,ha] at he
    next pair =>
      obtain ⟨u,qu⟩ := pair
      simpa [HybridIR.Cmd.eval,ia s q ls u qu ha] using ib u qu ls t qs he
  | branch e a b ia ib =>
    cases hv : e.eval i x y s ls [] <;> simp [bounded,hv] at he
    next v =>
      by_cases hz : v = 0
      · simp [hz] at he
        simpa [HybridIR.Cmd.eval,hv,hz] using ib s q ls t qs he
      · simp [hz] at he
        simpa [HybridIR.Cmd.eval,hv,hz] using ia s q ls t qs he
  | «repeat» n b ih =>
    exact fold_refines (fun u _ v hv => ih u.1 u.2 ls v.1 v.2 hv) (List.range n) he
  | forRange e b ih =>
    cases hv : e.eval i x y s ls [] <;> simp [bounded,hv] at he
    next n =>
      have hh := fold_refines (fun u (j : Nat) v hv => ih u.1 u.2 ((j:Int)::ls) v.1 v.2 hv) (List.range n.toNat) he
      simpa [HybridIR.Cmd.eval,hv] using hh

theorem bounded_failure (h : c.eval i x y s q ls = none) : bounded capacity i x y c s q ls = none := by
  cases he : bounded capacity i x y c s q ls with
  | none => rfl
  | some pair =>
    obtain ⟨t,qs⟩ := pair
    have hs := bounded_refines c s q ls t qs he
    rw [h] at hs
    cases hs

/-- Capacity affects acceptance only when a successful source execution would
produce a queue longer than the physical FIFO. -/
theorem bounded_eq (c : HybridIR.Cmd)
    (fits : ∀ t qs, c.eval i x y s q ls = some (t,qs) → qs.length ≤ capacity) :
    bounded capacity i x y c s q ls = c.eval i x y s q ls := by
  cases he : c.eval i x y s q ls with
  | none => exact bounded_failure he
  | some pair =>
      obtain ⟨t,qs⟩ := pair
      exact (bounded_complete c s q ls t qs he).2 (fits t qs he)

/-- The entire generated command controller reaches the source result,
including failure, when its output-capacity obligation is satisfied. -/
theorem command_finishes (c : HybridIR.Cmd) (b : Build) (i : Expr) (ls : List Expr)
    (p : Payload) (iv xv yv : Int) (lvs : List Int)
    (ctx : Context b.wires.size i ls p iv xv yv lvs)
    (capacities : Array (Nat × Nat))
    (fits : ∀ t qs, c.eval iv xv yv p.data (p.queues output) lvs = some (t,qs) →
      qs.length ≤ ((command i ls output c b).1.assemble capacities).capacity output) :
    let machine := (command i ls output c b).1.assemble capacities
    ∃ cycles, (machine.run cycles (p.at 1)).result =
      some ((c.eval iv xv yv p.data (p.queues output) lvs).map Prod.fst) := by
  let control := (command i ls output c b).1
  obtain ⟨result,he,ho⟩ := command_correct (cap:=(control.assemble capacities).capacity) c b i ls p iv xv yv lvs ctx
  rw [bounded_eq c fits] at ho
  obtain ⟨cycles,hc⟩ := control.assemble_finishes p he
  refine ⟨cycles,?_⟩
  rw [hc,← ho]
  simp only [Option.map_map]
  rfl

end IRComparison.Circuit
