import IRComparison.Circuit.Counter

namespace IRComparison.Circuit

/-- The logical buffer view may change length after the first iteration. The
actual holding-register bank stays fixed. This theorem tracks that change
without requiring initial and steady-state windows to have equal lengths. -/
theorem counter_iterations_indexed {α : Type} {view : Nat → Payload → α} {cap : Nat → Nat}
    {body : Schedule} {counter stop : Nat} {P : Nat → Payload → Prop} {f : Nat → α → Option α}
    (hview : ∀ j q v, view j (q.setWire counter v) = view j q)
    (hinc : ∀ j q v, P j q → P j (q.setWire counter v))
    (hbody : ∀ (j : Nat) q, j < stop → P j q → q.wires counter = (j:Int) →
      ∃ result, body.Eval cap q result ∧ result.map (view (j+1)) = f j (view j q) ∧
        ∀ t, result = some t → P (j+1) t ∧ t.wires counter = (j:Int))
    (remaining first : Nat) (hn : first + remaining = stop) (p : Payload)
    (hp : P first p) (hk : p.wires counter = (first:Int)) :
    ∃ result,
      (Schedule.loop (.bin .lt (.wire counter) (.lit stop))
        (.seq body (.step (.wire counter (.bin .add (.wire counter) (.lit 1)))))).Eval cap p result ∧
      result.map (view stop) = (List.range' first remaining).foldlM (fun s j => f j s) (view first p) ∧
      ∀ t, result = some t → P stop t ∧ t.wires counter = (stop:Int) := by
  induction remaining generalizing first p with
  | zero =>
    have hs : first = stop := by omega
    subst first
    refine ⟨some p,.loop_stop ?_,rfl,?_⟩
    · simp [Expr.eval,Bin.eval,hk]
    · intro t ht; cases ht; exact ⟨hp,hk⟩
  | succ n ih =>
    have hj : first < stop := by omega
    have guard : (Expr.bin .lt (.wire counter) (.lit stop)).eval p.data p.wires = some 1 := by
      simp [Expr.eval,Bin.eval,hk,show (first:Int) < stop from by omega]
    obtain ⟨r,hr,ho,hpost⟩ := hbody first p hj hp hk
    cases r with
    | none =>
      refine ⟨none,.loop_body_error guard (by decide) (.seq_error hr),?_,?_⟩
      · simp only [List.range'_succ,List.foldlM_cons,← ho]; rfl
      · intro t ht; cases ht
    | some q =>
      obtain ⟨hq,hqk⟩ := hpost q rfl
      let t := q.setWire counter (first+1)
      have htk : t.wires counter = ((first+1:Nat):Int) := by simp [t,Payload.setWire]
      obtain ⟨r',hr',ho',hpost'⟩ := ih (first+1) (by omega) t (hinc _ q _ hq) htk
      have increment : (Schedule.step (.wire counter (.bin .add (.wire counter) (.lit 1)))).Eval cap q (some t) := by
        apply setWire_eval
        simp [Expr.eval,Bin.eval,hqk]
      refine ⟨r',.loop_next guard (by decide) (.seq hr increment) hr',?_,hpost'⟩
      simpa only [List.range'_succ,List.foldlM_cons,← ho,bind,Option.bind,Option.map_some,t,hview] using ho'

end IRComparison.Circuit
