import IRComparison.Circuit.CommandContext
namespace IRComparison.Circuit

theorem setWire_eval (he : e.eval p.data p.wires = some v) :
    (Schedule.step (.wire k e)).Eval cap p (some (p.setWire k v)) := by
  have eq : (Action.wire k e).eval cap p = some (p.setWire k v) := by
    simp [Action.eval,Action.node,execute,Payload.at,Runtime.payload,Runtime.setWire,Payload.setWire,he]
  rw [← eq]; exact .step

theorem setWire_observe : observe output (p.setWire k v) = observe output p := rfl

def LoopResult (P : Payload → Prop) (counter stop : Nat) (result : Option Payload) : Prop :=
  ∀ q, result = some q → P q ∧ q.wires counter = (stop : Int)

/-- A general finite counter loop theorem. The invariant and body semantics
are parameters, so this applies to captured dynamic bounds and nested loops. -/
theorem counter_iterations_by {α : Type} {view : Payload → α} {cap : Nat → Nat} {body : Schedule} {counter stop : Nat}
    {limit : Expr} {P : Payload → Prop} {f : Nat → α → Option α}
    (hview : ∀ q v, view (q.setWire counter v) = view q)
    (hlimit : ∀ p, P p → limit.eval p.data p.wires = some (stop : Int))
    (hinc : ∀ p v, P p → P (p.setWire counter v))
    (hbody : ∀ (j : Nat) p, P p → p.wires counter = (j : Int) →
      ∃ result, body.Eval cap p result ∧ result.map view = f j (view p) ∧ LoopResult P counter j result)
    (remaining first : Nat) (hn : first + remaining = stop) (p : Payload)
    (hp : P p) (hk : p.wires counter = (first : Int)) :
    ∃ result,
      (Schedule.loop (.bin .lt (.wire counter) limit)
        (.seq body (.step (.wire counter (.bin .add (.wire counter) (.lit 1)))))).Eval cap p result ∧
      result.map view = (List.range' first remaining).foldlM (fun s j => f j s) (view p) ∧
      LoopResult P counter stop result := by
  induction remaining generalizing first p with
  | zero =>
    have hs : first = stop := by omega
    refine ⟨some p,Schedule.Eval.loop_stop ?_,rfl,?_⟩
    · simp [Expr.eval,Bin.eval,hk,hlimit p hp,hs]
    · intro q hq; cases hq; exact ⟨hp,by simpa [hs] using hk⟩
  | succ n ih =>
    have hl : (first : Int) < (stop : Int) := by omega
    have hguard : (Expr.bin .lt (.wire counter) limit).eval p.data p.wires = some 1 := by
      simp [Expr.eval,Bin.eval,hk,hlimit p hp,hl]
    obtain ⟨r,hr,ho,hp'⟩ := hbody first p hp hk
    cases r with
    | none =>
      refine ⟨none,Schedule.Eval.loop_body_error hguard (by decide) (.seq_error hr),?_,?_⟩
      · simp only [List.range'_succ,List.foldlM_cons,← ho]; rfl
      · intro q hq; cases hq
    | some q =>
      obtain ⟨hq,hqk⟩ := hp' q rfl
      let t := q.setWire counter (first+1)
      have ht : P t := hinc q _ hq
      have htk : t.wires counter = ((first+1 : Nat) : Int) := by simp [t,Payload.setWire]
      obtain ⟨r',hr',ho',hp''⟩ := ih (first+1) (by omega) t ht htk
      have increment : (Schedule.step (.wire counter (.bin .add (.wire counter) (.lit 1)))).Eval cap q (some t) := by
        apply setWire_eval
        simp [Expr.eval,Bin.eval,hqk]
      refine ⟨r',Schedule.Eval.loop_next hguard (by decide) (.seq hr increment) hr',?_,hp''⟩
      simpa only [List.range'_succ,List.foldlM_cons,← ho,bind,Option.bind,Option.map_some,t,hview] using ho'

theorem counter_iterations {cap : Nat → Nat} {body : Schedule} {counter stop : Nat}
    {limit : Expr} {output : Nat} {P : Payload → Prop} {f : Nat → State × List Int → Option (State × List Int)}
    (hlimit : ∀ p, P p → limit.eval p.data p.wires = some (stop : Int))
    (hinc : ∀ p v, P p → P (p.setWire counter v))
    (hbody : ∀ (j : Nat) p, P p → p.wires counter = (j : Int) →
      ∃ result, body.Eval cap p result ∧ result.map (observe output) = f j (observe output p) ∧ LoopResult P counter j result)
    (remaining first : Nat) (hn : first + remaining = stop) (p : Payload)
    (hp : P p) (hk : p.wires counter = (first : Int)) :
    ∃ result,
      (Schedule.loop (.bin .lt (.wire counter) limit)
        (.seq body (.step (.wire counter (.bin .add (.wire counter) (.lit 1)))))).Eval cap p result ∧
      result.map (observe output) = (List.range' first remaining).foldlM (fun s j => f j s) (observe output p) ∧
      LoopResult P counter stop result := by
  exact counter_iterations_by (view:=observe output) (fun _ _ => rfl) hlimit hinc hbody remaining first hn p hp hk

end IRComparison.Circuit

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
