import IRComparison.Hybrid.ChannelScope
import IRComparison.Hybrid.HybridCompactFIFO

namespace IRComparison.ChannelBuffers
open HybridIR

/-- Bind every old cell before overwriting any cell. Binding order gives
locals in slot order; copies never see a partially updated window. -/
def capture (slots : List Nat) (body : ChannelCmd) : ChannelCmd :=
  slots.foldl (fun c slot => .letBuffer slot c) body

theorem capture_correct (slots : List Nat) (body : ChannelCmd) :
    (capture slots body).eval i x y s ls = (do
      let values ← slots.mapM s.buffers
      body.eval i x y s (values++ls)) := by
  induction slots generalizing body ls with
  | nil => rfl
  | cons a as ih =>
    simp only [capture,List.foldl_cons] at *
    rw [ih]
    simp only [List.mapM_cons]
    cases ha : s.buffers a <;> cases ht : as.mapM s.buffers <;>
      simp [ha,ht,ChannelCmd.eval,List.cons_append]

def pop (channel buffer : Nat) : Nat → ChannelState → Option ChannelState
  | 0,s => some s
  | n+1,s => (s.receive channel buffer).bind (pop channel buffer n)

theorem pop_fold (items : List α) :
    items.foldlM (fun t _ => t.receive channel buffer) s = pop channel buffer items.length s := by
  induction items generalizing s with
  | nil => rfl
  | cons a as ih =>
    simp only [List.foldlM_cons,List.length_cons,pop]
    cases s.receive channel buffer <;> simp_all

theorem pop_correct (n : Nat) (s : ChannelState) :
    pop channel buffer (n+1) s = (s.queues channel)[n]?.map
      (fun value => (s.setQueue channel ((s.queues channel).drop (n+1))).setBuffer buffer value) := by
  induction n generalizing s with
  | zero =>
    cases hq : s.queues channel <;> simp [pop,ChannelState.receive,hq]
  | succ n ih =>
    cases hq : s.queues channel with
    | nil => simp [pop,ChannelState.receive,hq]
    | cons v vs =>
      rw [pop]
      simp only [ChannelState.receive,hq,Option.bind_some]
      rw [ih]
      simp only [ChannelState.setBuffer,ChannelState.setQueue,ite_true,List.getElem?_cons_succ,List.drop_succ_cons]
      congr 1
      funext value
      congr 1 <;> (funext a; split <;> simp_all)

/-- The final receive keeps the requested element; all preceding receives
are destructive discards. The loop count is an expression, not expanded code. -/
def take (channel buffer : Nat) (discard : Value) : ChannelCmd :=
  .forRange (.pure (.add (.natIndex discard) (.lit 1))) (.receive channel buffer)

theorem take_correct {discard : Value} {d : Int} (he : discard.eval i x y ls [] = some d) :
    (take channel buffer discard).eval i x y s ls = (s.queues channel)[d.toNat]?.map
      (fun value => (s.setQueue channel ((s.queues channel).drop (d.toNat+1))).setBuffer buffer value) := by
  simp only [take,ChannelCmd.eval,ReadCode.eval,Value.eval,he,bind,Option.bind,pure]
  have hn : (Int.ofNat d.toNat+1).toNat = d.toNat+1 := by
    change ((d.toNat:Int)+1).toNat = d.toNat+1
    omega
  rw [hn,pop_fold,List.length_range,pop_correct]

end IRComparison.ChannelBuffers
