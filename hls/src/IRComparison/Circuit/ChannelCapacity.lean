import IRComparison.Circuit.ChannelSound

namespace IRComparison.Circuit.ChannelLower
open HybridIR

/-- A conservative bound on total sends, hence also on sends to each channel.
Unknown bounds reject an allocation, not the source program. -/
def sendBudget : ChannelCmd → Option Nat
  | .send .. => some 1
  | .seq a b => do return (← sendBudget a) + (← sendBudget b)
  | .branch _ a b => do return max (← sendBudget a) (← sendBudget b)
  | .letValue _ b | .letBuffer _ b => sendBudget b
  | .repeat n b => (sendBudget b).map (n * ·)
  | .forRange e b => if sendBudget b = some 0 then some 0 else
      match e with
      | .pure (.lit count) => (sendBudget b).map (count.toNat * ·)
      | _ => none
  | _ => some 0

/-- Channels that may receive a send; this traverses syntax, not iterations. -/
def sentChannels : ChannelCmd → List Nat
  | .send q _ => [q]
  | .seq a b | .branch _ a b => sentChannels a ++ sentChannels b
  | .letValue _ b | .letBuffer _ b | .repeat _ b | .forRange _ b => sentChannels b
  | _ => []

def Fits (cap : Nat → Nat) (channels : List Nat) (n : Nat) (s : ChannelState) : Prop :=
  ∀ q, (s.queues q).length + (if q ∈ channels then n else 0) ≤ cap q

def Growth (channels : List Nat) (n : Nat) (s t : ChannelState) : Prop :=
  ∀ q, (t.queues q).length ≤ (s.queues q).length + (if q ∈ channels then n else 0)

/-- Equality includes failures. The growth clause makes sequential and loop
composition possible even when a command both sends and receives. -/
def Budgeted (cap : Nat → Nat) (channels : List Nat) (n : Nat)
    (logical finite : ChannelState → Option ChannelState) : Prop :=
  ∀ s, Fits cap channels n s → finite s = logical s ∧
    ∀ t, logical s = some t → Growth channels n s t

theorem Budgeted.weaken (h : Budgeted cap channels n f g) (le : n ≤ m) : Budgeted cap channels m f g := by
  intro s fits
  have h' := h s (fun q => by have := fits q; by_cases hq : q ∈ channels <;> simp only [hq,ite_true,ite_false] at * <;> omega)
  exact ⟨h'.1,fun t ht q => by have := h'.2 t ht q; dsimp [Growth] at *; by_cases hq : q ∈ channels <;> simp only [hq,ite_true,ite_false] at * <;> omega⟩

theorem Budgeted.seq (a : Budgeted cap channels m f f') (b : Budgeted cap channels n g g') :
    Budgeted cap channels (m+n) (fun s => (f s).bind g) (fun s => (f' s).bind g') := by
  intro s fits
  have ha := a s (fun q => by have := fits q; by_cases hq : q ∈ channels <;> simp only [hq,ite_true,ite_false] at * <;> omega)
  dsimp only
  rw [ha.1]
  cases hs : f s with
  | none => exact ⟨rfl,by simp⟩
  | some mid =>
    have grow := ha.2 mid hs
    have hb := b mid (fun q => by have := fits q; have := grow q; by_cases hq : q ∈ channels <;> simp only [hq,ite_true,ite_false] at * <;> omega)
    exact ⟨hb.1,fun t ht q => by have := hb.2 t ht q; have := grow q; by_cases hq : q ∈ channels <;> simp only [hq,ite_true,ite_false] at * <;> omega⟩

theorem Budgeted.fold (items : List α)
    (step : ∀ a, Budgeted cap channels n (fun s => f s a) (fun s => g s a)) :
    Budgeted cap channels (items.length*n) (fun s => items.foldlM f s) (fun s => items.foldlM g s) := by
  induction items with
  | nil => exact fun s _ => ⟨rfl,fun t ht q => by cases ht; simp⟩
  | cons a as ih =>
    simpa [List.foldlM_cons,Nat.add_mul,Nat.add_comm] using (step a).seq ih

private theorem unchanged (f : ChannelState → Option ChannelState)
    (h : ∀ s t, f s = some t → t.queues = s.queues) : Budgeted cap channels 0 f f := by
  intro s _
  exact ⟨rfl,fun t ht q => by rw [h s t ht]; simp⟩

/-- Checked send bounds are sufficient for the real capacity-aware evaluator.
This is a bound on execution, not generation-time loop expansion. -/
theorem sendBudget_sound (c : ChannelCmd) (hb : sendBudget c = some n)
    (support : ∀ q ∈ sentChannels c, q ∈ channels) :
    Budgeted cap channels n (fun s => c.eval i x y s ls) (fun s => bounded cap i x y c s ls) := by
  induction c generalizing n ls with
  | skip => cases hb; exact unchanged _ (by intro s t h; cases h; rfl)
  | assign r e =>
    cases hb
    exact unchanged _ (by intro s t h; cases he : e.eval i x y s.data ls [] <;> simp [ChannelCmd.eval,he] at h; cases h; rfl)
  | store a j e =>
    cases hb
    exact unchanged _ (by
      intro s t h
      cases hj : j.eval i x y s.data ls [] with
      | none => simp [ChannelCmd.eval,hj] at h
      | some k =>
        cases he : e.eval i x y s.data ls [] with
        | none => simp [ChannelCmd.eval,hj,he] at h
        | some v =>
          cases hw : s.data.write a k v <;> simp [ChannelCmd.eval,hj,he,hw] at h
          cases h; rfl)
  | hold b e =>
    cases hb
    exact unchanged _ (by intro s t h; cases he : e.eval i x y s.data ls [] <;> simp [ChannelCmd.eval,he] at h; cases h; rfl)
  | receive a b =>
    cases hb
    intro s _
    refine ⟨rfl,?_⟩
    intro t ht q
    cases hq : s.queues a with
    | nil => simp [ChannelCmd.eval,ChannelState.receive,hq] at ht
    | cons v rest =>
      simp only [ChannelCmd.eval,ChannelState.receive,hq,Option.some.injEq] at ht
      cases ht
      by_cases h : q = a
      · subst q; simp [ChannelState.setBuffer,ChannelState.setQueue,hq]
      · simp [ChannelState.setBuffer,ChannelState.setQueue,h]
  | send a e =>
    cases hb
    intro s fits
    have ha : (s.queues a).length < cap a := by have := fits a; have ha := support a (by simp [sentChannels]); simp only [ha,ite_true] at this; omega
    refine ⟨by simp [bounded,ChannelCmd.eval,ha],?_⟩
    intro t ht q
    cases he : e.eval i x y s.data ls [] with
    | none => simp [ChannelCmd.eval,he] at ht
    | some v =>
      simp only [ChannelCmd.eval,he,bind,Option.bind,Option.some.injEq] at ht
      cases ht
      by_cases h : q = a <;> simp [ChannelState.send,ChannelState.setQueue,h,show a ∈ channels from support a (by simp [sentChannels])]
  | seq a b ia ib =>
    cases ha : sendBudget a with
    | none => simp [sendBudget,ha] at hb
    | some m =>
      cases hc : sendBudget b with
      | none => simp [sendBudget,ha,hc] at hb
      | some k =>
        simp only [sendBudget,ha,hc,bind,Option.bind,pure,Option.some.injEq] at hb
        subst n
        exact (ia ha (fun q hq => support q (by simp [sentChannels,hq]))).seq (ib hc (fun q hq => support q (by simp [sentChannels,hq])))
  | branch e a b ia ib =>
    cases ha : sendBudget a with
    | none => simp [sendBudget,ha] at hb
    | some m =>
      cases hc : sendBudget b with
      | none => simp [sendBudget,ha,hc] at hb
      | some k =>
        simp only [sendBudget,ha,hc,bind,Option.bind,pure,Option.some.injEq] at hb
        subst n
        intro s fits
        cases he : e.eval i x y s.data ls [] with
        | none => exact ⟨by simp [bounded,ChannelCmd.eval,he],by simp [ChannelCmd.eval,he]⟩
        | some v =>
          simp only [ChannelCmd.eval,bounded,he,bind,Option.bind]
          split
          · exact (ia ha (fun q hq => support q (by simp [sentChannels,hq]))).weaken (Nat.le_max_left _ _) s fits
          · exact (ib hc (fun q hq => support q (by simp [sentChannels,hq]))).weaken (Nat.le_max_right _ _) s fits
  | letValue e c ih =>
    intro s fits
    cases he : e.eval i x y s.data ls [] with
    | none => exact ⟨by simp [bounded,ChannelCmd.eval,he],by simp [ChannelCmd.eval,he]⟩
    | some v => simpa [bounded,ChannelCmd.eval,he] using ih hb support (ls:=v::ls) s fits
  | letBuffer b c ih =>
    intro s fits
    cases he : s.buffers b with
    | none => exact ⟨by simp [bounded,ChannelCmd.eval,he],by simp [ChannelCmd.eval,he]⟩
    | some v => simpa [bounded,ChannelCmd.eval,he] using ih hb support (ls:=v::ls) s fits
  | «repeat» count c ih =>
    cases hc : sendBudget c with
    | none => simp [sendBudget,hc] at hb
    | some k =>
      simp only [sendBudget,hc,Option.map_some,Option.some.injEq] at hb
      subst n
      exact (by simpa using Budgeted.fold (List.range count) (fun (_:Nat) => ih hc support (ls:=ls)))
  | forRange e c ih =>
    by_cases hc : sendBudget c = some 0
    · simp only [sendBudget,hc,ite_true,Option.some.injEq] at hb
      subst n
      intro s fits
      cases he : e.eval i x y s.data ls [] with
      | none => exact ⟨by simp [bounded,ChannelCmd.eval,he],by simp [ChannelCmd.eval,he]⟩
      | some v =>
        have h := Budgeted.fold (List.range v.toNat) (fun (k:Nat) => ih hc support (ls:=(k:Int)::ls))
        simpa [bounded,ChannelCmd.eval,he] using h s fits
    · cases e with
      | pure e =>
        cases e with
        | lit count =>
          cases hs : sendBudget c with
          | none => simp [sendBudget,hc,hs] at hb
          | some m =>
            have hm : m ≠ 0 := by intro hz; exact hc (hs.trans (congrArg some hz))
            simp only [sendBudget,hs,Option.some.injEq,hm,ite_false,Option.map_some] at hb
            subst n
            have h := Budgeted.fold (List.range count.toNat)
              (fun (k:Nat) => ih hs support (ls:=(k:Int)::ls))
            simpa [bounded,ChannelCmd.eval,ReadCode.eval,Value.eval] using h
        | index | left | right | «local» | temp | natIndex | wrap32 | add | sub | mul | div =>
          simp [sendBudget,hc] at hb
      | register | memory | bind | branch => simp [sendBudget,hc] at hb

/-- Only channels receiving sends can affect capacity-aware execution. -/
theorem bounded_congr (c : ChannelCmd) (same : ∀ q ∈ sentChannels c, cap q = other q) :
    bounded cap i x y c s ls = bounded other i x y c s ls := by
  induction c generalizing s ls with
  | skip | assign | store | hold | receive => rfl
  | send q e => simp only [bounded,same q (by simp [sentChannels])]
  | letValue e c ih =>
    simp only [bounded]
    cases e.eval i x y s.data ls [] <;> simp_all [sentChannels]
  | letBuffer b c ih =>
    simp only [bounded]
    cases s.buffers b <;> simp_all [sentChannels]
  | seq a b ia ib =>
    have ha := ia (s:=s) (ls:=ls) (fun q hq => same q (by simp [sentChannels,hq]))
    have hb := fun s => ib (s:=s) (ls:=ls) (fun q hq => same q (by simp [sentChannels,hq]))
    simp only [bounded,ha,hb]
  | branch e a b ia ib =>
    have ha := ia (s:=s) (ls:=ls) (fun q hq => same q (by simp [sentChannels,hq]))
    have hb := ib (s:=s) (ls:=ls) (fun q hq => same q (by simp [sentChannels,hq]))
    simp only [bounded,ha,hb]
  | «repeat» n c ih =>
    have hf : (fun s (_:Nat) => bounded cap i x y c s ls) =
        (fun s (_:Nat) => bounded other i x y c s ls) := by
      funext s k; exact ih same
    simp only [bounded,hf]
  | forRange e c ih =>
    have hf : (fun s (k:Nat) => bounded cap i x y c s ((k:Int)::ls)) =
        (fun s (k:Nat) => bounded other i x y c s ((k:Int)::ls)) := by
      funext s k; exact ih same
    simp only [bounded,hf]

end IRComparison.Circuit.ChannelLower
