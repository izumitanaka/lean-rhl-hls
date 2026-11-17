import IRComparison.Circuit.SharedBuilderRelation

namespace IRComparison.Circuit.Shared
open BuilderRelated

theorem small_simulates (s : Circuit.Schedule) : s.Simulates (s.mapExpressions ofExpr) := by
  induction s with
  | skip => exact .skip
  | step a =>
    apply Schedule.Simulates.step
    intro cap p
    cases a <;> simp [Action.mapExpressions,Action.eval,Action.node,execute]
  | seq a b ia ib => exact ia.seq ib
  | branch e a b ia ib => exact Schedule.Simulates.branch (by intros; simp) ia ib
  | loop e body ih => exact Schedule.Simulates.loop (by intros; simp) ih

theorem small_related (f : Builder Circuit.Schedule) (h : BuilderRelated Eq f f) :
    BuilderRelated Schedule.Simulates f (small f) := by
  intro a b same
  have pair := h a b same
  exact ⟨by simpa only [small,pair.1] using small_simulates (f b).1,pair.2⟩

theorem take_related (q slot : Nat) (e : Circuit.Expr) :
    BuilderRelated Eq (Circuit.take q slot e) (Circuit.take q slot e) := by
  intro a b h
  let a1 := a.addWire (a.exprRange e.natIndex)
  let a2 := a1.addWire (a1.exprRange e.natIndex)
  let b1 := b.addWire (b.exprRange e.natIndex)
  let b2 := b1.addWire (b1.exprRange e.natIndex)
  change
    (Schedule.seq (.step (.wire a.wires.size e.natIndex))
      (.seq (Circuit.counterLoop a1.wires.size (.wire a.wires.size) (.step (.receive q a2.wires.size)))
        (.step (.receive q slot)))) =
    (Schedule.seq (.step (.wire b.wires.size e.natIndex))
      (.seq (Circuit.counterLoop b1.wires.size (.wire b.wires.size) (.step (.receive q b2.wires.size)))
        (.step (.receive q slot)))) ∧ BuildRelated (a2.addWire wordRange) (b2.addWire wordRange)
  exact ⟨by simp [a1,a2,b1,b2,Build.addWire,h.size],((h.addWire _ _).addWire _ _).addWire _ _⟩

theorem loadOne_related (input q : Nat) (old : List Circuit.Expr) (slot : Nat) (l : WindowFIFO.Load) :
    BuilderRelated Eq (Circuit.loadOne input q old slot l) (Circuit.loadOne input q old slot l) := by
  cases l with
  | memory | saved => exact pure rfl
  | take => exact take_related _ _ _

theorem expandedLoads_equal (input q : Nat) (old : List Circuit.Expr) (ls : List WindowFIFO.Load) (vs : List Nat) :
    BuilderRelated Eq (Circuit.expandedLoads input q old ls vs) (Circuit.expandedLoads input q old ls vs) := by
  induction ls generalizing vs with
  | nil => exact pure rfl
  | cons l ls ih =>
    cases vs with
    | nil => exact pure rfl
    | cons v vs => exact equalBind (loadOne_related _ _ _ _ _) (fun a => equalBind (ih vs) (fun b => pure rfl))

theorem loads_equal (i : Circuit.Expr) (input q : Nat) (old : List Circuit.Expr) (ls : List Circuit.Load) (vs : List Nat) :
    BuilderRelated Eq (Circuit.loads i input q old ls vs) (Circuit.loads i input q old ls vs) := by
  induction ls generalizing vs with
  | nil => exact pure rfl
  | cons l ls ih =>
    cases vs with
    | nil => exact pure rfl
    | cons v vs =>
      have first : BuilderRelated Eq (compactLoadOne i input q old v l) (compactLoadOne i input q old v l) := by
        cases l with
        | memory | saved => exact pure rfl
        | take => exact take_related _ _ _
      exact equalBind first (fun a => equalBind (ih vs) (fun b => pure rfl))

theorem loads_related (i : Circuit.Expr) (input q : Nat) (old : List Circuit.Expr) (ls : List Circuit.Load) (vs : List Nat) :
    BuilderRelated Schedule.Simulates (Circuit.loads i input q old ls vs) (loads i input q old ls vs) :=
  small_related _ (loads_equal i input q old ls vs)

theorem blocks_related (input qi qo : Nat) (old : List Circuit.Expr) (bs : List HybridIR.Block) :
    BuilderRelated Schedule.Simulates (Circuit.blocks input qi qo old bs) (blocks input qi qo old bs) := by
  induction bs generalizing old with
  | nil => exact pure .skip
  | cons block bs ih =>
    apply equalBind (BuilderRelated.newSlots _)
    intro vs
    apply BuilderRelated.bind (small_related _ (expandedLoads_equal _ _ _ _ _))
    intro a x ha
    apply BuilderRelated.bind (command_related _ _ _ _)
    intro b y hb
    apply BuilderRelated.bind (ih (vs.map Circuit.Expr.wire))
    intro c z hc
    exact pure (ha.seq (hb.seq hc))

structure CountedRelated (a : Circuit.CountedLayout) (b : CountedLayout) : Prop where
  counter : a.counter = b.counter
  held : a.held = b.held
  scratch : a.scratch = b.scratch
  firstLoads : a.firstLoads.Simulates b.firstLoads
  firstBody : a.firstBody.Simulates b.firstBody
  firstRefill : a.firstRefill.Simulates b.firstRefill
  laterLoads : a.laterLoads.Simulates b.laterLoads
  laterBody : a.laterBody.Simulates b.laterBody

theorem prepareCounted_related (start stride : Int) (count : Nat) (initial refill : List Circuit.Load)
    (body : HybridIR.Cmd) (input qi qo : Nat) :
    BuilderRelated CountedRelated
      (Circuit.prepareCounted start stride count initial refill body input qi qo)
      (prepareCounted start stride count initial refill body input qi qo) := by
  apply equalBind (BuilderRelated.fresh _ _)
  intro k
  apply equalBind (BuilderRelated.newSlots _)
  intro held
  apply equalBind (BuilderRelated.newSlots _)
  intro scratch
  apply BuilderRelated.bind (loads_related _ _ _ _ _ _)
  intro a x ha
  apply BuilderRelated.bind (command_related _ _ _ _)
  intro b y hb
  apply BuilderRelated.bind (loads_related _ _ _ _ _ _)
  intro c z hc
  apply BuilderRelated.bind (loads_related _ _ _ _ _ _)
  intro d u hd
  apply BuilderRelated.bind (command_related _ _ _ _)
  intro e v he
  exact pure ⟨rfl,rfl,rfl,ha,hb,hc,hd,he⟩

theorem CountedRelated.round (h : CountedRelated a b) (n : Nat) :
    (a.round n).Simulates (b.round n) := by
  apply Schedule.Simulates.branch
  · intro s w; simp [h.counter]
  · apply Schedule.Simulates.seq
    · exact Schedule.Simulates.branch (by intros; simp [h.counter]) h.laterLoads h.firstRefill
    · have copy : (Circuit.copies (a.held.take n) a.scratch).Simulates (copies (b.held.take n) b.scratch) := by
        simpa only [h.held,h.scratch] using small_simulates (Circuit.copies (a.held.take n) a.scratch)
      exact copy.seq h.laterBody
  · exact h.firstLoads.seq h.firstBody

theorem counted_related (start stride : Int) (count : Nat) (initial refill : List Circuit.Load)
    (body : HybridIR.Cmd) (input qi qo : Nat) :
    BuilderRelated Schedule.Simulates (Circuit.counted start stride count initial refill body input qi qo)
      (counted start stride count initial refill body input qi qo) := by
  unfold Circuit.counted counted
  by_cases zero : count = 0
  · simp only [zero,↓reduceIte]; exact pure .skip
  · simp only [zero,↓reduceIte,pure_bind]
    apply BuilderRelated.bind (prepareCounted_related _ _ _ _ _ _ _ _ _)
    intro a b h
    exact pure (by simpa only [h.counter] using counterLoop_simulates (h.round refill.length) a.counter (.lit count))

theorem namedCounted_related (start stride : Int) (count : Nat) (initial refill : List Circuit.Load)
    (body : HybridIR.Cmd) (input qi qo : Nat) :
    BuilderRelated Schedule.Simulates (ChannelCounted.lower start stride count initial refill body input qi qo)
      (namedCounted start stride count initial refill body input qi qo) := by
  intro a b h
  let c := ChannelCounted.command input qi qo start stride count initial refill body
  have bank : ChannelLower.bankFor c a = ChannelLower.bankFor c b := by simp [ChannelLower.bankFor,h.size]
  have reserved : BuildRelated (ChannelLower.reserve c a) (ChannelLower.reserve c b) :=
    ⟨by simp [ChannelLower.reserve,h.size],h.resources⟩
  have pair := channel_related c (ChannelLower.bankFor c b) (.lit 0) [] _ _ reserved
  change (ChannelLower.lower (ChannelLower.bankFor c a) (.lit 0) [] c (ChannelLower.reserve c a)).1.Simulates
      (channel (ChannelLower.bankFor c b) (.lit 0) [] c (ChannelLower.reserve c b)).1 ∧
    BuildRelated (ChannelLower.lower (ChannelLower.bankFor c a) (.lit 0) [] c (ChannelLower.reserve c a)).2
      (channel (ChannelLower.bankFor c b) (.lit 0) [] c (ChannelLower.reserve c b)).2
  rw [bank]
  exact pair

end IRComparison.Circuit.Shared
