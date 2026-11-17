import IRComparison.Circuit.ChannelLower

namespace IRComparison.Circuit.ChannelLower

def Protected (bank : Buffers) (bound slot : Nat) : Prop :=
  slot < bound ∧ (slot < bank.base ∨ bank.stop ≤ slot)

inductive Captured (bank : Buffers) (bound : Nat) : Expr → Prop where
  | fail : Captured bank bound .fail
  | lit : Captured bank bound (.lit n)
  | wire : Protected bank bound slot → Captured bank bound (.wire slot)
  | bin : Captured bank bound a → Captured bank bound b → Captured bank bound (.bin op a b)
  | natIndex : Captured bank bound a → Captured bank bound (.natIndex a)
  | wrap32 : Captured bank bound a → Captured bank bound (.wrap32 a)
  | select : Captured bank bound c → Captured bank bound a → Captured bank bound b → Captured bank bound (.select c a b)
  | seq : Captured bank bound a → Captured bank bound b → Captured bank bound (.seq a b)

theorem Captured.mono (h : Captured bank n e) (hn : n ≤ m) : Captured bank m e := by
  induction h with
  | fail => exact .fail
  | lit => exact .lit
  | wire h => exact .wire ⟨by have := h.1; omega,h.2⟩
  | bin _ _ ia ib => exact .bin ia ib
  | natIndex _ ih => exact .natIndex ih
  | wrap32 _ ih => exact .wrap32 ih
  | select _ _ _ ic ia ib => exact .select ic ia ib
  | seq _ _ ia ib => exact .seq ia ib

theorem Captured.stable {p q : Payload} (h : Captured bank bound e)
    (hw : ∀ k, Protected bank bound k → p.wires k = q.wires k) :
    e.eval p.data p.wires = e.eval q.data q.wires := by
  induction h with
  | fail | lit => rfl
  | wire h => exact congrArg some (hw _ h)
  | bin _ _ ia ib => simp only [Expr.eval,ia,ib]
  | natIndex _ ih | wrap32 _ ih => simp only [Expr.eval,ih]
  | select _ _ _ ic ia ib => simp only [Expr.eval,ic,ia,ib]
  | seq _ _ ia ib => simp only [Expr.eval,ia,ib]

def actionFrame (bank : Buffers) (bound : Nat) : Action → Prop
  | .wire slot _ | .receive _ slot => ∀ k, Protected bank bound k → k ≠ slot
  | _ => True

def frame (bank : Buffers) (bound : Nat) : Schedule → Prop
  | .skip => True
  | .step a => actionFrame bank bound a
  | .seq a b | .branch _ a b => frame bank bound a ∧ frame bank bound b
  | .loop _ a => frame bank bound a

theorem action_frame (h : actionFrame bank bound a) (hr : a.eval cap p = some q) :
    ∀ k, Protected bank bound k → p.wires k = q.wires k := by
  cases a <;> simp only [Action.eval,Action.node,execute,Payload.at] at hr
  case wire slot e =>
    cases he : e.eval p.data p.wires <;> simp [he,Runtime.payload,Runtime.setWire] at hr
    subst q; intro k hk; simp [h k hk]
  case receive queue slot =>
    cases hq : p.queues queue <;> simp [hq,Runtime.payload,Runtime.setQueue,Runtime.setWire] at hr
    subst q; intro k hk; simp [h k hk]
  case assign slot e =>
    cases he : e.eval p.data p.wires <;> simp [he,Runtime.payload] at hr
    subst q; intros; rfl
  case store a j e =>
    cases hj : j.eval p.data p.wires <;> simp [hj] at hr
    next k =>
      cases he : e.eval p.data p.wires <;> simp [he] at hr
      next v =>
        cases hw : p.data.write a k v <;> simp [hw,Runtime.payload] at hr
        subst q; intros; rfl
  case send queue e =>
    cases he : e.eval p.data p.wires <;> simp [he] at hr
    next v =>
      have hr := hr.2
      simp [Runtime.payload,Runtime.setQueue] at hr
      subst q; intros; rfl
  case snapshot a b | erase a | clear a =>
    simp [Runtime.payload,Runtime.setArray,Runtime.setQueue] at hr
    subst q; intros; rfl

theorem schedule_frame (he : c.Eval cap p result) (hf : frame bank bound c) (hr : result = some q) :
    ∀ k, Protected bank bound k → p.wires k = q.wires k := by
  induction he generalizing q with
  | skip => cases hr; intros; rfl
  | step => exact action_frame hf hr
  | seq_error | branch_error | loop_error | loop_body_error => contradiction
  | seq _ _ ia ib => intro k hk; exact (ia hf.1 rfl k hk).trans (ib hf.2 hr k hk)
  | branch_yes _ _ _ ih => exact ih hf.1 hr
  | branch_no _ _ ih => exact ih hf.2 hr
  | loop_stop => cases hr; intros; rfl
  | loop_next _ _ _ _ ib il => intro k hk; exact (ib hf rfl k hk).trans (il hf hr k hk)

theorem frame_mono (h : frame bank n c) (hn : m ≤ n) : frame bank m c := by
  induction c with
  | skip => trivial
  | step a => cases a <;> try trivial
              all_goals intro k hk; exact h k ⟨by have := hk.1; omega,hk.2⟩
  | seq a b ia ib | branch e a b ia ib => exact ⟨ia h.1,ib h.2⟩
  | loop e a ih => exact ih h

theorem wire_frame (h : bound ≤ slot) : actionFrame bank bound (.wire slot e) :=
  fun _ hk => by have := hk.1; omega

theorem buffer_frame (h : slot < bank.count) :
    (∀ k, Protected bank bound k → k ≠ bank.value slot) ∧
    (∀ k, Protected bank bound k → k ≠ bank.valid slot) := by
  constructor <;> intro k hk <;> rcases hk.2 with hk | hk <;>
    dsimp [Buffers.value,Buffers.valid,Buffers.stop] at * <;> omega

/-- Generated operations modify only their buffer bank and fresh captures. -/
theorem lower_frame (c : HybridIR.ChannelCmd) (bank : Buffers) (b : Build) (i : Expr) (ls : List Expr)
    (fits : bufferCount c ≤ bank.count) :
    b.wires.size ≤ (lower bank i ls c b).2.wires.size ∧ frame bank b.wires.size (lower bank i ls c b).1 := by
  induction c generalizing b i ls with
  | skip | assign | store | send => exact ⟨Nat.le_refl _,trivial⟩
  | hold slot e | receive q slot =>
    have hs : slot < bank.count := by change slot+1 ≤ _ at fits; omega
    exact ⟨Nat.le_refl _,buffer_frame hs⟩
  | letValue e c ih =>
    let b1 := b.addWire (b.exprRange (read i (.wire 0) (.wire 1) ls [] e))
    have h := ih b1 i (.wire b.wires.size::ls) fits
    have hb : b1.wires.size = b.wires.size+1 := by simp [b1,Build.addWire]
    change b.wires.size ≤ (lower bank i (.wire b.wires.size::ls) c b1).2.wires.size ∧ _
    exact ⟨by have := h.1; omega,⟨wire_frame (Nat.le_refl _),frame_mono h.2 (by omega)⟩⟩
  | letBuffer slot c ih =>
    let b1 := b.addWire wordRange
    have fit : bufferCount c ≤ bank.count := Nat.le_trans (Nat.le_max_right _ _) fits
    have h := ih b1 i (.wire b.wires.size::ls) fit
    have hb : b1.wires.size = b.wires.size+1 := by simp [b1,Build.addWire]
    change b.wires.size ≤ (lower bank i (.wire b.wires.size::ls) c b1).2.wires.size ∧ _
    exact ⟨by have := h.1; omega,⟨wire_frame (Nat.le_refl _),frame_mono h.2 (by omega)⟩⟩
  | seq a c ia ib | branch e a c ia ib =>
    have fa : bufferCount a ≤ bank.count := Nat.le_trans (Nat.le_max_left _ _) fits
    have fc : bufferCount c ≤ bank.count := Nat.le_trans (Nat.le_max_right _ _) fits
    have ha := ia b i ls fa
    have hb := ib (lower bank i ls a b).2 i ls fc
    exact ⟨Nat.le_trans ha.1 hb.1,⟨ha.2,frame_mono hb.2 ha.1⟩⟩
  | «repeat» n c ih =>
    let b1 := b.addWire ⟨0,n⟩
    have h := ih b1 i ls fits
    have hb : b1.wires.size = b.wires.size+1 := by simp [b1,Build.addWire]
    refine ⟨by have := h.1; change _ ≤ (lower bank i ls c b1).2.wires.size; omega,?_⟩
    exact ⟨wire_frame (Nat.le_refl _),⟨frame_mono h.2 (by omega),wire_frame (Nat.le_refl _)⟩⟩
  | forRange e c ih =>
    let expr := Expr.natIndex (read i (.wire 0) (.wire 1) ls [] e)
    let b1 := b.addWire (b.exprRange expr)
    let b2 := b1.addWire (b1.exprRange expr)
    have h := ih b2 i (.wire b1.wires.size::ls) fits
    have hb1 : b1.wires.size = b.wires.size+1 := by simp [b1,Build.addWire]
    have hb2 : b2.wires.size = b1.wires.size+1 := by simp [b2,Build.addWire]
    refine ⟨by have := h.1; change _ ≤ (lower bank i (.wire b1.wires.size::ls) c b2).2.wires.size; omega,?_⟩
    change frame bank b.wires.size (.seq (.step (.wire b.wires.size expr))
      (counterLoop b1.wires.size (.wire b.wires.size) (lower bank i (.wire b1.wires.size::ls) c b2).1))
    exact ⟨wire_frame (Nat.le_refl _),⟨wire_frame (by omega),⟨frame_mono h.2 (by omega),wire_frame (by omega)⟩⟩⟩

structure Context (bank : Buffers) (bound : Nat) (i : Expr) (ls : List Expr) (p : Payload)
    (iv xv yv : Int) (lvs : List Int) : Prop where
  inputs : 2 ≤ bank.base
  floor : bank.stop ≤ bound
  indexScope : Captured bank bound i
  localsScope : ∀ e ∈ ls, Captured bank bound e
  index : i.eval p.data p.wires = some iv
  left : p.wires 0 = xv
  right : p.wires 1 = yv
  locals : Matches p.data p.wires ls lvs

theorem Context.weaken (h : Context bank n i ls p iv xv yv lvs) (hn : n ≤ m) :
    Context bank m i ls p iv xv yv lvs :=
  ⟨h.inputs,Nat.le_trans h.floor hn,h.indexScope.mono hn,fun e he => (h.localsScope e he).mono hn,h.index,h.left,h.right,h.locals⟩

theorem lookup_captured (h : ∀ e ∈ ls, Captured bank bound e) : Captured bank bound (lookup ls k) := by
  unfold lookup
  cases he : ls[k]? with
  | none => exact .fail
  | some e => exact h e (List.mem_of_getElem? he)

theorem Context.preserve (h : Context bank bound i ls p iv xv yv lvs)
    (hw : ∀ k, Protected bank bound k → p.wires k = q.wires k) : Context bank bound i ls q iv xv yv lvs := by
  have base : bank.base ≤ bound := Nat.le_trans (by dsimp [Buffers.stop]; omega) h.floor
  refine ⟨h.inputs,h.floor,h.indexScope,h.localsScope,(h.indexScope.stable hw).symm.trans h.index,?_,?_,?_⟩
  · exact (hw 0 ⟨by have := h.inputs; omega,Or.inl (by have := h.inputs; omega)⟩).symm.trans h.left
  · exact (hw 1 ⟨by have := h.inputs; omega,Or.inl (by have := h.inputs; omega)⟩).symm.trans h.right
  · intro k
    exact ((lookup_captured h.localsScope).stable hw).symm.trans (h.locals k)

theorem Context.setFresh (h : Context bank bound i ls p iv xv yv lvs) (hs : bound ≤ slot) :
    Context bank bound i ls (p.setWire slot v) iv xv yv lvs := by
  apply h.preserve
  intro k hk
  simp [Payload.setWire,show k ≠ slot from by have := hk.1; omega]

theorem Context.bind (h : Context bank n i ls p iv xv yv lvs) :
    Context bank (n+1) i (.wire n::ls) (p.setWire n v) iv xv yv (v::lvs) := by
  have old := (h.setFresh (v:=v) (Nat.le_refl _)).weaken (Nat.le_succ _)
  refine ⟨old.inputs,old.floor,old.indexScope,?_,old.index,old.left,old.right,?_⟩
  · intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact .wire ⟨Nat.lt_succ_self _,Or.inr h.floor⟩
    · exact old.localsScope e he
  · exact matches_cons old.locals (by simp [Expr.eval,Payload.setWire])

theorem Context.read (h : Context bank n i ls p iv xv yv lvs) (e : HybridIR.ReadCode) :
    (read i (.wire 0) (.wire 1) ls [] e).eval p.data p.wires = e.eval iv xv yv p.data lvs [] :=
  read_correct e h.index (congrArg some h.left) (congrArg some h.right) h.locals matches_nil

end IRComparison.Circuit.ChannelLower
