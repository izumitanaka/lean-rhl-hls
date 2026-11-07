import IRComparison.Circuit.Structured

namespace IRComparison.Circuit

/-- Stable expression made only from captured holding registers and constants.
Stateful reads are deliberately excluded from lexical environments. -/
inductive Static (limit : Nat) : Expr → Prop where
  | fail : Static limit .fail
  | lit : Static limit (.lit n)
  | wire : slot < limit → Static limit (.wire slot)
  | bin : Static limit a → Static limit b → Static limit (.bin op a b)
  | natIndex : Static limit a → Static limit (.natIndex a)
  | select : Static limit c → Static limit a → Static limit b → Static limit (.select c a b)
  | seq : Static limit a → Static limit b → Static limit (.seq a b)

def SameBelow (limit : Nat) (a b : Nat → Int) : Prop := ∀ n, n < limit → a n = b n

theorem SameBelow.refl : SameBelow n w w := fun _ _ => rfl
theorem SameBelow.trans (h : SameBelow n a b) (k : SameBelow n b c) : SameBelow n a c :=
  fun i hi => (h i hi).trans (k i hi)
theorem SameBelow.mono (h : SameBelow n a b) (hk : k ≤ n) : SameBelow k a b :=
  fun i hi => h i (by omega)

theorem Static.mono (h : Static n e) (hk : n ≤ k) : Static k e := by
  induction h with
  | fail => exact .fail
  | lit => exact .lit
  | wire hn => exact .wire (by omega)
  | bin _ _ ha hb => exact .bin ha hb
  | natIndex _ ha => exact .natIndex ha
  | select _ _ _ hc ha hb => exact .select hc ha hb
  | seq _ _ ha hb => exact .seq ha hb

theorem Static.stable (h : Static n e) (hw : SameBelow n w w') :
    e.eval s w = e.eval s' w' := by
  induction h with
  | fail | lit => rfl
  | wire hn => exact congrArg some (hw _ hn)
  | bin _ _ ha hb => simp only [Expr.eval,ha,hb]
  | natIndex _ ha => simp only [Expr.eval,ha]
  | select _ _ _ hc ha hb => simp only [Expr.eval,hc,ha,hb]
  | seq _ _ ha hb => simp only [Expr.eval,ha,hb]

/-- Structural frame condition for generated temporary registers. -/
def Action.above (base : Nat) : Action → Prop
  | .wire slot _ | .receive _ slot => base ≤ slot
  | _ => True

def Schedule.above (base : Nat) : Schedule → Prop
  | .skip => True
  | .step a => a.above base
  | .seq a b | .branch _ a b => a.above base ∧ b.above base
  | .loop _ b => b.above base

theorem Action.preserves_below {a : Action} (ha : a.above base) (he : a.eval cap p = some q) :
    SameBelow base p.wires q.wires := by
  cases a <;> simp only [Action.eval,Action.node,execute,Payload.at] at he
  case wire slot e =>
    cases hv : e.eval p.data p.wires with
    | none => simp [hv] at he
    | some v =>
      simp [hv,Runtime.payload,Runtime.setWire] at he
      subst q
      intro n hn
      simp [show n ≠ slot from by change base ≤ slot at ha; omega]
  case receive queue slot =>
    cases hv : p.queues queue with
    | nil => simp [hv] at he
    | cons x xs =>
      simp [hv,Runtime.payload,Runtime.setQueue,Runtime.setWire] at he
      subst q
      intro n hn
      simp [show n ≠ slot from by change base ≤ slot at ha; omega]
  case assign slot e =>
    cases hv : e.eval p.data p.wires <;> simp [hv,Runtime.payload] at he
    subst q; exact .refl
  case store a j e =>
    cases hj : j.eval p.data p.wires <;> simp [hj] at he
    next k =>
      cases hv : e.eval p.data p.wires <;> simp [hv] at he
      next v =>
        cases hs : p.data.write a k v <;> simp [hs,Runtime.payload] at he
        subst q; exact .refl
  case send queue e =>
    cases hv : e.eval p.data p.wires <;> simp [hv] at he
    next v =>
      have he := he.2
      simp [Runtime.payload,Runtime.setQueue] at he
      subst q; exact .refl
  case snapshot a b | erase a | clear a =>
    simp [Runtime.payload,Runtime.setArray,Runtime.setQueue] at he
    subst q; exact .refl

theorem Schedule.preserves_below {c : Schedule} (he : c.Eval cap p result) (ha : c.above base)
    (hr : result = some q) : SameBelow base p.wires q.wires := by
  induction he generalizing q with
  | skip => cases hr; exact .refl
  | step => exact Action.preserves_below ha hr
  | seq_error | branch_error | loop_error | loop_body_error => contradiction
  | seq _ _ ia ib => exact (ia ha.1 rfl).trans (ib ha.2 hr)
  | branch_yes _ _ _ ih => exact ih ha.1 hr
  | branch_no _ _ ih => exact ih ha.2 hr
  | loop_stop => cases hr; exact .refl
  | loop_next _ _ _ _ ib il => exact (ib ha rfl).trans (il ha hr)

theorem Schedule.above_mono (c : Schedule) (h : c.above n) (hk : k ≤ n) : c.above k := by
  induction c with
  | skip => trivial
  | step a => cases a <;> simp_all [Schedule.above,Action.above] <;> omega
  | seq a b ia ib | branch e a b ia ib => exact ⟨ia h.1,ib h.2⟩
  | loop e b ih => exact ih h

end IRComparison.Circuit
