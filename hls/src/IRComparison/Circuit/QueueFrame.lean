import IRComparison.Circuit.CommandFrame

namespace IRComparison.Circuit

def Action.noQueue (qi : Nat) : Action → Prop
  | .clear q | .send q _ | .receive q _ => q ≠ qi
  | _ => True

def Schedule.noQueue (qi : Nat) : Schedule → Prop
  | .skip => True
  | .step a => a.noQueue qi
  | .seq a b | .branch _ a b => a.noQueue qi ∧ b.noQueue qi
  | .loop _ b => b.noQueue qi

theorem Action.preserves_queue {a : Action} (ha : a.noQueue qi) (he : a.eval cap p = some q) :
    q.queues qi = p.queues qi := by
  cases a <;> simp only [Action.eval,Action.node,execute,Payload.at] at he
  case wire slot e | assign slot e =>
    cases hv : e.eval p.data p.wires <;> simp [hv,Runtime.payload,Runtime.setWire] at he
    subst q; rfl
  case store a j e =>
    cases hj : j.eval p.data p.wires <;> simp [hj] at he
    next k =>
      cases hv : e.eval p.data p.wires <;> simp [hv] at he
      next v =>
        cases hs : p.data.write a k v <;> simp [hs,Runtime.payload] at he
        subst q; rfl
  case snapshot a b | erase a =>
    simp [Runtime.payload,Runtime.setArray] at he
    subst q; rfl
  case clear id =>
    simp [Runtime.payload,Runtime.setQueue] at he
    subst q
    simp [Ne.symm ha]
  case send id e =>
    cases hv : e.eval p.data p.wires <;> simp [hv] at he
    next v =>
      have he := he.2
      simp [Runtime.payload,Runtime.setQueue] at he
      subst q
      simp [Ne.symm ha]
  case receive id slot =>
    cases hv : p.queues id with
    | nil => simp [hv] at he
    | cons x xs =>
      simp [hv,Runtime.payload,Runtime.setQueue,Runtime.setWire] at he
      subst q
      simp [Ne.symm ha]

theorem Schedule.preserves_queue {c : Schedule} (he : c.Eval cap p result) (ha : c.noQueue qi)
    (hr : result = some q) : q.queues qi = p.queues qi := by
  induction he generalizing q with
  | skip => cases hr; rfl
  | step => exact Action.preserves_queue ha hr
  | seq_error | branch_error | loop_error | loop_body_error => contradiction
  | seq _ _ ia ib => exact (ib ha.2 hr).trans (ia ha.1 rfl)
  | branch_yes _ _ _ ih => exact ih ha.1 hr
  | branch_no _ _ ih => exact ih ha.2 hr
  | loop_stop => cases hr; rfl
  | loop_next _ _ _ _ ib il => exact (il ha hr).trans (ib ha rfl)

theorem command_noQueue (c : HybridIR.Cmd) (b : Build) (i : Expr) (locals : List Expr)
    (h : output ≠ qi) : ((command i locals output c).run b).1.noQueue qi := by
  induction c generalizing b i locals with
  | skip | assign | store => trivial
  | send => exact h
  | letValue e c ih =>
    let b1 := b.addWire (b.exprRange (read i (.wire 0) (.wire 1) locals [] e))
    exact ⟨True.intro,ih b1 i (.wire b.wires.size::locals)⟩
  | seq a c ia ib | branch e a c ia ib =>
    dsimp only [command,bind,pure,StateT.bind,StateT.pure,StateT.run]
    have ha := ia b i locals
    dsimp only [StateT.run] at ha
    generalize he : command i locals output a b = pair at *
    obtain ⟨first,b1⟩ := pair
    exact ⟨ha,ib b1 i locals⟩
  | «repeat» n c ih =>
    exact ⟨True.intro,⟨ih (b.addWire ⟨0,n⟩) i locals,True.intro⟩⟩
  | forRange e c ih =>
    let expr := Expr.natIndex (read i (.wire 0) (.wire 1) locals [] e)
    let b1 := b.addWire (b.exprRange expr)
    let b2 := b1.addWire (b1.exprRange expr)
    exact ⟨True.intro,⟨True.intro,⟨ih b2 i (.wire b1.wires.size::locals),True.intro⟩⟩⟩

theorem take_noQueue (b : Build) (qi slot : Nat) (e : Expr) (h : qi ≠ protectedQueue) :
    ((take qi slot e).run b).1.noQueue protectedQueue := by
  exact ⟨True.intro,⟨⟨True.intro,⟨h,True.intro⟩⟩,h⟩⟩

theorem expandedLoads_noQueue (input qi : Nat) (old : List Expr) (loads : List WindowFIFO.Load)
    (slots : List Nat) (b : Build) (h : qi ≠ protectedQueue) :
    ((expandedLoads input qi old loads slots).run b).1.noQueue protectedQueue := by
  induction loads generalizing slots b with
  | nil => trivial
  | cons l ls ih =>
    cases slots with
    | nil => trivial
    | cons slot slots =>
      cases l with
      | memory | saved => exact ⟨True.intro,ih slots b⟩
      | take n =>
        dsimp only [expandedLoads,loadOne,bind,pure,StateT.bind,StateT.pure,StateT.run]
        have hh := take_noQueue b qi slot (.lit n) h
        dsimp only [StateT.run] at hh
        generalize he : take qi slot (.lit n) b = pair at *
        obtain ⟨first,b1⟩ := pair
        exact ⟨hh,ih slots b1⟩

end IRComparison.Circuit
