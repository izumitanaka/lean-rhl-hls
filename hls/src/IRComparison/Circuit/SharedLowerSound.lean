import IRComparison.Circuit.SharedLower

namespace IRComparison.Circuit.Shared

@[simp] theorem expressionEvaluation_shared (e : Program) (s : State) (w : Nat → Int) :
    ExpressionEvaluation.eval e s w = e.eval s w := rfl

theorem counterLoop_simulates {body : Schedule} {shared : Schedule Program}
    (h : body.Simulates shared) (k : Nat) (limit : Circuit.Expr) :
    (Circuit.counterLoop k limit body).Simulates (counterLoop k limit shared) := by
  apply Schedule.Simulates.seq
  · apply Schedule.Simulates.step
    intro cap p
    simp [Action.eval,Action.node,execute,ofExpr_eval]
  · apply Schedule.Simulates.loop
    · intro s w; simp
    · apply Schedule.Simulates.seq h
      apply Schedule.Simulates.step
      intro cap p
      simp [Action.eval,Action.node,execute,ofExpr_eval]

/-- Allocation bounds may differ; the allocation order and every execution do
not. In particular this proof does not require rebuilding old expression trees
in the executable shared lowerer. -/
theorem command_simulates (c : HybridIR.Cmd) (i : Circuit.Expr) (ls : List Circuit.Expr)
    (output : Nat) (old fresh : Build) (size : old.wires.size = fresh.wires.size) :
    (Circuit.command i ls output c old).2.wires.size = (command i ls output c fresh).2.wires.size ∧
    (Circuit.command i ls output c old).1.Simulates (command i ls output c fresh).1 := by
  induction c generalizing i ls old fresh with
  | skip => exact ⟨size,Schedule.Simulates.skip⟩
  | assign r e | store a j e | send e =>
    refine ⟨size,Schedule.Simulates.step ?_⟩
    intro cap p
    simp [command,Circuit.command,Action.eval,Action.node,execute,compile_correct]
  | seq a b ia ib | branch e a b ia ib =>
    dsimp only [command,Circuit.command,bind,pure,StateT.bind,StateT.pure]
    have first := ia i ls old fresh size
    have second := ib i ls _ _ first.1
    refine ⟨second.1,?_⟩
    first
    | exact Schedule.Simulates.seq first.2 second.2
    | exact Schedule.Simulates.branch (by intro s w; simp [compile_correct]) first.2 second.2
  | letValue e body ih =>
    dsimp only [command,Circuit.command,bind,pure,StateT.bind,StateT.pure,freshFor,Circuit.freshFor,Circuit.fresh]
    have body := ih i (.wire old.wires.size :: ls)
      (old.addWire (old.exprRange (read i (.wire 0) (.wire 1) ls [] e)))
      (fresh.addWire ((compile i (.wire 0) (.wire 1) ls [] e).range (fun n => fresh.wires[n]?.getD wordRange)))
      (by simpa [Build.addWire] using size)
    rw [← size]
    exact ⟨body.1,Schedule.Simulates.seq
      (Schedule.Simulates.step (by intro cap p; simp [Action.eval,Action.node,execute,compile_correct])) body.2⟩
  | «repeat» n body ih =>
    dsimp only [command,Circuit.command,bind,pure,StateT.bind,StateT.pure,Circuit.fresh]
    have body := ih i ls (old.addWire ⟨0,n⟩) (fresh.addWire ⟨0,n⟩) (by simpa [Build.addWire] using size)
    rw [← size]
    exact ⟨body.1,counterLoop_simulates body.2 _ _⟩
  | forRange e body ih =>
    dsimp only [command,Circuit.command,bind,pure,StateT.bind,StateT.pure,freshFor,Circuit.freshFor,Circuit.fresh,bounds,Circuit.bounds]
    simp only [Build.addWire,Array.size_push]
    rw [← size]
    let oe := Expr.natIndex (read i (.wire 0) (.wire 1) ls [] e)
    let se := naturalIndex (compile i (.wire 0) (.wire 1) ls [] e)
    let ob := old.addWire (old.exprRange oe)
    let sb := fresh.addWire (se.range (fun n => fresh.wires[n]?.getD wordRange))
    have body := ih i (.wire (old.wires.size+1) :: ls)
      (ob.addWire (ob.exprRange oe)) (sb.addWire (se.range (fun n => sb.wires[n]?.getD wordRange)))
      (by simp [ob,sb,Build.addWire,size])
    exact ⟨body.1,Schedule.Simulates.seq
      (Schedule.Simulates.step (by intro cap p; simp only [Action.eval,Action.node,execute,expressionEvaluation_original,expressionEvaluation_shared,naturalIndex_eval,compile_correct,Expr.eval]; cases (read i (.wire 0) (.wire 1) ls [] e).eval (p.at 0).data (p.at 0).wires <;> rfl))
      (counterLoop_simulates body.2 _ _)⟩

theorem channel_simulates (c : HybridIR.ChannelCmd) (bank : ChannelLower.Buffers) (i : Circuit.Expr) (ls : List Circuit.Expr)
    (old fresh : Build) (size : old.wires.size = fresh.wires.size) :
    (ChannelLower.lower bank i ls c old).2.wires.size = (channel bank i ls c fresh).2.wires.size ∧
    (ChannelLower.lower bank i ls c old).1.Simulates (channel bank i ls c fresh).1 := by
  induction c generalizing i ls old fresh with
  | skip => exact ⟨size,Schedule.Simulates.skip⟩
  | assign r e | store a j e | send q e =>
    refine ⟨size,Schedule.Simulates.step ?_⟩
    intro cap p
    simp [channel,ChannelLower.lower,Action.eval,Action.node,execute,compile_correct]
  | hold slot e =>
    refine ⟨size,Schedule.Simulates.seq (Schedule.Simulates.step ?_) (Schedule.Simulates.step ?_)⟩
    all_goals intro cap p; simp [Action.eval,Action.node,execute,compile_correct]
  | receive q slot =>
    refine ⟨size,Schedule.Simulates.seq (Schedule.Simulates.step ?_) (Schedule.Simulates.step ?_)⟩
    all_goals intro cap p; simp [Action.eval,Action.node,execute]
  | letBuffer slot body ih =>
    dsimp only [channel,ChannelLower.lower,bind,pure,StateT.bind,StateT.pure,Circuit.fresh]
    have body := ih i (.wire old.wires.size :: ls) (old.addWire wordRange) (fresh.addWire wordRange)
      (by simpa [Build.addWire] using size)
    rw [← size]
    exact ⟨body.1,Schedule.Simulates.seq
      (Schedule.Simulates.step (by intro cap p; simp [Action.eval,Action.node,execute])) body.2⟩
  | seq a b ia ib | branch e a b ia ib =>
    dsimp only [channel,ChannelLower.lower,bind,pure,StateT.bind,StateT.pure]
    have first := ia i ls old fresh size
    have second := ib i ls _ _ first.1
    refine ⟨second.1,?_⟩
    first
    | exact Schedule.Simulates.seq first.2 second.2
    | exact Schedule.Simulates.branch (by intro s w; simp [compile_correct]) first.2 second.2
  | letValue e body ih =>
    dsimp only [channel,ChannelLower.lower,bind,pure,StateT.bind,StateT.pure,freshFor,Circuit.freshFor,Circuit.fresh]
    have body := ih i (.wire old.wires.size :: ls)
      (old.addWire (old.exprRange (read i (.wire 0) (.wire 1) ls [] e)))
      (fresh.addWire ((compile i (.wire 0) (.wire 1) ls [] e).range (fun n => fresh.wires[n]?.getD wordRange)))
      (by simpa [Build.addWire] using size)
    rw [← size]
    exact ⟨body.1,Schedule.Simulates.seq
      (Schedule.Simulates.step (by intro cap p; simp [Action.eval,Action.node,execute,compile_correct])) body.2⟩
  | «repeat» n body ih =>
    dsimp only [channel,ChannelLower.lower,bind,pure,StateT.bind,StateT.pure,Circuit.fresh]
    have body := ih i ls (old.addWire ⟨0,n⟩) (fresh.addWire ⟨0,n⟩) (by simpa [Build.addWire] using size)
    rw [← size]
    exact ⟨body.1,counterLoop_simulates body.2 _ _⟩
  | forRange e body ih =>
    dsimp only [channel,ChannelLower.lower,bind,pure,StateT.bind,StateT.pure,freshFor,Circuit.freshFor,Circuit.fresh,bounds,Circuit.bounds]
    simp only [Build.addWire,Array.size_push]
    rw [← size]
    let oe := Expr.natIndex (read i (.wire 0) (.wire 1) ls [] e)
    let se := naturalIndex (compile i (.wire 0) (.wire 1) ls [] e)
    let ob := old.addWire (old.exprRange oe)
    let sb := fresh.addWire (se.range (fun n => fresh.wires[n]?.getD wordRange))
    have body := ih i (.wire (old.wires.size+1) :: ls)
      (ob.addWire (ob.exprRange oe)) (sb.addWire (se.range (fun n => sb.wires[n]?.getD wordRange)))
      (by simp [ob,sb,Build.addWire,size])
    exact ⟨body.1,Schedule.Simulates.seq
      (Schedule.Simulates.step (by intro cap p; simp only [Action.eval,Action.node,execute,expressionEvaluation_original,expressionEvaluation_shared,naturalIndex_eval,compile_correct,Expr.eval]; cases (read i (.wire 0) (.wire 1) ls [] e).eval (p.at 0).data (p.at 0).wires <;> rfl))
      (counterLoop_simulates body.2 _ _)⟩

end IRComparison.Circuit.Shared
