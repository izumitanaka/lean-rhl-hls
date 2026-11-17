import IRComparison.Circuit.Lower
import IRComparison.Circuit.Scope

namespace IRComparison.Circuit

/-- Allocating temporary registers never overwrites the caller's captures. -/
theorem command_frame (c : HybridIR.Cmd) (i : Expr) (locals : List Expr) (output : Nat) (b : Build) :
    let (s,b') := (command i locals output c).run b
    b.wires.size ≤ b'.wires.size ∧ s.above b.wires.size := by
  induction c generalizing b i locals with
  | skip => simp [command,Schedule.above]
  | assign => simp [command,Schedule.above,Action.above]
  | store => simp [command,Schedule.above,Action.above]
  | send => simp [command,Schedule.above,Action.above]
  | letValue e c ih =>
    let b1 := b.addWire (b.exprRange (read i (.wire 0) (.wire 1) locals [] e))
    change let (body,b2) := command i (.wire b.wires.size::locals) output c b1
           b.wires.size ≤ b2.wires.size ∧ (Schedule.seq (.step (.wire b.wires.size _)) body).above b.wires.size
    have h := ih i (.wire b.wires.size::locals) b1
    dsimp only [StateT.run] at h
    have hb : b1.wires.size = b.wires.size+1 := by simp [b1,Build.addWire]
    generalize he : command i (.wire b.wires.size::locals) output c b1 = pair at *
    obtain ⟨body,b2⟩ := pair
    exact ⟨by omega,⟨Nat.le_refl _,body.above_mono h.2 (by omega)⟩⟩
  | seq a c ia ib | branch e a c ia ib =>
    dsimp only [command,bind,pure,StateT.bind,StateT.pure,StateT.run]
    have ha := ia i locals b
    dsimp only [StateT.run] at ha
    generalize hea : command i locals output a b = pa at *
    obtain ⟨first,b1⟩ := pa
    dsimp only
    have hb := ib i locals b1
    dsimp only [StateT.run] at hb
    generalize heb : command i locals output c b1 = pb at *
    obtain ⟨second,b2⟩ := pb
    exact ⟨Nat.le_trans ha.1 hb.1,⟨ha.2,second.above_mono hb.2 ha.1⟩⟩
  | «repeat» n c ih =>
    let b1 := b.addWire ⟨0,n⟩
    change let (body,b2) := command i locals output c b1
           b.wires.size ≤ b2.wires.size ∧ (counterLoop b.wires.size (.lit n) body).above b.wires.size
    have h := ih i locals b1
    dsimp only [StateT.run] at h
    have hb : b1.wires.size = b.wires.size+1 := by simp [b1,Build.addWire]
    generalize he : command i locals output c b1 = pair at *
    obtain ⟨body,b2⟩ := pair
    exact ⟨by omega,⟨Nat.le_refl _,⟨body.above_mono h.2 (by omega),Nat.le_refl _⟩⟩⟩
  | forRange e c ih =>
    let expr := Expr.natIndex (read i (.wire 0) (.wire 1) locals [] e)
    let b1 := b.addWire (b.exprRange expr)
    let b2 := b1.addWire (b1.exprRange expr)
    change let (body,b3) := command i (.wire b1.wires.size::locals) output c b2
           b.wires.size ≤ b3.wires.size ∧
           (Schedule.seq (.step (.wire b.wires.size expr)) (counterLoop b1.wires.size (.wire b.wires.size) body)).above b.wires.size
    have h := ih i (.wire b1.wires.size::locals) b2
    dsimp only [StateT.run] at h
    have hb1 : b1.wires.size = b.wires.size+1 := by simp [b1,Build.addWire]
    have hb2 : b2.wires.size = b.wires.size+2 := by simp [b2,Build.addWire,hb1,Nat.add_assoc]
    generalize he : command i (.wire b1.wires.size::locals) output c b2 = pair at *
    obtain ⟨body,b3⟩ := pair
    exact ⟨by omega,⟨Nat.le_refl _,⟨(show b.wires.size ≤ b1.wires.size from by omega),
      ⟨body.above_mono h.2 (by omega),(show b.wires.size ≤ b1.wires.size from by omega)⟩⟩⟩⟩

end IRComparison.Circuit
