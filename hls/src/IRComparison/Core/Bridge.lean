import IRComparison.Core.Imperative
import IRComparison.Core.Functional

namespace IRComparison

/-- A comparison/frontend bridge, not used inside either optimizer. -/
def lowerBody : Imperative.Cmd → Functional.Term
  | .skip => .yield 0
  | .letValue e b => .letValue 0 e (lowerBody b)
  | .assign r e => .letSet 0 r e (.yield 0)
  | .store a j e => .letWrite 0 a j e (.yield 0)
  | .seq a b => .letResult 0 (lowerBody a) (lowerBody b)
  | .branch e a b => .branch 0 e (lowerBody a) (lowerBody b)
  | .repeat n b => .iterate 0 n (lowerBody b) (.yield 0)
  | .forRange e b => .forRange 0 e (lowerBody b) (.yield 0)

theorem lowerBody_correct (b : Imperative.Cmd) (i x y : Int)
    (s : State) (rest : List State) (locals : List Int := []) :
    (lowerBody b).eval i x y (s :: rest) locals = b.eval i x y s locals := by
  induction b generalizing s rest locals with
  | skip => rfl
  | letValue e b hb => simp [lowerBody, Functional.Term.eval, Imperative.Cmd.eval, hb]
  | assign r e => simp [lowerBody, Functional.Term.eval, Imperative.Cmd.eval]
  | store a j e => simp [lowerBody, Functional.Term.eval, Imperative.Cmd.eval]
  | seq a b ha hb => simp [lowerBody, Functional.Term.eval, Imperative.Cmd.eval, ha, hb]
  | branch e a b ha hb => simp [lowerBody, Functional.Term.eval, Imperative.Cmd.eval, ha, hb]
  | «repeat» n b hb => simp [lowerBody, Functional.Term.eval, Imperative.Cmd.eval, hb]
  | forRange e b hb => simp [lowerBody, Functional.Term.eval, Imperative.Cmd.eval, hb]

def lowerProgram : Imperative.Program → Functional.Program
  | .loop i d n l r b => .loop i d n l r (lowerBody b)
  | .buffered i d n l b => .carried i d n l (lowerBody b)
  | .effect b => .value (lowerBody b)
  | .seq a b => .letResult (lowerProgram a) (lowerProgram b)
  | .branch r a b => .branch r (lowerProgram a) (lowerProgram b)

theorem lowerProgram_correct (p : Imperative.Program) (input : Input) (s : State) :
    (lowerProgram p).eval input s = p.eval input s := by
  induction p generalizing s with
  | loop i d n l r b =>
      simp [lowerProgram, Functional.Program.eval, Imperative.Program.eval, lowerBody_correct]
  | buffered i d n l b =>
      simp [lowerProgram, Functional.Program.eval, Imperative.Program.eval,
        Functional.runCarried_correct, Imperative.runBuffered_correct, lowerBody_correct]
  | effect b => exact lowerBody_correct b 0 0 0 s []
  | seq a b ha hb => simp [lowerProgram, Functional.Program.eval, Imperative.Program.eval, ha, hb]
  | branch r a b ha hb => simp [lowerProgram, Functional.Program.eval, Imperative.Program.eval, ha, hb]

/-- Both separately implemented optimizers agree on corresponding programs. -/
theorem optimized_agree (p : Imperative.Program) (input : Input) (s : State) :
    (Functional.transform (lowerProgram p)).eval input s =
      (Imperative.transform p).eval input s := by
  rw [Functional.transform_correct, Imperative.transform_correct, lowerProgram_correct]

end IRComparison
