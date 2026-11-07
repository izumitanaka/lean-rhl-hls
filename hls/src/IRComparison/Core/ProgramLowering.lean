import IRComparison.Core.StateLowering

namespace IRComparison.ProgramLowering

/-- Allocate the functional program's current state using the existing proved
    body pass. Unsupported persistent versions still fail explicitly. -/
def lower : Functional.Program → Option Imperative.Program
  | .loop i d n l r b => return .loop i d n l r (← StateLowering.lower b)
  | .carried i d n o b => return .buffered i d n o (← StateLowering.lower b)
  | .value b => return .effect (← StateLowering.lower b)
  | .letResult a b => return .seq (← lower a) (← lower b)
  | .branch r a b => return .branch r (← lower a) (← lower b)

theorem lower_correct (p : Functional.Program) (q : Imperative.Program)
    (h : lower p = some q) (input : Input) (s : State) : q.eval input s = p.eval input s := by
  induction p generalizing q s with
  | loop i d n l r b =>
    cases hb : StateLowering.lower b <;> simp [lower,hb] at h
    subst q
    have same := funext fun i => funext fun x => funext fun y => funext fun s =>
      StateLowering.lower_correct b _ hb i x y s [] []
    simpa only [Imperative.Program.eval,Functional.Program.eval] using
      congrArg (fun step => readLoop input step d l r n i s) same
  | carried i d n o b =>
    cases hb : StateLowering.lower b <;> simp [lower,hb] at h
    subst q
    have same := funext fun i => funext fun x => funext fun y => funext fun s =>
      StateLowering.lower_correct b _ hb i x y s [] []
    simp only [Imperative.Program.eval,Functional.Program.eval,
      Imperative.runBuffered_correct,Functional.runCarried_correct]
    exact congrArg (fun step => sourceLoop (fun j => input (j+o)) step d n i s) same
  | value b =>
    cases hb : StateLowering.lower b <;> simp [lower,hb] at h
    subst q
    exact StateLowering.lower_correct b _ hb 0 0 0 s [] []
  | letResult a b ha hb =>
    cases hqa : lower a <;> simp [lower,hqa] at h
    cases hqb : lower b <;> simp [hqb] at h
    subst q
    simp [Imperative.Program.eval,Functional.Program.eval,ha _ hqa,hb _ hqb]
  | branch r a b ha hb =>
    cases hqa : lower a <;> simp [lower,hqa] at h
    cases hqb : lower b <;> simp [hqb] at h
    subst q
    simp [Imperative.Program.eval,Functional.Program.eval,ha _ hqa,hb _ hqb]

end IRComparison.ProgramLowering
