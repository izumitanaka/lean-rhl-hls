import IRComparison.Core.Source

namespace IRComparison.Frontend

/-- Unrecognized source operations remain executable, interleaved with
    optimized code. Loop indices are lexically scoped in both evaluators. -/
inductive Target (Code : Type) where
  | original (command : Source.Cmd)
  | code (program : Code)
  | seq (a b : Target Code)
  | branch (condition : Source.Scalar) (yes no : Target Code)
  | loop (start stride : Int) (count : Nat) (body : Target Code)

def Target.eval (run : Code → Input → State → Option State) (input : Input)
    (i : Int) : Target Code → State → Option State
  | .original p, s => p.eval input i s
  | .code p, s => run p input s
  | .seq a b, s => do b.eval run input i (← a.eval run input i s)
  | .branch e a b, s => do
      if (← e.eval i s) != 0 then a.eval run input i s else b.eval run input i s
  | .loop start stride n b, s => Source.iterate (fun j => b.eval run input j) stride n start s

/-- A common pattern extractor feeds either independently proved optimizer. -/
def compile (emit : Imperative.Program → Code) : Source.Cmd → Target Code
  | .seq a b => .seq (compile emit a) (compile emit b)
  | .branch e a b => .branch e (compile emit a) (compile emit b)
  | .loop start stride n b =>
      match Source.extract b with
      | some q => .code (emit (.loop start stride n q.leftOffset q.rightOffset q.body))
      | none => .loop start stride n (compile emit b)
  | p => .original p

theorem compile_correct (emit : Imperative.Program → Code)
    (run : Code → Input → State → Option State)
    (emit_correct : ∀ p input s, run (emit p) input s = p.eval input s)
    (p : Source.Cmd) (input : Input) (i : Int) (s : State) :
    (compile emit p).eval run input i s = p.eval input i s := by
  induction p generalizing i s with
  | skip | assign | store | load => rfl
  | seq a b ha hb => simp [compile, Target.eval, Source.Cmd.eval, ha, hb]
  | branch e a b ha hb => simp [compile, Target.eval, Source.Cmd.eval, ha, hb]
  | loop start stride n b hb =>
      cases he : Source.extract b with
      | none =>
          simp only [compile, he, Target.eval, Source.Cmd.eval]
          exact Source.iterate_congr _ _ (fun j t => hb j t) stride n start s
      | some q =>
          simp only [compile, he, Target.eval, emit_correct, Imperative.Program.eval,
            Source.Cmd.eval]
          exact (Source.extracted_loop_correct b q he input stride n start s).symm

abbrev runImperative (p : Imperative.Program) (input : Input) := p.eval input
abbrev runFunctional (p : Functional.Program) (input : Input) := p.eval input

abbrev compileImperative := compile Imperative.transform

abbrev compileFunctional := compile (fun p => Functional.transform (lowerProgram p))

theorem compileImperative_correct (p : Source.Cmd) (input : Input) (i : Int) (s : State) :
    (compileImperative p).eval runImperative input i s = p.eval input i s :=
  compile_correct _ _ Imperative.transform_correct p input i s

theorem compileFunctional_correct (p : Source.Cmd) (input : Input) (i : Int) (s : State) :
    (compileFunctional p).eval runFunctional input i s = p.eval input i s := by
  apply compile_correct
  intro q xs t
  simp [runFunctional, Functional.transform_correct, lowerProgram_correct]

theorem compilers_agree (p : Source.Cmd) (input : Input) (i : Int) (s : State) :
    (compileImperative p).eval runImperative input i s =
      (compileFunctional p).eval runFunctional input i s := by
  rw [compileImperative_correct, compileFunctional_correct]

end IRComparison.Frontend
