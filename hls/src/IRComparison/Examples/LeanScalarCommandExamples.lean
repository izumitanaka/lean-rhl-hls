import IRComparison.Frontend.LeanScalarCommand

namespace IRComparison.LeanScalarCommandExamples

def mean (_i x y : Int) : Int := (x + y) / 2
hls_scalar mean as generated

/-- The emitted theorem is about every input/state and loop configuration,
    not only the concrete execution checks below. -/
example (reg : Nat) (start stride : Int) (count : Nat) (l r : Int) (input : Input) (s : State) :
    (generated.imperative reg start stride count l r).eval input s =
      ScalarBackends.runSource mean reg start stride count l r input s :=
  generated.imperative_correct reg start stride count l r input s

example (reg : Nat) (start stride : Int) (count : Nat) (l r : Int) (input : Input) (s : State) :
    (generated.functional reg start stride count l r).eval input s =
      ScalarBackends.runSource mean reg start stride count l r input s :=
  generated.functional_correct reg start stride count l r input s

private def initial : State := ⟨fun _ => 0, fun _ => #[]⟩
private def input : Input := arrayInput #[2,4,8,16]

def observe (result : Option State) : Option Int := result.map (fun s => s.regs 0)

example : observe ((generated.imperative 0 0 1 3 0 1).eval input initial) = some 12 := by decide
example : observe ((generated.functional 0 0 1 3 0 1).eval input initial) = some 12 := by decide
example : observe ((generated.imperative 0 3 (-1) 3 0 (-1)).eval input initial) = some 3 := by decide
example : observe ((generated.functional 0 3 (-1) 3 0 (-1)).eval input initial) = some 3 := by decide
example : observe ((generated.imperative 0 0 1 4 0 1).eval input initial) = none := by decide
example : observe ((generated.functional 0 0 1 4 0 1).eval input initial) = none := by decide
example : observe ((generated.imperative 0 0 1 2 0 2).eval input initial) = some 10 := by decide
example : observe ((generated.functional 0 0 1 2 0 2).eval input initial) = some 10 := by decide

end IRComparison.LeanScalarCommandExamples
