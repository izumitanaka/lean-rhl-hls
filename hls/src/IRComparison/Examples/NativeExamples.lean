import IRComparison.Frontend.NativeBody
import IRComparison.Examples.Examples

namespace IRComparison.NativeExamples

/-- Actual native Lean source body. -/
def meanBody (i x y : Int) (s : State) : Option State :=
  s.write 0 i ((x + y) / 2)

/-- Explicit assembly of the generic lowering rules for now. This is NOT
    an implemented, generally verified Lean.Expr quotation/parser. -/
def meanCode : NativeBody.Code meanBody :=
  NativeBody.store 0 NativeBody.index
    (NativeBody.divide (NativeBody.add NativeBody.left NativeBody.right) (NativeBody.literal 2))

/-- Same native program for both paths; no Source.Cmd or IR evaluator appears. -/
def algorithm (input : Input) (start stride : Int) (count : Nat) (s : State) : Option State := do
  let mut state := s
  for k in List.range count do
    let i := start + (k : Int) * stride
    let x ← input i
    let y ← input (i + stride)
    state ← meanBody i x y state
  return state

theorem imperative_correct (input : Input) (start stride : Int) (count : Nat) (s : State) :
    (NativeBody.compileImperative meanCode start stride count 0 stride).eval input s =
      algorithm input start stride count s := by
  rw [NativeBody.compileImperative_correct]
  simp [NativeLoop.run, NativeLoop.readBody, algorithm, Option.bind_assoc]

theorem functional_correct (input : Input) (start stride : Int) (count : Nat) (s : State) :
    (NativeBody.compileFunctional meanCode start stride count 0 stride).eval input s =
      algorithm input start stride count s := by
  rw [NativeBody.compileFunctional_correct]
  simp [NativeLoop.run, NativeLoop.readBody, algorithm, Option.bind_assoc]

/-- Native state-dependent update, rather than a filter-only pure calculation. -/
def updateBody (_i x y : Int) (s : State) : Option State := do
  if x != 0 then
    let old ← (s.arrays 0)[0]?
    s.write 0 0 (old + y)
  else
    s.write 0 0 99

def updateCode : NativeBody.Code updateBody := by
  let code := NativeBody.branch NativeBody.left
    (NativeBody.store 0 (NativeBody.literal 0)
      (NativeBody.add (NativeBody.read 0 (NativeBody.literal 0)) NativeBody.right))
    (NativeBody.store 0 (NativeBody.literal 0) (NativeBody.literal 99))
  exact {
    imperative := code.imperative
    functional := code.functional
    imperative_correct := by
      intros
      simpa [code, updateBody, Option.bind_assoc] using code.imperative_correct _ _ _ _
    functional_correct := by
      intros
      simpa [code, updateBody, Option.bind_assoc] using code.functional_correct _ _ _ _ }

theorem update_imperative_correct (input : Input) (start stride : Int) (count : Nat) (s : State) :
    (NativeBody.compileImperative updateCode start stride count 0 stride).eval input s =
      NativeLoop.run (NativeLoop.readBody input updateBody 0 stride) start stride count s :=
  NativeBody.compileImperative_correct updateCode input start stride count 0 stride s

theorem update_functional_correct (input : Input) (start stride : Int) (count : Nat) (s : State) :
    (NativeBody.compileFunctional updateCode start stride count 0 stride).eval input s =
      NativeLoop.run (NativeLoop.readBody input updateBody 0 stride) start stride count s :=
  NativeBody.compileFunctional_correct updateCode input start stride count 0 stride s

example : Examples.observe (algorithm (arrayInput #[2,4,6,8]) 0 1 3 (Examples.initial 3)) =
    some (0,#[3,5,7]) := by decide

example : Examples.observe (algorithm (arrayInput #[2,4,6,8]) 3 (-1) 3 (Examples.initial 4)) =
    some (0,#[0,3,5,7]) := by decide

example : Examples.observe ((NativeBody.compileFunctional updateCode 0 1 3 0 1).eval
    (arrayInput #[1,2,3,4]) (Examples.initial 1)) = some (0,#[9]) := by decide

end IRComparison.NativeExamples
