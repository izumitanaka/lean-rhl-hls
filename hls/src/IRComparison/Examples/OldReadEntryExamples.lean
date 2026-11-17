import IRComparison.Frontend.LeanControlCommand

namespace IRComparison.OldReadEntryExamples

def previous (i x _y : Int) (s : State) : Option State := do
  let next ← s.write 0 i x
  let old ← (s.arrays 0)[0]?
  next.write 1 0 old

hls_control previous as saved

example : saved.imperativeControl = saved.functionalControl := rfl

def initial : State := ⟨fun _ => 0, fun a => if a = 0 then #[7,8] else #[0]⟩
def observe (r : ControlIR.Config) : Option (Option (Array Int × Array Int)) :=
  match r with
  | .running .. | .inSnapshots .. => none
  | .stopped result => some (result.map fun s => (s.arrays 0,s.arrays 1))

example : observe (ControlIR.run 0 99 0 40 (.running saved.imperativeControl initial [])) =
    some (some (#[99,8],#[7])) := by decide +kernel
example : observe (ControlIR.run 5 99 0 40 (.running saved.functionalControl initial [])) =
    some none := by decide +kernel

end IRComparison.OldReadEntryExamples
