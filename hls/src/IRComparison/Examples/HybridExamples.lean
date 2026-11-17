import IRComparison.Hybrid.HybridControl
import IRComparison.Examples.GlobalPipelineExamples

namespace IRComparison.HybridExamples
open HybridIR
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def initial : State := ⟨fun r => if r = 2 then 7 else 0,fun _ => #[10,20,30,40]⟩
def sample : Expr := .add (.read 0 .index) (.mul (.reg 2) (.local 0))
example : (extract sample).eval 1 0 0 initial [3] [999] = some 41 := by decide +kernel
example : (extract (.select (.lit 0) (.read 0 (.lit 99)) (.lit 7))).eval 0 0 0 initial [] [] = some 7 := by decide +kernel
example : (extract (.select (.lit 1) (.read 0 (.lit 99)) (.lit 7))).eval 0 0 0 initial [] [] = none := by decide +kernel
example : (extract (.read 0 (.lit (-1)))).eval 0 0 0 initial [] [] = none := by decide +kernel

/-- Bind scopes, repeated state updates, and dynamically counted loops remain
    executable; extracting reads does not cache them across writes. -/
def updates : Imperative.Cmd := .seq
  (.repeat 2 (.assign 0 (.add (.reg 0) (.lit 1))))
  (.forRange (.lit 3) (.store 0 (.local 0) (.add (.reg 0) (.local 0))))
example : ((MemoryCmd.fromImperative updates).target.eval 0 0 0 initial [] []).map (fun (s,q) => (s.regs 0,s.arrays 0,q)) =
    some (2,#[2,3,4,40],[]) := by decide +kernel

#eval show IO Unit from do
  match HybridCommandControl.run 0 0 0 100 (.running [((MemoryCmd.fromImperative updates).target,[])] initial []) with
  | .stopped r => unless r.map (fun (s,q) => (s.regs 0,s.arrays 0,q)) == some (2,#[2,3,4,40],[]) do
      throw (IO.userError "hybrid loop control mismatch")
  | _ => throw (IO.userError "hybrid loop control did not finish")

end IRComparison.HybridExamples
