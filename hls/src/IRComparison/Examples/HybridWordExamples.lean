import IRComparison.Hybrid.HybridWordPipeline

namespace IRComparison.HybridWordExamples
open HybridWord
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

def pairSum : Cmd := .assign 0
  (.add (.read 0 .index) (.read 0 (.add .index (.lit 1))))

-- Ordinary Lean computation used as a specification. Its automatic parsing is
-- not implemented by this test; the IR construction above is explicit.
def nativePairSum (i : Word) (s : HybridWord.State) : Option HybridWord.State := do
  let a ← (s.arrays 0)[i.toNat]?
  let b ← (s.arrays 0)[(i+1).toNat]?
  return s.set 0 (a+b)

theorem pairSum_native (i x y : Word) (s : HybridWord.State) :
    pairSum.eval i x y s [] = nativePairSum i s := by
  simp [pairSum, Cmd.eval, HybridWord.Expr.eval, nativePairSum, Option.bind_assoc]
def initial : HybridWord.State :=
  ⟨fun _ => 0, fun _ => #[4294967295, 2, 3, 4]⟩
def forward := compile 4 0 pairSum 1 3 0 [0,1,2,3]
def reverse := compile 4 0 pairSum (-1) 3 2 [0,1,2,3]

-- These assert that actual optimization occurred, not only fallback correctness.
example : forward.isFIFO = true ∧ forward.hasBuffer = true := by decide +kernel
example : reverse.isFIFO = false ∧ reverse.hasBuffer = true := by decide +kernel
example : (pairSum.eval 0 0 0 initial []).map (fun s => s.regs 0) = some 1 := by decide +kernel
example : (forward.eval (initial.encode.arrays 0) 0 0 initial.encode
    [4294967295,2,3,4]).map (fun s => s.regs 0) = some 7 := by decide +kernel
example : (reverse.eval (initial.encode.arrays 0) 0 0 initial.encode []).map
    (fun s => s.regs 0) = some 1 := by decide +kernel

-- Multiplication overflow, unsigned division, zero divisor, and failing reads.
example : (HybridWord.Expr.mul (.lit 2147483648) (.lit 2)).eval 0 0 0 initial [] = some 0 := by decide +kernel
example : (HybridWord.Expr.div (.lit 4294967295) (.lit 2)).eval 0 0 0 initial [] = some 2147483647 := by decide +kernel
example : (HybridWord.Expr.div (.lit 7) (.lit 0)).eval 0 0 0 initial [] = some 0 := by decide +kernel
example : (HybridWord.Expr.read 0 (.sub (.lit 0) (.lit 1))).eval 0 0 0 initial [] = none := by decide +kernel
example : (HybridWord.Expr.select (.lit 0) (.read 0 (.lit 99)) (.lit 7)).eval 0 0 0 initial [] = some 7 := by decide +kernel

#print axioms HybridWord.Expr.lower_correct
#print axioms HybridWord.Cmd.lower_correct
#print axioms HybridWord.compile_correct
#print axioms HybridWord.control_finishes
#print axioms HybridWord.optimized_control_finishes
end IRComparison.HybridWordExamples
