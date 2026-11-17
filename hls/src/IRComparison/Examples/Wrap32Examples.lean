import IRComparison.Frontend.LeanHLSCommand

namespace IRComparison.Wrap32Examples
open HybridWord

/-- Runtime operands exercise high bits and underflow, not constant folding. -/
def arithmetic (s : HybridWord.State) : Option HybridWord.State := do
  let x ← (s.arrays 0)[0]?
  let t ← s.write 1 0 (x - 1)
  let t ← t.write 1 1 (x + 4294967295)
  let t ← t.write 1 2 (x * 4294967295)
  t.write 1 3 (-x)
hls_program arithmetic as arithmeticHLS

example (wr : Nat → Circuit.Interval) (e : Circuit.Expr) :
    Circuit.range wr (.wrap32 e) = Circuit.wordRange := rfl

example (wr : Nat → Circuit.Interval) (a b : Circuit.Expr) :
    Circuit.range wr (.wrap32 (.bin .mul a b)) =
      Circuit.range wr (.wrap32 (.bin .mul b a)) := rfl

example (s : IRComparison.State) (w : Nat → Int) (a b : Circuit.Expr) :
    (Circuit.Expr.wrap32 (.bin .mul a b)).eval s w =
      (Circuit.Expr.wrap32 (.bin .mul b a)).eval s w := by
  cases ha : a.eval s w <;> cases hb : b.eval s w <;>
    simp [Circuit.Expr.eval,Circuit.Bin.eval,ha,hb,Int.mul_comm]

-- Natural-number host coordinates never silently wrap onto another bank.
example : Circuit.SystemVerilog.ExternalPorts.request false 4294967296 0 = none := by decide
example : Circuit.SystemVerilog.ExternalPorts.request false 0 4294967296 = none := by decide
example : (Circuit.SystemVerilog.ExternalPorts.request false 4294967295 4294967295).map
    (fun p => (p.id.toNat,p.address.toNat)) = some (4294967295,4294967295) := by decide

end IRComparison.Wrap32Examples
