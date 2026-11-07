import IRComparison.Components.ClockedComponent
import IRComparison.Components.ClockedOperation
import IRComparison.Hybrid.HybridWord

/-! BV32 instances of the clocked component contract. This connects its result
to the arithmetic used by the existing mixed IR. `extra` is a chosen latency
contract, not a claim about a synthesized multiplier/divider's timing. -/
namespace IRComparison.WordComponent
open HybridWord

inductive Op where
  | add | sub | mul | udiv
  deriving DecidableEq, Repr

def Op.eval : Op → Word → Word → Word
  | .add => (· + ·)
  | .sub => (· - ·)
  | .mul => (· * ·)
  | .udiv => (· / ·)

def Op.lower : Op → HybridIR.Value → HybridIR.Value → HybridIR.Value
  | .add => HybridWord.add
  | .sub => HybridWord.sub
  | .mul => HybridWord.mul
  | .udiv => HybridWord.udiv

theorem Op.lower_correct (op : Op)
    (ha : a.eval i x y ls ts = some (encode u))
    (hb : b.eval i x y ls ts = some (encode v)) :
    (op.lower a b).eval i x y ls ts = some (encode (op.eval u v)) := by
  cases op with
  | add => exact HybridWord.add_correct ha hb
  | sub => exact HybridWord.sub_correct ha hb
  | mul => exact HybridWord.mul_correct ha hb
  | udiv => exact HybridWord.udiv_correct ha hb

structure Request where
  op : Op
  lhs : Word
  rhs : Word
  deriving DecidableEq, Repr

def Request.eval (r : Request) := r.op.eval r.lhs r.rhs
def Request.lower (r : Request) := r.op.lower (.lit (encode r.lhs)) (.lit (encode r.rhs))

theorem Request.lower_correct (r : Request) :
    r.lower.eval i x y ls ts = some (encode r.eval) := r.op.lower_correct rfl rfl

abbrev State := ClockedComponent.State Request Word
abbrev Input := ClockedComponent.Input Request

/-- From acceptance to response valid takes `extra r + 1` edges. Input
signals during those edges are arbitrary; the captured operands are used. -/
theorem finishes (r : Request) (extra : Request → Nat) (is : List Input)
    (h : is.length = extra r + 1) :
    ClockedComponent.run Request.eval extra .idle (⟨some r, ack⟩ :: is) =
      .response r r.eval := ClockedComponent.request_finishes is h

/-- Compatibility at the operation boundary, not yet a whole-program
translation from the sequential control IR to a clocked machine. -/
theorem finishes_mixed (r : Request) (extra : Request → Nat) (is : List Input)
    (h : is.length = extra r + 1) :
    (ClockedComponent.output
      (ClockedComponent.run Request.eval extra .idle (⟨some r, ack⟩ :: is))).map encode =
      r.lower.eval i x y ls ts := by
  rw [finishes r extra is h, r.lower_correct]
  rfl

/-- The closed controller/component pair finishes with exactly the specified
BV32 value; no fairness premise is needed for this fixed-latency component. -/
theorem controlled_finishes (r : Request) (extra : Request → Nat) :
    ClockedOperation.run Request.eval extra (extra r + 3) (ClockedOperation.start r) =
      ClockedOperation.stop r.eval ∧
    r.lower.eval i x y ls ts = some (encode r.eval) :=
  ⟨ClockedOperation.finishes r,r.lower_correct⟩

end IRComparison.WordComponent
