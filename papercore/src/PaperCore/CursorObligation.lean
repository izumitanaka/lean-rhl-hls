import PaperCore.DirectBody

namespace PaperCore.CursorObligation
open AccessAnalysis

def Obligation (summary : Summary) (counterAfter : Affine)
    (shape : Int → IndexMap → Prop) (stop step : Int) : Prop :=
  ∀ k indices, shape k indices → k ≠ stop →
    ∃ afterIndices,
      DirectBody.consume indices (summary.accesses.map (SymbolicAccess.eval k)) = some afterIndices ∧
      shape (counterAfter.eval k + step) afterIndices


end PaperCore.CursorObligation
