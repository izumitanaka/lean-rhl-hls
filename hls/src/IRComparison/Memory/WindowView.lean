import IRComparison.Frontend.NativeWindowPlan

namespace IRComparison.WindowView

/-- The window program before committing its reads to one supplier trace.
    This enables checking a common continuation against alternative traces. -/
structure View (array size : Nat) (source : Int → Int → State → Option State) where
  blocks : List NativeWindowPlan.Block
  correct : ∀ s, (s.arrays array).size = size → ∀ x y,
    NativeWindowPlan.evalI (arrayInput (s.arrays array)) x y blocks [] s = source x y s

def View.rebase (v : View array size source) (same : ∀ x y s, source x y s = other x y s) :
    View array size other := ⟨v.blocks,fun s hs x y => (v.correct s hs x y).trans (same x y s)⟩

end IRComparison.WindowView
