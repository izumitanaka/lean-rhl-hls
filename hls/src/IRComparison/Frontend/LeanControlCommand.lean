import IRComparison.Frontend.LeanBodyCommand
import IRComparison.Core.ControlIR

namespace IRComparison
open Lean Elab Command

/-- Compile the common supported body input to executable controllers. The
    existing optimized loop wrappers are still produced separately by hls_body. -/
elab "hls_control " source:ident " as " target:ident : command => do
  let base := target.getId
  let iBody := mkIdent (.str base "imperativeBody")
  let fBody := mkIdent (.str base "functionalBody")
  let iProof := mkIdent (.str base "imperativeBody_correct")
  let fProof := mkIdent (.str base "functionalBody_correct")
  let iCode := mkIdent (.str base "imperativeControl")
  let fCode := mkIdent (.str base "functionalControl")
  let fLower := mkIdent (.str base "functionalControl_lowered")
  let iCorrect := mkIdent (.str base "imperativeControl_correct")
  let fCorrect := mkIdent (.str base "functionalControl_correct")
  elabCommand (← `(hls_body $source as $target))
  elabCommand (← `(def $iCode : List ControlIR.Instr := ControlIR.lower $iBody))
  -- The proof of isSome and the following equality are kernel checked. There
  -- is no empty-program fallback when allocation is unsupported.
  elabCommand (← `(def $fCode : List ControlIR.Instr :=
    (ControlIR.lowerFunctional $fBody).get (by decide)))
  elabCommand (← `(theorem $fLower : ControlIR.lowerFunctional $fBody = some $fCode := by rfl))
  elabCommand (← `(theorem $iCorrect (i x y : Int) (s : State) :
      ∃ n, ControlIR.run i x y n (.running $iCode s []) = .stopped ($source i x y s) := by
    have h := ControlIR.lower_finishes $iBody i x y s []
    have hb : Imperative.Cmd.eval i x y $iBody s [] = $source i x y s := $iProof i x y s
    rw [hb] at h
    exact h))
  elabCommand (← `(theorem $fCorrect (i x y : Int) (s : State) :
      ∃ n, ControlIR.run i x y n (.running $fCode s []) = .stopped ($source i x y s) := by
    have h := ControlIR.lowerFunctional_finishes $fBody $fCode $fLower i x y s []
    have hb : Functional.Term.eval i x y $fBody [s] [] = $source i x y s := $fProof i x y s
    rw [hb] at h
    exact h))

end IRComparison
