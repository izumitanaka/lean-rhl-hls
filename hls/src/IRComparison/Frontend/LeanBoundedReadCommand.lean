import IRComparison.Frontend.LeanBoundedReadEntry
import IRComparison.Frontend.LeanCertificate
import IRComparison.Core.ArrayControlIR

namespace IRComparison
open Lean Elab Command

elab "hls_get " source:ident " as " target:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo source
  let some r := LeanBoundedReadEntry.compile (← getEnv) name
    | throwErrorAt source "certified bounded read failed: expected a direct Array Int / Fin a.size read"
  let base := (← getCurrNamespace) ++ target.getId
  for (suffix,functional,type,constructor,proof) in
    [("imperative",false,``BoundedReadIR.Imperative,``BoundedReadIR.Imperative.load,r.imperativeProof),
     ("functional",true,``BoundedReadIR.Functional,``BoundedReadIR.Functional.index,r.functionalProof)] do
    liftCoreM <| addAndCompile (.defnDecl {
      name := .str base suffix, levelParams := [], type := .const type [],
      value := .const constructor [], hints := .abbrev, safety := .safe })
    liftCoreM <| addDecl (.thmDecl {
      name := .str base (suffix ++ "_correct"), levelParams := [],
      type := LeanCertificate.expression (LeanBoundedReadEntry.specification functional name),
      value := LeanCertificate.expression proof })

  for (suffix,lower,fact) in [("imperative", ``ArrayControlIR.lowerImperativeGet, ``ArrayControlIR.imperative_get_correct),
      ("functional", ``ArrayControlIR.lowerFunctionalGet, ``ArrayControlIR.functional_get_correct)] do
    let ir := mkIdent (.str base suffix)
    let proof := mkIdent (.str base (suffix ++ "_correct"))
    let control := mkIdent (.str target.getId (suffix ++ "Control"))
    let correct := mkIdent (.str target.getId (suffix ++ "Control_correct"))
    let lower := mkIdent lower
    let fact := mkIdent fact
    elabCommand (← `(def $control (k : Nat) : ArrayControlIR.Operation := $lower $ir k))
    elabCommand (← `(theorem $correct (a : Array Int) (i : Fin a.size) :
        ArrayControlIR.run 1 (.ready ($control i.val) a) =
          .stopped (some (.scalar ($source a i))) := by
      have h := $fact $ir a i.val
      have hp := $proof a i
      change ($ir).eval a i.val = some ($source a i) at hp
      rw [hp] at h
      exact h))

end IRComparison
