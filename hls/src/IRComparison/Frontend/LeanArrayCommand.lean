import IRComparison.Frontend.LeanArrayEntry
import IRComparison.Frontend.LeanCertificate
import IRComparison.Core.ArrayControlIR

namespace IRComparison
open Lean Elab Command

elab "hls_array " source:ident " as " target:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo source
  let some r := LeanArrayEntry.compile (← getEnv) name
    | throwErrorAt source "certified Array.map entry failed: expected Array Int → Array Int with a supported pure integer mapper"
  let base := (← getCurrNamespace) ++ target.getId
  for (suffix,functional,type,constructor,proof) in
    [("imperative",false,``ArrayIR.Imperative,``ArrayIR.Imperative.generate,r.imperativeProof),
     ("functional",true,``ArrayIR.Functional,``ArrayIR.Functional.map,r.functionalProof)] do
    liftCoreM <| addAndCompile (.defnDecl {
      name := .str base suffix, levelParams := [], type := .const type [],
      value := .app (.const constructor []) (LeanIRQuotation.quote r.emitted), hints := .abbrev, safety := .safe })
    liftCoreM <| addDecl (.thmDecl {
      name := .str base (suffix ++ "_correct"), levelParams := [],
      type := LeanCertificate.expression (LeanArrayEntry.specification functional name r.emitted),
      value := LeanCertificate.expression proof })

  for (suffix,lower,fact) in [("imperative", ``ArrayControlIR.lowerImperative, ``ArrayControlIR.imperative_correct),
      ("functional", ``ArrayControlIR.lowerFunctional, ``ArrayControlIR.functional_correct)] do
    let ir := mkIdent (.str base suffix)
    let proof := mkIdent (.str base (suffix ++ "_correct"))
    let control := mkIdent (.str target.getId (suffix ++ "Control"))
    let correct := mkIdent (.str target.getId (suffix ++ "Control_correct"))
    let lower := mkIdent lower
    let fact := mkIdent fact
    elabCommand (← `(def $control : ArrayControlIR.Operation := $lower $ir))
    elabCommand (← `(theorem $correct (a : Array Int) :
        ArrayControlIR.run (a.size+2) (.ready $control a) =
          .stopped (some (.array ($source a))) := by
      have h := $fact $ir a
      have hp := $proof a
      change ($ir).eval a = some ($source a) at hp
      rw [hp] at h
      exact h))

end IRComparison
