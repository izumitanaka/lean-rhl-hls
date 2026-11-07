import IRComparison.Frontend.LeanBodyPipeline
import IRComparison.Frontend.LeanCertificate

namespace IRComparison
open Lean Elab Command

/-- Automatic comparison entry for ordinary Lean state-update bodies.
    State/Option are the current comparison harness, not a final source DSL. -/
elab "hls_body " source:ident " as " target:ident : command => do
  let sourceName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo source
  let targetName := (← getCurrNamespace) ++ target.getId
  let native ← getEnv
  let some result := LeanBodyPipeline.compile native sourceName
    | throwErrorAt source "certified body compilation failed; supported bodies currently use State.write, optional array reads, state/value bind/return, local beta reductions, nonzero conditionals and List.range n.toNat loops with integer computations, with signature Int → Int → Int → State → Option State. No unproved output was generated."
  for (suffix,compiler,bodyType,body,formalBody,proof,backend) in
      [("imperative", ``BodyBackends.imperative, ``Imperative.Cmd,
        LeanBodyQuotation.imperativeQuote result.source.body.imperative,
        LeanBodyQuotation.imperativeCode result.source.body.imperative,
        result.imperativeProof.term, LeanBodyPipeline.Backend.imperative),
       ("functional", ``BodyBackends.functional, ``Functional.Term,
        LeanBodyQuotation.functionalQuote result.source.body.functional,
        LeanBodyQuotation.functionalCode result.source.body.functional,
        result.functionalProof.term, LeanBodyPipeline.Backend.functional)] do
    let bodyName := .str targetName (suffix ++ "Body")
    liftCoreM <| addAndCompile (.defnDecl {
      name := bodyName, levelParams := [], type := .const bodyType [],
      value := body, hints := .abbrev, safety := .safe })
    let bodyEval := match backend with
      | .imperative => LeanBodyQuotation.imperativeEval formalBody (.bvar 3) (.bvar 2) (.bvar 1) (.bvar 0)
      | .functional => LeanBodyQuotation.functionalEval formalBody (.bvar 3) (.bvar 2) (.bvar 1) (.bvar 0)
    let bodyProof := match backend with
      | .imperative => result.source.imperativeProof
      | .functional => result.source.functionalProof
    liftCoreM <| addDecl (.thmDecl {
      name := .str targetName (suffix ++ "Body_correct"), levelParams := [],
      type := LeanCertificate.expression (LeanNamedBody.specification sourceName bodyEval),
      value := LeanCertificate.expression (LeanNamedBody.close bodyProof) })
    let info ← getConstInfo compiler
    let .forallE _ _ type _ := info.type | throwError "backend signature is not a function"
    liftCoreM <| addAndCompile (.defnDecl {
      name := .str targetName suffix, levelParams := [],
      type := type.instantiate1 (.const bodyName []),
      value := .app (.const compiler []) (.const bodyName []),
      hints := .abbrev, safety := .safe })
    liftCoreM <| addDecl (.thmDecl {
      name := .str targetName (suffix ++ "_correct"), levelParams := [],
      type := LeanCertificate.expression (LeanBodyPipeline.specification backend sourceName formalBody),
      value := LeanCertificate.expression proof })

end IRComparison
