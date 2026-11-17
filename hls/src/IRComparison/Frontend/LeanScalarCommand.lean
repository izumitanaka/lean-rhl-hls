import IRComparison.Frontend.LeanCertificate

namespace IRComparison
open Lean Elab Command

/-- Compile an ordinary scalar definition into both optimized IR backends.
    This command exports the generally constructed certificates; the kernel
    check is an additional validation, not the compiler's correctness argument. -/
elab "hls_scalar " source:ident " as " target:ident : command => do
  let sourceName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo source
  let targetName := (← getCurrNamespace) ++ target.getId
  let native ← getEnv
  let some result := LeanScalarPipeline.compile native sourceName
    | throwErrorAt source "certified scalar compilation failed; expected a safe ordinary definition with three Int arguments and a supported Int body (arithmetic, integer let, or nonzero conditional). No default meaning or unproved output was generated."
  let code := LeanIRQuotation.quote result.source.entry.compiled.body.emitted
  let codeName := targetName ++ `code
  liftCoreM <| addAndCompile (.defnDecl {
    name := codeName, levelParams := [], type := .const ``IRComparison.Expr [],
    value := code, hints := .abbrev, safety := .safe })
  for (suffix,compiler,backend) in
      [("imperative", ``ScalarBackends.imperative, LeanScalarPipeline.Backend.imperative),
       ("functional", ``ScalarBackends.functional, LeanScalarPipeline.Backend.functional)] do
    let info ← getConstInfo compiler
    let .forallE _ _ type _ := info.type | throwError "backend signature is not a function"
    liftCoreM <| addAndCompile (.defnDecl {
      name := .str targetName suffix, levelParams := [],
      type := type.instantiate1 (.const codeName []),
      value := .app (.const compiler []) (.const codeName []),
      hints := .abbrev, safety := .safe })
    liftCoreM <| addDecl (LeanCertificate.declaration (.str targetName (suffix ++ "_correct")) result backend)

end IRComparison
