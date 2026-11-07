import IRComparison.Frontend.WordFrontend

namespace IRComparison
open Lean Elab Command

/-- Ordinary Lean definition input. The command only exports the already
formally constructed body and proof, as hls_body does for the Int frontend. -/
elab "hls_word " source:ident " as " target:ident : command => do
  let sourceName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo source
  let native ← getEnv
  let some result := WordFrontend.compile native sourceName
    | throwErrorAt source "BV32 frontend could not construct the formal source connection. No unproved output was generated."
  let base := (← getCurrNamespace) ++ target.getId
  let bodyName := .str base "wordBody"
  liftCoreM <| addAndCompile (.defnDecl {
    name := bodyName,levelParams := [],type := .const ``HybridWord.Cmd [],
    value := result.code,hints := .abbrev,safety := .safe })
  liftCoreM <| addDecl (.thmDecl {
    name := .str base "wordBody_correct",levelParams := [],
    type := WordFrontend.specification sourceName (.const bodyName []),
    value := LeanCertificate.expression result.proof.proofCore.val })
  let bodyId := mkIdent bodyName
  let proofId := mkIdent (.str base "wordBody_correct")
  let kernelId := mkIdent (.str target.getId "kernel")
  elabCommand (← `(def $kernelId (size array : Nat) (start stride : Int) (count : Nat)
      (supplier : Unit → List Int) : HybridWord.Kernel :=
    { body := $bodyId, native := $source, correct := $proofId,
      size := size, array := array, start := start, stride := stride, count := count, supplier := supplier }))

end IRComparison
