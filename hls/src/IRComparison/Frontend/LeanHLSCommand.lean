import IRComparison.Frontend.LeanWordCommand
import IRComparison.Frontend.WordLoadingCompleteness
import IRComparison.Frontend.CertifiedHLS
import IRComparison.Frontend.FixedHLS

namespace IRComparison
open Lean Elab Command

/-- Ordinary Lean definition → frontend evidence → executable whole compiler
and its source-to-text theorem. No source/IR or source/RTL lemma is requested
from the user. The exported theorem applies the general compiler theorem. -/
elab "hls_certified " source:ident " as " target:ident : command => do
  elabCommand (← `(hls_word $source as $target))
  let sourceName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo source
  let base := (← getCurrNamespace) ++ target.getId
  let bodyId := mkIdent (.str base "wordBody")
  let proofId := mkIdent (.str base "wordBody_correct")
  let entryName := .str base "entry"
  let entryId := mkIdent (.str target.getId "entry")
  elabCommand (← `(def $entryId : CertifiedHLS.BodyEntry $source :=
    ⟨$bodyId,$proofId⟩))
  let compileId := mkIdent (.str target.getId "compile")
  elabCommand (← `(def $compileId (size array : Nat) (start stride : Int)
      (count : Nat) (supplier : Unit → List Int) (outputs : List Nat)
      (sizes : Nat → Nat) (layout : Array (Nat × Nat)) (fuel : Nat := 4096)
      (strategy : Circuit.Pipelining.LoopStrategy := .rolled) :=
    CertifiedHLS.BodyEntry.compile $entryId size array start stride count supplier outputs sizes layout fuel strategy))
  let proof := mkApp2 (.const ``CertifiedHLS.BodyEntry.compile_correct [])
    (.const sourceName []) (.const entryName [])
  let type ← liftTermElabM <| Meta.inferType proof
  liftCoreM <| addDecl (.thmDecl {
    name := .str base "correct",levelParams := [],type := type,value := proof })

/-- Whole State-valued Lean program. The administrative lift supplies unused
legacy scalar parameters; the exported theorem refers to the original function. -/
elab "hls_program " source:ident " as " target:ident : command => do
  let sourceName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo source
  let some (.defnInfo info) := (← getEnv).find? sourceName
    | throwErrorAt source "expected an ordinary Lean definition"
  if info.safety != .safe then
    throwErrorAt source "HLS input must be a safe Lean definition"
  unless ← liftTermElabM (Meta.isDefEq info.type (.const ``CertifiedHLS.Program [])) do
    throwErrorAt source "expected HybridWord.State → Option HybridWord.State"
  let base := (← getCurrNamespace) ++ target.getId
  let liftedName := .str base "sourceBody"
  let w := WordFrontend.word
  let value := Lean.Expr.lam `i w (.lam `x w (.lam `y w info.value .default) .default) .default
  -- The public type may be written using the Program abbreviation. Use the
  -- explicit, already checked signature for this administrative definition;
  -- addAndCompile still asks Lean to check the unchanged source body.
  let programType := Lean.Expr.forallE `s WordFrontend.state
    (WordFrontend.option WordFrontend.state) .default
  let type := Lean.Expr.forallE `i w (.forallE `x w (.forallE `y w programType .default) .default) .default
  liftCoreM <| addAndCompile (.defnDecl {
    name := liftedName,levelParams := [],type,value,hints := .abbrev,safety := .safe })
  let liftedId := mkIdent liftedName
  elabCommand (← `(hls_word $liftedId as $target))
  let bodyId := mkIdent (.str base "wordBody")
  let proofId := mkIdent (.str base "wordBody_correct")
  let entryName := .str base "entry"
  let entryId := mkIdent (.str target.getId "entry")
  elabCommand (← `(def $entryId : CertifiedHLS.ProgramEntry $source := ⟨$bodyId,$proofId⟩))
  let compileId := mkIdent (.str target.getId "compile")
  elabCommand (← `(def $compileId (outputs : List Nat) (sizes : Nat → Nat)
      (layout : Array (Nat × Nat)) (fuel : Nat := 4096)
      (strategy : Circuit.Pipelining.LoopStrategy := .rolled) :=
    CertifiedHLS.ProgramEntry.compile $entryId outputs sizes layout fuel strategy))
  let proof := mkApp2 (.const ``CertifiedHLS.ProgramEntry.compile_correct [])
    (.const sourceName []) (.const entryName [])
  let type ← liftTermElabM <| Meta.inferType proof
  liftCoreM <| addDecl (.thmDecl {
    name := .str base "correct",levelParams := [],type,value := proof })

/-- Fixed declarations are checked for the entire parsed body, including all
branches and loop bodies. The native definition is still an ordinary Lean def. -/
elab "hls_fixed_program " source:ident " using " declarations:ident " as " target:ident : command => do
  let internal := mkIdent (.str target.getId "native")
  elabCommand (← `(hls_program $source as $internal))
  let base := (← getCurrNamespace) ++ target.getId
  let bodyEntry := mkIdent (.str (.str base "native") "entry")
  let declarationsName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo declarations
  let ds := Lean.Expr.const declarationsName []
  let unique := mkApp (.const ``FixedMemory.unique []) ds
  unless ← liftTermElabM (Meta.isDefEq unique (.const ``Bool.true [])) do
    throwErrorAt declarations "fixed-memory declarations contain duplicate array identifiers"
  let code := Lean.Expr.const (.str (.str base "native") "wordBody") []
  let checked := mkApp2 (.const ``FixedMemory.declared []) ds code
  unless ← liftTermElabM (Meta.isDefEq checked (.const ``Bool.true [])) do
    throwErrorAt source "fixed-memory input uses an undeclared array or a copy length different from its source/destination declarations"
  let entryId := mkIdent (.str target.getId "entry")
  elabCommand (← `(def $entryId : FixedHLS.Entry $source :=
    ⟨$bodyEntry,$declarations,by decide,by decide⟩))
  let compileId := mkIdent (.str target.getId "compile")
  elabCommand (← `(def $compileId (outputs : List Nat) (fuel : Nat := 4096)
      (strategy : Circuit.Pipelining.LoopStrategy := .rolled) :=
    FixedHLS.Entry.compile $entryId outputs fuel strategy))
  let sourceName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo source
  let proof := mkApp2 (.const ``FixedHLS.Entry.compile_correct [])
    (.const sourceName []) (.const (.str base "entry") [])
  let type ← liftTermElabM <| Meta.inferType proof
  liftCoreM <| addDecl (.thmDecl {
    name := .str base "correct",levelParams := [],type,value := proof })
  let totalProof := mkApp2 (.const ``FixedHLS.Entry.compile_total [])
    (.const sourceName []) (.const (.str base "entry") [])
  let totalType ← liftTermElabM <| Meta.inferType totalProof
  liftCoreM <| addDecl (.thmDecl {
    name := .str base "generates",levelParams := [],type := totalType,value := totalProof })

end IRComparison
