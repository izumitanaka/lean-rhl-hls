import IRComparison.Frontend.WordSyntaxEnvironment

/-! Native declarations → signature loading → contextual source induction.
The source judgment and static signature table are independent of compiler
success. This module covers the constructors of ScopedSyntax; administrative
closure forms are not silently identified with that completed fragment. -/
namespace IRComparison.WordFrontend.NativeCompleteness
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic

/-- A static type environment for the source and proof library. Entries are
actual native declarations and have finite dependency paths from the source
or the fixed library. Neither loading nor parsing success is a field. -/
structure SourceTable (native : Lean.Environment) (name : Lean.Name) (value : Lean.Expr) where
  model : VEnv
  declarations : ∀ n signature, model.constants n = some signature →
    ∃ declaration : LeanLibrary.Declaration native n, signature = declaration.signature
  reachable : ∀ n signature, model.constants n = some signature →
    DependencyClosure.Reachable (typeDependencies native) (libraryRoots name value) n

theorem SourceTable.installed (table : SourceTable native name value)
    (loaded : WordFrontend.load native name = some lib)
    (sourceValue : lib.source.declaration.value = value) :
    SignatureExtension table.model lib.model := by
  intro n signature found
  obtain ⟨declaration,same⟩ := table.declarations n signature found
  rw [same]
  apply loaded_source_signature loaded declaration
  rw [sourceValue]
  exact table.reachable n signature found

/-- Freshness of a source name relative to the fixed alias and fact library.
This is normally ensured by the namespace of the administrative wrapper. -/
structure NameFresh (name : Lean.Name) : Prop where
  word : ``HybridWord.Word ≠ name
  bitvec : ``BitVec ≠ name
  ofNat : ``OfNat ≠ name
  numerals : ∀ n ∈ [``Nat.zero,``Nat.succ,``Nat.mul], n ≠ name
  classes : ∀ op : Binary, op.className ≠ name
  heterogeneous : ∀ op : Binary, op.heterogeneous ≠ name
  neg : ``Neg ≠ name
  scalarHeads : ∀ n ∈ LexicalScalarSyntax.valueHeads, n ≠ name
  heads : ∀ n ∈ [``HybridWord.State,``Eq,``Option.some,``Pure.pure,
    ``HybridWord.State.write,``HybridWord.State.copy,``ite,``Bind.bind,``ForIn.forIn,
    ``WordLoopFacts.lift,``PUnit,``Nat,``List.foldlM,``Option,``GetElem?.getElem?,``GetElem?,``Array.instGetElem?NatLtSize,``HybridWord.State.arrays,``BitVec.toNat,``ForInStep,``bne,``Decidable,``instDecidableEqBool], n ≠ name

end IRComparison.WordFrontend.NativeCompleteness
