import IRComparison.Frontend.LeanTypeReduction

namespace IRComparison.LeanEnvironmentProvenance
open Lean4Lean

/-- Every delta equation is an actual safe native definition, never an axiom
    asserting that a source program equals an optimized program. -/
def Equations (native : Lean.Environment) (env : VEnv) : Prop :=
  ∀ equation, env.defeqs equation →
    ∃ name, ∃ d : LeanTypeReduction.Definition native name, equation = d.equation

structure Faithful (native : Lean.Environment) (env : VEnv) : Prop where
  constants : LeanLibrary.Faithful native env
  equations : Equations native env

def aliasDefinition (entry : LeanTypeAliases.Alias native name) :
    LeanTypeReduction.Definition native name :=
  ⟨entry.declaration,entry.found,entry.named,entry.safe,
    ⟨LeanTypeAliases.identityType,entry.type⟩,⟨LeanTypeAliases.identityBody,entry.body⟩⟩

theorem alias_equation (entry : LeanTypeAliases.Alias native name) :
    entry.equation = (aliasDefinition entry).equation := by
  simp [LeanTypeAliases.Alias.equation, aliasDefinition, LeanTypeReduction.Definition.equation,
    entry.arity, VLevel.params]

theorem install_definition (baseFaithful : Faithful native base)
    (d : LeanTypeReduction.Definition native name) : Faithful native (d.install base) where
  constants := baseFaithful.constants
  equations := by
    intro equation registered
    rcases registered with same | previous
    · exact ⟨name,d,same⟩
    · exact baseFaithful.equations equation previous

theorem install_alias (baseFaithful : Faithful native base)
    (entry : LeanTypeAliases.Alias native name) : Faithful native (entry.install base) where
  constants := baseFaithful.constants
  equations := by
    intro equation registered
    rcases registered with same | previous
    · exact ⟨name,aliasDefinition entry,same.trans (alias_equation entry)⟩
    · exact baseFaithful.equations equation previous

theorem install_types (names : List Lean.Name)
    (installed : LeanLibrary.installTypes native VEnv.empty names = some env) : Faithful native env where
  constants := LeanLibrary.installTypes_faithful names LeanLibrary.faithful_empty installed
  equations := by
    intro equation registered
    exact False.elim (LeanLibrary.installTypes_no_equations names (fun _ h => h) installed equation registered)

end IRComparison.LeanEnvironmentProvenance
