import IRComparison.Frontend.WordBinder
import IRComparison.Frontend.WordBodyCompleteness

/-! Type aliases in scalar bindings do not change the accepted source grammar.
The actual binder is retained in the source and certificate; only the library
fact's Word-domain interface requires a conversion. -/
namespace IRComparison.WordFrontend.WordBinder
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic
set_option maxHeartbeats 800000

theorem Annotation.domain_proved (annotation : Annotation) (setup : AliasSetup env)
    (library : Signatures env) :
    ∃ equation, LeanStructuralConversion.prove env setup.basic setup.exposure 0 63 ctx
      annotation.core wordType = some equation ∧ equation.type = .sort (.succ .zero) := by
  cases annotation with
  | word =>
    exact LeanStructuralConversion.prove_reflexive_complete
      (Annotation.type_typed .word library) setup.basic_word_refl_none 62 setup.exposure
  | bitvec =>
    obtain ⟨result,accepted,kind⟩ := setup.bitvec_word (U := 0) (ctx := ctx)
    obtain ⟨equation,proved,typed⟩ := LeanStructuralConversion.prove_base_complete accepted 62 setup.exposure
    exact ⟨equation,proved,typed.trans (congrArg VExpr.sort kind)⟩

theorem Annotation.function_conversion (annotation : Annotation) (setup : AliasSetup env)
    (library : Signatures env)
    (resultTyped : DirectTyping env 0 (annotation.core::ctx) (optionType valueType) (.sort (.succ .zero)))
    (resultFresh : ∀ r ∈ setup.rules, ``Option ≠ r.name) :
    ∃ result, setup.conversion 0 ctx (.forallE annotation.core (optionType valueType))
      (.forallE wordType (optionType valueType)) = some result := by
  have resultNone := setup.basic_no_reduction (U := 0) (ctx := annotation.core::ctx) (optionType valueType) (optionType valueType) rfl rfl
    resultFresh resultFresh rfl
  cases annotation with
  | word =>
    have typed := DirectTyping.forallType (Annotation.type_typed .word library) resultTyped
    obtain ⟨equation,proved,kind⟩ := LeanStructuralConversion.prove_reflexive_complete
      typed (show setup.basic 0 ctx (.forallE wordType (optionType valueType)) (.forallE wordType (optionType valueType)) = none from rfl)
      63 setup.exposure
    exact LeanStructuralConversion.conversion_of_prove equation proved kind
  | bitvec =>
    obtain ⟨domain,domainProved,domainType⟩ := Annotation.domain_proved .bitvec setup library (ctx := ctx)
    obtain ⟨body,bodyProved,bodyType⟩ := LeanStructuralConversion.prove_reflexive_complete
      resultTyped resultNone 62 setup.exposure
    obtain ⟨equation,proved,kind⟩ := LeanStructuralConversion.prove_forall_complete
      (by intro same; cases (VExpr.forallE.inj same).1)
      (show setup.basic 0 ctx (.forallE bitvecType (optionType valueType)) (.forallE wordType (optionType valueType)) = none from rfl)
      domain domainProved domainType body bodyProved bodyType
    exact LeanStructuralConversion.conversion_of_prove equation proved kind

theorem Annotation.continuation_conversion (annotation : Annotation) (setup : AliasSetup env)
    (library : Signatures env) (closed : ClosedConstantTypes env)
    (resultClosed : resultType.ClosedN 0) (notSort : ∀ u, resultType ≠ .sort u)
    (prefixTyped : CastTyping env 0 (SourceCasts env) (annotation.core::ctx)
      (.app (.app (.const ``Eq [.succ .zero]) resultType) lhs)
      (.forallE resultType (.sort .zero)))
    (sourceTyped : CastTyping env 0 (SourceCasts env) (annotation.core::ctx) sourceBody resultType)
    (sourceForm : ValueForm setup (annotation.core::ctx) sourceBody resultType)
    (eqFresh : ∀ r ∈ setup.rules, ``Eq ≠ r.name) :
    ∃ result, setup.conversion 0 ctx
      (.forallE annotation.core (equalValues resultType lhs sourceBody))
      (.forallE wordType (equalValues resultType lhs
        (continuationValue annotation.core sourceBody))) = some result := by
  obtain ⟨domain,proved,kind⟩ := annotation.domain_proved setup library (ctx := ctx)
  exact continuation_beta_conversion_with_domain setup library closed annotation.closed
    resultClosed notSort domain proved kind prefixTyped sourceTyped sourceForm eqFresh

end IRComparison.WordFrontend.WordBinder
