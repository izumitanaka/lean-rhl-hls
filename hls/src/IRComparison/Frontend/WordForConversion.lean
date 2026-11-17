import IRComparison.Frontend.WordRetainedConversion
import IRComparison.Frontend.WordForLibrary
import IRComparison.Frontend.WordScalarConversion
import IRComparison.Frontend.WordAnnotatedCondition
import IRComparison.Frontend.WordPairConversion
import IRComparison.Frontend.WordReadAnnotationConversion
import IRComparison.Frontend.WordReadElementConversion

/-! Concrete conversion coverage for the native two-argument loop
continuation. The only source premise is independent typing and body shape;
no parser or typechecker success is included in the conversion relation. -/
namespace IRComparison.WordFrontend.Certificate.For
open Lean4Lean LeanTyped LeanTypeInference LeanTypeReduction
open Arithmetic (SourceCasts continuation2Value continuation2Value_ne)
set_option maxHeartbeats 1500000

open Step (equalityPrefix equalityPrefix_typed)

theorem equality_beta2_proved (setup : Arithmetic.AliasSetup env) (arithmetic : Arithmetic.Signatures env)
    (signatures : Step.Signatures env) (closed : ClosedConstantTypes env)
    (plainTyped : CastTyping env 0 (SourceCasts env) (stateType::wordType::ctx) plain (optionType stateType))
    (sourceTyped : CastTyping env 0 (SourceCasts env) (stateType::wordType::ctx) original (optionType Step.stepState))
    (sourceForm : Arithmetic.ValueForm setup (stateType::wordType::ctx) original (optionType Step.stepState))
    (eqDeclared : env.constants ``Eq = some eqSignature)
    (eqFresh : ∀ r ∈ setup.rules, ``Eq ≠ r.name) (fuel : Nat) :
    ∃ equation, LeanStructuralConversion.prove env setup.basic setup.exposure 0 (fuel+6) (stateType::wordType::ctx)
      (Step.expected plain original) (Step.expected plain (continuation2Value wordType stateType original)) = some equation ∧
      equation.type = .sort .zero := by
  have prefixTyped := equalityPrefix_typed signatures eqDeclared plainTyped
  have prefixNone : setup.basic 0 (stateType::wordType::ctx) (equalityPrefix plain) (equalityPrefix plain) = none :=
    setup.basic_no_reduction _ _ rfl rfl eqFresh eqFresh rfl
  obtain ⟨fn,fnProved,fnType⟩ := LeanStructuralConversion.prove_reflexive_cast_complete prefixTyped prefixNone
    (setup.covers_source_recursive arithmetic closed fuel)
  have stateTyped : DirectTyping env 0 ctx stateType (.sort (.succ .zero)) :=
    .constant signatures.state (by simp) rfl
  obtain ⟨right,rightProved,rightType⟩ := setup.value_beta2_proved arithmetic closed (by trivial) (by trivial)
    stateTyped (by trivial) (by intro u; simp [optionType]) sourceTyped sourceForm fuel
  have wholeNone : setup.basic 0 (stateType::wordType::ctx) (Step.expected plain original)
      (Step.expected plain (continuation2Value wordType stateType original)) = none :=
    setup.basic_no_reduction _ _ rfl rfl eqFresh eqFresh rfl
  exact LeanStructuralConversion.prove_application_complete
    (leftName := ``Eq) (rightName := ``Eq) rfl rfl
    (fun same => continuation2Value_ne wordType stateType original (VExpr.app.inj same).2)
    wholeNone fn fnProved fnType right rightProved rightType

theorem continuation_beta_conversion (setup : Arithmetic.AliasSetup env) (arithmetic : Arithmetic.Signatures env)
    (signatures : Step.Signatures env) (closed : ClosedConstantTypes env)
    (inputs : InputsTyped env ctx p)
    (codeTyped : CastTyping env 0 (SourceCasts env) ctx code cmdType) (codeClosed : code.ClosedN 0)
    (sourceTyped : CastTyping env 0 (SourceCasts env) (stateType::wordType::ctx) original (optionType Step.stepState))
    (sourceForm : Arithmetic.ValueForm setup (stateType::wordType::ctx) original (optionType Step.stepState))
    (consDeclared : env.constants ``List.cons = some consSignature)
    (eqDeclared : env.constants ``Eq = some eqSignature)
    (evalDeclared : env.constants ``HybridWord.Cmd.eval = some ⟨0,evalSignature⟩)
    (stateFresh : ∀ r ∈ setup.rules, ``HybridWord.State ≠ r.name)
    (eqFresh : ∀ r ∈ setup.rules, ``Eq ≠ r.name) :
    ∃ result, setup.conversion 0 ctx (actualPremise inputs code original)
      (continuationType inputs code (.lam wordType (.lam stateType original))) = some result := by
  have targetTyped : CastTyping env 0 (SourceCasts env) (stateType::wordType::ctx) code cmdType :=
    codeTyped.closed_context SourceCasts.closed codeClosed _
  have evaluation := eval_cast_typed (nextInputs inputs closed arithmetic.word consDeclared) evalDeclared targetTyped
  obtain ⟨eq,eqProved,eqType⟩ := equality_beta2_proved setup arithmetic signatures closed evaluation
    sourceTyped sourceForm eqDeclared eqFresh 56
  have stateTyped : DirectTyping env 0 (wordType::ctx) stateType (.sort (.succ .zero)) :=
    .constant signatures.state (by simp) rfl
  have stateNone : setup.basic 0 (wordType::ctx) stateType stateType = none :=
    setup.basic_no_reduction _ _ rfl rfl stateFresh stateFresh rfl
  obtain ⟨stateEq,stateProved,stateTypeEq⟩ := LeanStructuralConversion.prove_reflexive_complete stateTyped stateNone 61 setup.exposure
  have pointwiseDifferent :
      VExpr.forallE stateType (Step.expected
        (bodyValue (nextInputs inputs closed arithmetic.word consDeclared).i.val
          (nextInputs inputs closed arithmetic.word consDeclared).x.val
          (nextInputs inputs closed arithmetic.word consDeclared).y.val code
          (nextInputs inputs closed arithmetic.word consDeclared).s.val
          (nextInputs inputs closed arithmetic.word consDeclared).ls.val) original) ≠
      .forallE stateType (Step.expected
        (bodyValue (nextInputs inputs closed arithmetic.word consDeclared).i.val
          (nextInputs inputs closed arithmetic.word consDeclared).x.val
          (nextInputs inputs closed arithmetic.word consDeclared).y.val code
          (nextInputs inputs closed arithmetic.word consDeclared).s.val
          (nextInputs inputs closed arithmetic.word consDeclared).ls.val)
        (continuation2Value wordType stateType original)) := by
    intro same
    exact continuation2Value_ne _ _ _ (VExpr.app.inj (VExpr.forallE.inj same).2).2
  obtain ⟨pointwise,pointwiseProved,pointwiseType⟩ := LeanStructuralConversion.prove_forall_complete
    pointwiseDifferent (by rfl) stateEq stateProved stateTypeEq eq eqProved eqType
  have wordTyped : DirectTyping env 0 ctx wordType (.sort (.succ .zero)) := .constant arithmetic.word (by simp) rfl
  obtain ⟨wordEq,wordProved,wordTypeEq⟩ := LeanStructuralConversion.prove_reflexive_complete wordTyped setup.basic_word_refl_none 62 setup.exposure
  have unequal : actualPremise inputs code original ≠
      continuationType inputs code (.lam wordType (.lam stateType original)) := by
    intro same
    apply continuation2Value_ne wordType stateType original
    have h := (VExpr.app.inj (VExpr.forallE.inj (VExpr.forallE.inj same).2).2).2
    simpa only [continuation2Value,VExpr.lift,VExpr.liftN,wordType,stateType,VExpr.liftN'_liftN_hi] using h
  have baseNone : setup.basic 0 ctx (actualPremise inputs code original)
      (continuationType inputs code (.lam wordType (.lam stateType original))) = none := rfl
  have normalized : continuationType inputs code (.lam wordType (.lam stateType original)) =
      .forallE wordType (.forallE stateType
        (Step.expected
          (bodyValue inputs.i.val.lift.lift inputs.x.val.lift.lift inputs.y.val.lift.lift code (.bvar 0)
            (applications (.const ``List.cons [.zero]) [wordType,.bvar 1,inputs.ls.val.lift.lift]))
          (continuation2Value wordType stateType original))) := by
    simp only [continuationType,continuation2Value,VExpr.lift,VExpr.liftN,wordType,stateType,
      codeClosed.liftN_eq (Nat.zero_le _),VExpr.liftN'_liftN_hi]
  rw [normalized] at unequal baseNone ⊢
  obtain ⟨equation,proved,kind⟩ := LeanStructuralConversion.prove_forall_complete unequal baseNone
    wordEq wordProved wordTypeEq pointwise
    (by simpa only [nextInputs,InputsTyped.nextWord,InputsTyped.nextState,InputsTyped.lift,
      VExpr.lift,VExpr.liftN,applications,wordType,stateType] using pointwiseProved) pointwiseType
  exact LeanStructuralConversion.conversion_of_prove equation proved kind

/-- Unit continuations inserted by Lean's do elaboration retain the same
scope in the command semantics. Both result modes share this conversion. -/
def unitResult (isStep : Bool) : VExpr := if isStep then Step.stepState else stateType

def unitEquation (isStep : Bool) (plain source : VExpr) : VExpr :=
  if isStep then Step.expected plain source else equalValues (optionType stateType) plain source

def unitActual (isStep : Bool) (plain source : VExpr) : VExpr :=
  .forallE UnitStep.unitType (unitEquation isStep plain source)

def unitRequired (isStep : Bool) (plain source : VExpr) : VExpr :=
  .forallE UnitStep.unitType (unitEquation isStep plain (Arithmetic.continuationValue UnitStep.unitType source))

theorem unit_beta_conversion (setup : Arithmetic.AliasSetup env) (arithmetic : Arithmetic.Signatures env)
    (signatures : Step.Signatures env) (closed : ClosedConstantTypes env)
    (units : UnitStep.Signatures env) (isStep : Bool)
    (plainTyped : CastTyping env 0 (SourceCasts env) (UnitStep.unitType::ctx) plain (optionType stateType))
    (sourceTyped : CastTyping env 0 (SourceCasts env) (UnitStep.unitType::ctx) original (optionType (unitResult isStep)))
    (sourceForm : Arithmetic.ValueForm setup (UnitStep.unitType::ctx) original (optionType (unitResult isStep)))
    (eqDeclared : env.constants ``Eq = some eqSignature)
    (eqFresh : ∀ r ∈ setup.rules, ``Eq ≠ r.name)
    (unitFresh : ∀ r ∈ setup.rules, ``PUnit ≠ r.name) :
    ∃ result, setup.conversion 0 ctx (unitActual isStep plain original)
      (unitRequired isStep plain original) = some result := by
  have domainNone : setup.basic 0 ctx UnitStep.unitType UnitStep.unitType = none :=
    setup.basic_no_reduction _ _ rfl rfl unitFresh unitFresh rfl
  cases isStep with
  | true =>
    exact Step.direct_beta_conversion_domain setup arithmetic signatures closed units.type_typed
      (by trivial) domainNone plainTyped sourceTyped sourceForm eqDeclared eqFresh
  | false =>
    have prefixTyped :=  CastTyping.application
      ((equality_head_typed (ctx := UnitStep.unitType::ctx) signatures.state signatures.option eqDeclared).withCasts
        (SourceCasts env)) plainTyped
    simp only [WordFrontend.optionState,stateType,VExpr.inst] at prefixTyped
    exact Certificate.continuation_beta_conversion setup arithmetic closed units.type_typed
      (by trivial) domainNone prefixTyped sourceTyped sourceForm eqFresh

/-- The equality surrounding a source call is independent of how its
argument types were obtained. Both exact and convertible spines use this
single congruence proof. The reduction premise is internal to these wrappers. -/
private theorem helper_equality_from_value {resultType lhs normalized source : VExpr}
    (setup : Arithmetic.AliasSetup env) (arithmetic : Arithmetic.Signatures env)
    (closed : ClosedConstantTypes env)
    (prefixTyped : CastTyping env 0 (SourceCasts env) ctx
      (.app (.app (.const ``Eq [.succ .zero]) resultType) lhs)
      (.forallE resultType (.sort .zero)))
    (normalizedTyped : CastTyping env 0 (SourceCasts env) ctx normalized resultType)
    (eqFresh : ∀ r ∈ setup.rules, ``Eq ≠ r.name)
    (valueProof : ∃ equation, LeanStructuralConversion.prove env setup.basic setup.exposure 0 63 ctx
      normalized source = some equation ∧ equation.type = resultType) :
    ∃ result, setup.conversion 0 ctx (equalValues resultType lhs normalized)
      (equalValues resultType lhs source) = some result := by
  have wholeNone := setup.basic_no_reduction (U := 0) (ctx := ctx)
    (equalValues resultType lhs normalized) (equalValues resultType lhs source)
    rfl rfl eqFresh eqFresh rfl
  by_cases same : normalized = source
  · rw [← same] at wholeNone ⊢
    obtain ⟨equation,proved,kind⟩ := LeanStructuralConversion.prove_reflexive_cast_complete
      (CastTyping.application prefixTyped normalizedTyped) wholeNone
      (setup.covers_source_recursive arithmetic closed 59)
    exact LeanStructuralConversion.conversion_of_prove equation proved kind
  · have prefixNone := setup.basic_no_reduction (U := 0) (ctx := ctx)
      (.app (.app (.const ``Eq [.succ .zero]) resultType) lhs)
      (.app (.app (.const ``Eq [.succ .zero]) resultType) lhs) rfl rfl eqFresh eqFresh rfl
    obtain ⟨fn,fnProved,fnType⟩ := LeanStructuralConversion.prove_reflexive_cast_complete
      prefixTyped prefixNone (setup.covers_source_recursive arithmetic closed 58)
    obtain ⟨value,valueProved,valueType⟩ := valueProof
    obtain ⟨equation,proved,kind⟩ := LeanStructuralConversion.prove_application_complete
      (leftName := ``Eq) (rightName := ``Eq) rfl rfl
      (fun h => same (VExpr.app.inj h).2) wholeNone fn fnProved fnType value valueProved valueType
    exact LeanStructuralConversion.conversion_of_prove equation proved kind

theorem helper_equality_conversion {body resultType domain bodyType arg lhs : VExpr} {args : List VExpr} (setup : Arithmetic.AliasSetup env)
    (arithmetic : Arithmetic.Signatures env) (closed : ClosedConstantTypes env)
    (prefixTyped : CastTyping env 0 (SourceCasts env) ctx
      (.app (.app (.const ``Eq [.succ .zero]) resultType) lhs)
      (.forallE resultType (.sort .zero)))
    (bodyTyped : CastTyping env 0 (SourceCasts env) (domain::ctx) body bodyType)
    (argument : CastTyping env 0 (SourceCasts env) ctx arg domain)
    (arguments : ArgumentsCasts env 0 (SourceCasts env) ctx (bodyType.inst arg) args resultType)
    (normalizedTyped : CastTyping env 0 (SourceCasts env) ctx
      (args.foldl applyReduced (body.inst arg)) resultType)
    (form : Arithmetic.ValueForm setup ctx (args.foldl applyReduced (body.inst arg)) resultType)
    (notSort : ∀ u, resultType ≠ .sort u)
    (eqFresh : ∀ r ∈ setup.rules, ``Eq ≠ r.name) :
    ∃ result, setup.conversion 0 ctx
      (equalValues resultType lhs (args.foldl applyReduced (body.inst arg)))
      (equalValues resultType lhs (applications (.app (.lam domain body) arg) args)) = some result := by
  exact helper_equality_from_value setup arithmetic closed prefixTyped normalizedTyped eqFresh
    (setup.helper_proved arithmetic closed bodyTyped argument arguments form notSort 58)

theorem helper_checked_equality_conversion {body resultType domain arg lhs : VExpr} {args domains : List VExpr} (setup : Arithmetic.AliasSetup env)
    (arithmetic : Arithmetic.Signatures env) (closed : ClosedConstantTypes env)
    (prefixTyped : CastTyping env 0 (SourceCasts env) ctx
      (.app (.app (.const ``Eq [.succ .zero]) resultType) lhs)
      (.forallE resultType (.sort .zero)))
    (bodyTyped : CastTyping env 0 (SourceCasts env) (domain::ctx) body (domains.foldr VExpr.forallE resultType))
    (argument : CheckedTyping env 0 (SourceCasts env) ctx arg domain)
    (arguments : List.Forall₂ (fun domain arg =>
      CheckedTyping env 0 (SourceCasts env) ctx arg domain) domains args)
    (typesClosed : ∀ n, ((domains.drop n).foldr VExpr.forallE resultType).ClosedN 0)
    (prefixTypes : ∀ before after, args = before ++ after → after ≠ [] →
      CastTyping env 0 (SourceCasts env) ctx (before.foldl applyReduced (body.inst arg))
        ((domains.drop before.length).foldr VExpr.forallE resultType))
    (normalizedTyped : CastTyping env 0 (SourceCasts env) ctx
      (args.foldl applyReduced (body.inst arg)) resultType)
    (form : Arithmetic.ValueForm setup ctx (args.foldl applyReduced (body.inst arg)) resultType)
    (notSort : ∀ u, resultType ≠ .sort u)
    (eqFresh : ∀ r ∈ setup.rules, ``Eq ≠ r.name) :
    ∃ result, setup.conversion 0 ctx
      (equalValues resultType lhs (args.foldl applyReduced (body.inst arg)))
      (equalValues resultType lhs (applications (.app (.lam domain body) arg) args)) = some result := by
  exact helper_equality_from_value setup arithmetic closed prefixTyped normalizedTyped eqFresh
    (setup.helper_checked_proved arithmetic closed bodyTyped argument arguments typesClosed prefixTypes normalizedTyped form notSort 58)


inductive Casts (setup : Arithmetic.AliasSetup env) : TypeCasts where
  | condition (cast : AnnotatedCondition.Casts setup ctx actual required) : Casts setup ctx actual required
  | annotatedChoice (premises : AnnotatedCondition.ChoiceConditions setup ctx ty v d a b lhs annotation) :
      Casts setup ctx (equalValues ty lhs (AnnotatedCondition.choice ty .word v d a b))
        (equalValues ty lhs (AnnotatedCondition.choice ty annotation v d a b))
  | retainedEquality {body resultType domain arg lhs left : VExpr} {args domains : List VExpr}
      (prefixTyped : CastTyping env 0 (SourceCasts env) ctx
        (.app (.app (.const ``Eq [.succ .zero]) resultType) lhs)
        (.forallE resultType (.sort .zero)))
      (bodyTyped : CastTyping env 0 (SourceCasts env) (domain::ctx) body (domains.foldr VExpr.forallE resultType))
      (argument : CheckedTyping env 0 (SourceCasts env) ctx arg domain)
      (arguments : List.Forall₂ (fun domain arg => CheckedTyping env 0 (SourceCasts env) ctx arg domain) domains args)
      (typesClosed : ∀ n, ((domains.drop n).foldr VExpr.forallE resultType).ClosedN 0)
      (prefixTypes : ∀ before after, args = before ++ after → after ≠ [] →
        CastTyping env 0 (SourceCasts env) ctx (before.foldl applyReduced (body.inst arg))
          ((domains.drop before.length).foldr VExpr.forallE resultType))
      (chain : RetainedConversion.Prefix env 0 (SourceCasts env) resultType ctx left
        (args.foldl applyReduced (body.inst arg)) count)
      (resultClosed : resultType.ClosedN 0) :
      Casts setup ctx (equalValues resultType lhs left)
        (equalValues resultType lhs (applications (.app (.lam domain body) arg) args))
  | helperEquality {body resultType domain bodyType arg lhs : VExpr} {args : List VExpr}
      (prefixTyped : CastTyping env 0 (SourceCasts env) ctx
        (.app (.app (.const ``Eq [.succ .zero]) resultType) lhs)
        (.forallE resultType (.sort .zero)))
      (bodyTyped : CastTyping env 0 (SourceCasts env) (domain::ctx) body bodyType)
      (argument : CastTyping env 0 (SourceCasts env) ctx arg domain)
      (arguments : ArgumentsCasts env 0 (SourceCasts env) ctx (bodyType.inst arg) args resultType)
      (normalizedTyped : CastTyping env 0 (SourceCasts env) ctx
        (args.foldl applyReduced (body.inst arg)) resultType)
      (form : Arithmetic.ValueForm setup ctx (args.foldl applyReduced (body.inst arg)) resultType)
      (notSort : ∀ u, resultType ≠ .sort u) :
      Casts setup ctx (equalValues resultType lhs (args.foldl applyReduced (body.inst arg)))
        (equalValues resultType lhs (applications (.app (.lam domain body) arg) args))
  | helperCheckedEquality {body resultType domain arg lhs : VExpr} {args domains : List VExpr}
      (prefixTyped : CastTyping env 0 (SourceCasts env) ctx
        (.app (.app (.const ``Eq [.succ .zero]) resultType) lhs)
        (.forallE resultType (.sort .zero)))
      (bodyTyped : CastTyping env 0 (SourceCasts env) (domain::ctx) body (domains.foldr VExpr.forallE resultType))
      (argument : CheckedTyping env 0 (SourceCasts env) ctx arg domain)
      (arguments : List.Forall₂ (fun domain arg =>
        CheckedTyping env 0 (SourceCasts env) ctx arg domain) domains args)
      (typesClosed : ∀ n, ((domains.drop n).foldr VExpr.forallE resultType).ClosedN 0)
      (prefixTypes : ∀ before after, args = before ++ after → after ≠ [] →
        CastTyping env 0 (SourceCasts env) ctx (before.foldl applyReduced (body.inst arg))
          ((domains.drop before.length).foldr VExpr.forallE resultType))
      (normalizedTyped : CastTyping env 0 (SourceCasts env) ctx
        (args.foldl applyReduced (body.inst arg)) resultType)
      (form : Arithmetic.ValueForm setup ctx (args.foldl applyReduced (body.inst arg)) resultType)
      (notSort : ∀ u, resultType ≠ .sort u) :
      Casts setup ctx (equalValues resultType lhs (args.foldl applyReduced (body.inst arg)))
        (equalValues resultType lhs (applications (.app (.lam domain body) arg) args))
  | readElementEquality
      (library : Read.Signatures env)
      (getterFresh : ∀ r ∈ setup.rules, ``GetElem?.getElem? ≠ r.name)
      (instanceFresh : ∀ r ∈ setup.rules, ``Array.instGetElem?NatLtSize ≠ r.name)
      (prefixTyped : CastTyping env 0 (SourceCasts env) ctx
        (.app (.app (.const ``Eq [.succ .zero]) (optionType wordType)) lhs)
        (.forallE (optionType wordType) (.sort .zero)))
      (arrayTyped : DirectTyping env 0 ctx arr Read.arrayType)
      (arrayForm : Arithmetic.ValueForm setup ctx arr Read.arrayType)
      (indexTyped : CastTyping env 0 (SourceCasts env) ctx index Arithmetic.natType)
      (indexForm : Arithmetic.ValueForm setup ctx index Arithmetic.natType) :
      Casts setup ctx (equalValues (optionType wordType) lhs (.app (.app Read.header arr) index))
        (equalValues (optionType wordType) lhs (Read.bitsSourceCore arr index))
  | annotatedReadEquality {body resultType : VExpr}
      (library : BindSignatures env)
      (resultTyped : ∀ ctx, DirectTyping env 0 ctx resultType (.sort (.succ .zero)))
      (resultClosed : resultType.ClosedN 0)
      (resultHead : LeanTypeReduction.constantHead resultType = some (resultName,resultLevels))
      (resultFresh : ∀ r ∈ setup.rules, resultName ≠ r.name)
      (resultBase : setup.base 0 ctx resultType resultType = none)
      (bindFresh : ∀ r ∈ setup.rules, ``Bind.bind ≠ r.name)
      (prefixTyped : CastTyping env 0 (SourceCasts env) ctx
        (.app (.app (.const ``Eq [.succ .zero]) (optionType resultType)) lhs)
        (.forallE (optionType resultType) (.sort .zero)))
      (firstTyped : CheckedTyping env 0 (SourceCasts env) ctx first (optionType wordType))
      (firstForm : Arithmetic.ValueForm setup ctx first (optionType wordType))
      (bodyTyped : CastTyping env 0 (SourceCasts env) (Arithmetic.bitvecType::ctx) body (optionType resultType)) :
      Casts setup ctx
        (equalValues (optionType resultType) lhs (WordBinder.bindValueAnnotated wordType first (.lam Arithmetic.bitvecType body) resultType))
        (equalValues (optionType resultType) lhs (WordBinder.bindValueAnnotated Arithmetic.bitvecType first (.lam Arithmetic.bitvecType body) resultType))
  | annotatedFunction (annotation : WordBinder.Annotation)
      (resultTyped : DirectTyping env 0 (annotation.core::ctx) (optionType valueType) (.sort (.succ .zero)))
      (optionFresh : ∀ r ∈ setup.rules, ``Option ≠ r.name) :
      Casts setup ctx (.forallE annotation.core (optionType valueType))
        (.forallE wordType (optionType valueType))
  | annotatedContinuation {resultType : VExpr} (annotation : WordBinder.Annotation)
      (resultClosed : resultType.ClosedN 0) (notSort : ∀ u, resultType ≠ .sort u)
      (prefixTyped : CastTyping env 0 (SourceCasts env) (annotation.core::ctx)
        (.app (.app (.const ``Eq [.succ .zero]) resultType) lhs)
        (.forallE resultType (.sort .zero)))
      (sourceTyped : CastTyping env 0 (SourceCasts env) (annotation.core::ctx) original resultType)
      (sourceForm : Arithmetic.ValueForm setup (annotation.core::ctx) original resultType) :
      Casts setup ctx (.forallE annotation.core (equalValues resultType lhs original))
        (.forallE wordType (equalValues resultType lhs (Arithmetic.continuationValue annotation.core original)))

  | pair (first second : Lean.Name)
      (firstDeclared : env.constants first = some ⟨0,.sort (.succ .zero)⟩)
      (secondDeclared : env.constants second = some ⟨0,.sort (.succ .zero)⟩)
      (firstFresh : ∀ r ∈ setup.rules, first ≠ r.name)
      (secondFresh : ∀ r ∈ setup.rules, second ≠ r.name)
      (tyTyped : DirectTyping env 0 (.const second []::.const first []::ctx) ty (.sort (.succ .zero)))
      (tyClosed : ty.ClosedN 0) (notSort : ∀ u, ty ≠ .sort u)
      (lhsTyped : CastTyping env 0 (SourceCasts env) (.const second []::.const first []::ctx) lhs ty)
      (rhsTyped : CastTyping env 0 (SourceCasts env) (.const second []::.const first []::ctx) rhs ty)
      (rhsForm : Arithmetic.ValueForm setup (.const second []::.const first []::ctx) rhs ty) :
      Casts setup ctx (Pair.actual (.const first []) (.const second []) ty lhs rhs)
        (Pair.required (.const first []) (.const second []) ty lhs rhs)
  | scalar (library : ScalarConversion.Signatures env)
      (freshSome : ∀ r ∈ setup.rules, ``Option.some ≠ r.name)
      (cast : ScalarConversion.Casts setup ctx actual required) : Casts setup ctx actual required
  | base {actual required : VExpr} : Step.NormalizationCasts setup ctx actual required → Casts setup ctx actual required
  | continuation (inputs : InputsTyped env ctx p)
      (codeTyped : CastTyping env 0 (SourceCasts env) ctx code cmdType)
      (codeClosed : code.ClosedN 0)
      (sourceTyped : CastTyping env 0 (SourceCasts env) (stateType::wordType::ctx) original (optionType Step.stepState))
      (sourceForm : Arithmetic.ValueForm setup (stateType::wordType::ctx) original (optionType Step.stepState)) :
      Casts setup ctx (actualPremise inputs code original)
        (continuationType inputs code (.lam wordType (.lam stateType original)))
  | directContinuation (binder : Step.Binder)
      (plainTyped : CastTyping env 0 (SourceCasts env) (binder.core::ctx) plain (optionType stateType))
      (sourceTyped : CastTyping env 0 (SourceCasts env) (binder.core::ctx) original (optionType Step.stepState))
      (sourceForm : Arithmetic.ValueForm setup (binder.core::ctx) original (optionType Step.stepState)) :
      Casts setup ctx (.forallE binder.core (Step.expected plain original))
        (.forallE binder.core (Step.expected plain (Arithmetic.continuationValue binder.core original)))
  | unitContinuation (units : UnitStep.Signatures env) (isStep : Bool)
      (plainTyped : CastTyping env 0 (SourceCasts env) (UnitStep.unitType::ctx) plain (optionType stateType))
      (sourceTyped : CastTyping env 0 (SourceCasts env) (UnitStep.unitType::ctx) original (optionType (unitResult isStep)))
      (sourceForm : Arithmetic.ValueForm setup (UnitStep.unitType::ctx) original (optionType (unitResult isStep)))
      (unitFresh : ∀ r ∈ setup.rules, ``PUnit ≠ r.name) :
      Casts setup ctx (unitActual isStep plain original) (unitRequired isStep plain original)

instance : Arithmetic.Includes (Casts setup) := ⟨fun _ _ _ h => .base (.base (.source (.arithmetic h)))⟩

theorem Casts.covered (setup : Arithmetic.AliasSetup env) (arithmetic : Arithmetic.Signatures env)
    (signatures : Step.Signatures env) (closed : ClosedConstantTypes env)
    (consDeclared : env.constants ``List.cons = some consSignature)
    (eqDeclared : env.constants ``Eq = some eqSignature)
    (evalDeclared : env.constants ``HybridWord.Cmd.eval = some ⟨0,evalSignature⟩)
    (stateFresh : ∀ r ∈ setup.rules, ``HybridWord.State ≠ r.name)
    (eqFresh : ∀ r ∈ setup.rules, ``Eq ≠ r.name)
    (liftFresh : ∀ r ∈ setup.rules, ``WordLoopFacts.lift ≠ r.name) :
    Conversion.Covers setup.conversion 0 (Casts setup) := by
  intro ctx actual required cast
  cases cast with
  | condition h => exact AnnotatedCondition.Casts.covered_top setup arithmetic closed ctx actual required h
  | annotatedChoice premises => exact premises.conversion arithmetic closed
  | retainedEquality prefixTyped bodyTyped argument arguments typesClosed prefixTypes chain resultClosed =>
    obtain ⟨result,success⟩ := RetainedConversion.conversion_checked_call
      bodyTyped argument arguments typesClosed prefixTypes chain closed SourceCasts.closed resultClosed
      prefixTyped (by rfl) (setup.covers_source_ordinary arithmetic closed) setup.exposure chain.length_le
    exact LeanStructuralConversion.conversion_of_retained
      (by simpa only [RetainedConversion.automatic,equalValues] using success)
  | helperEquality prefixTyped bodyTyped argument arguments normalizedTyped form notSort =>
    exact helper_equality_conversion setup arithmetic closed prefixTyped bodyTyped argument
      arguments normalizedTyped form notSort eqFresh
  | helperCheckedEquality prefixTyped bodyTyped argument arguments typesClosed prefixTypes normalizedTyped form notSort =>
    exact helper_checked_equality_conversion setup arithmetic closed prefixTyped bodyTyped argument
      arguments typesClosed prefixTypes normalizedTyped form notSort eqFresh
  | readElementEquality library getterFresh instanceFresh prefixTyped arrayTyped arrayForm indexTyped indexForm =>
    exact Read.element_equality_conversion setup arithmetic library closed getterFresh instanceFresh eqFresh
      prefixTyped arrayTyped arrayForm indexTyped indexForm
  | annotatedReadEquality library resultTyped resultClosed resultHead resultFresh resultBase bindFresh prefixTyped firstTyped firstForm bodyTyped =>
    exact WordBinder.bind_equality_conversion setup arithmetic library closed resultTyped resultClosed
      resultHead resultFresh resultBase bindFresh eqFresh prefixTyped firstTyped firstForm bodyTyped
  | annotatedFunction annotation resultTyped optionFresh =>
    exact annotation.function_conversion setup arithmetic resultTyped optionFresh
  | annotatedContinuation annotation resultClosed notSort prefixTyped sourceTyped sourceForm =>
    exact annotation.continuation_conversion setup arithmetic closed resultClosed notSort
      prefixTyped sourceTyped sourceForm eqFresh

  | pair first second firstDeclared secondDeclared firstFresh secondFresh
      tyTyped tyClosed notSort lhsTyped rhsTyped rhsForm =>
    exact Pair.conversion setup arithmetic closed first second firstDeclared secondDeclared
      firstFresh secondFresh tyTyped tyClosed notSort lhsTyped rhsTyped rhsForm eqDeclared eqFresh
  | scalar library freshSome cast =>
    exact ScalarConversion.Casts.covered setup arithmetic library closed eqFresh freshSome ctx actual required cast
  | base cast =>
    exact Step.NormalizationCasts.covered setup arithmetic signatures closed consDeclared eqDeclared
      evalDeclared stateFresh eqFresh liftFresh ctx actual required cast
  | continuation inputs codeTyped codeClosed sourceTyped sourceForm =>
    exact continuation_beta_conversion setup arithmetic signatures closed inputs codeTyped codeClosed
      sourceTyped sourceForm consDeclared eqDeclared evalDeclared stateFresh eqFresh
  | directContinuation binder plainTyped sourceTyped sourceForm =>
    exact Step.direct_beta_conversion setup arithmetic signatures closed binder plainTyped sourceTyped sourceForm
      eqDeclared stateFresh eqFresh
  | unitContinuation units isStep plainTyped sourceTyped sourceForm unitFresh =>
    exact unit_beta_conversion setup arithmetic signatures closed units isStep plainTyped sourceTyped sourceForm
      eqDeclared eqFresh unitFresh

end IRComparison.WordFrontend.Certificate.For
