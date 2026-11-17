import IRComparison.Frontend.WordUnitConversion

/-! The concrete beta conversions needed when a normalized loop body is
abstracted over its next Word/State value. The normalization certificate is
composed once; no input-specific conversion is trusted. -/
namespace IRComparison.WordFrontend.Certificate.Step
open Lean4Lean LeanTyped LeanTypeInference LeanTypeReduction
open Arithmetic (SourceCasts continuationValue continuationValue_ne)
set_option maxHeartbeats 1000000

theorem lift_beta_proved (setup : Arithmetic.AliasSetup env) (arithmetic : Arithmetic.Signatures env)
    (closed : ClosedConstantTypes env) (domainClosed : domain.ClosedN 0)
    (plainTyped : CastTyping env 0 (SourceCasts env) (domain::ctx) plain (optionType stateType))
    (plainForm : Arithmetic.ValueForm setup (domain::ctx) plain (optionType stateType))
    (liftDeclared : env.constants ``WordLoopFacts.lift = some ⟨0,liftSignature⟩)
    (liftFresh : ∀ r ∈ setup.rules, ``WordLoopFacts.lift ≠ r.name) (fuel : Nat) :
    ∃ equation, LeanStructuralConversion.prove env setup.basic setup.exposure 0 (fuel+6) (domain::ctx)
      (lifted plain) (lifted (continuationValue domain plain)) = some equation ∧
      equation.type = optionType stepState := by
  have functionTyped : DirectTyping env 0 (domain::ctx) (.const ``WordLoopFacts.lift []) liftSignature :=
    .constant liftDeclared (by simp) rfl
  have functionNone : setup.basic 0 (domain::ctx) (.const ``WordLoopFacts.lift [])
      (.const ``WordLoopFacts.lift []) = none := setup.basic_no_reduction _ _ rfl rfl liftFresh liftFresh rfl
  obtain ⟨fn,fnProved,fnType⟩ := LeanStructuralConversion.prove_reflexive_complete
    functionTyped functionNone (fuel+4) setup.exposure
  obtain ⟨arg,argProved,argType⟩ := setup.value_beta_proved arithmetic closed domainClosed
    (by trivial) (by intro u; simp [optionType,stateType]) plainTyped plainForm fuel
  have wholeNone : setup.basic 0 (domain::ctx) (lifted plain) (lifted (continuationValue domain plain)) = none :=
    setup.basic_no_reduction _ _ rfl rfl liftFresh liftFresh rfl
  obtain ⟨equation,proved,kind⟩ := LeanStructuralConversion.prove_application_complete
    (leftName := ``WordLoopFacts.lift) (rightName := ``WordLoopFacts.lift) rfl rfl
    (fun same => continuationValue_ne domain plain (VExpr.app.inj same).2) wholeNone
    fn fnProved fnType arg argProved argType
  exact ⟨equation,proved,kind⟩

theorem equality_betas_proved (setup : Arithmetic.AliasSetup env) (arithmetic : Arithmetic.Signatures env)
    (signatures : Signatures env) (closed : ClosedConstantTypes env) (domainClosed : domain.ClosedN 0)
    (plainTyped : CastTyping env 0 (SourceCasts env) (domain::ctx) plain (optionType stateType))
    (sourceTyped : CastTyping env 0 (SourceCasts env) (domain::ctx) original (optionType stepState))
    (plainForm : Arithmetic.ValueForm setup (domain::ctx) plain (optionType stateType))
    (sourceForm : Arithmetic.ValueForm setup (domain::ctx) original (optionType stepState))
    (eqDeclared : env.constants ``Eq = some eqSignature)
    (eqFresh : ∀ r ∈ setup.rules, ``Eq ≠ r.name)
    (liftFresh : ∀ r ∈ setup.rules, ``WordLoopFacts.lift ≠ r.name) (fuel : Nat) :
    ∃ equation, LeanStructuralConversion.prove env setup.basic setup.exposure 0 (fuel+8) (domain::ctx)
      (expected plain original) (expected (continuationValue domain plain) (continuationValue domain original)) = some equation ∧
      equation.type = .sort .zero := by
  have optionTyped : DirectTyping env 0 (domain::ctx) (.const ``Option [.zero])
      (.forallE (.sort (.succ .zero)) (.sort (.succ .zero))) :=
    .constant signatures.option (by simp [VLevel.WF]) rfl
  have eqTyped : DirectTyping env 0 (domain::ctx) (.const ``Eq [.succ .zero]) (eqSignature.type.instL [.succ .zero]) :=
    .constant eqDeclared (by simp [VLevel.WF]) rfl
  have eqHead := DirectTyping.application eqTyped (DirectTyping.application optionTyped signatures.step_typed)
  simp only [eqSignature,VExpr.instL,VLevel.inst,VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,
    VExpr.instVar_lower,Nat.reduceAdd,VExpr.lift,VExpr.liftN,optionType,stepState,stateType,List.map_nil] at eqHead
  have headNone : setup.basic 0 (domain::ctx) (.app (.const ``Eq [.succ .zero]) (optionType stepState))
      (.app (.const ``Eq [.succ .zero]) (optionType stepState)) = none :=
    setup.basic_no_reduction _ _ rfl rfl eqFresh eqFresh rfl
  obtain ⟨fn,fnProved,fnType⟩ := LeanStructuralConversion.prove_reflexive_complete eqHead headNone (fuel+5) setup.exposure
  obtain ⟨left,leftProved,leftType⟩ := lift_beta_proved setup arithmetic closed domainClosed plainTyped plainForm
    signatures.liftDecl liftFresh fuel
  have prefixNone : setup.basic 0 (domain::ctx)
      (applications (.const ``Eq [.succ .zero]) [optionType stepState,lifted plain])
      (applications (.const ``Eq [.succ .zero]) [optionType stepState,lifted (continuationValue domain plain)]) = none :=
    setup.basic_no_reduction _ _ rfl rfl eqFresh eqFresh rfl
  obtain ⟨prefixEq,prefixProved,prefixType⟩ := LeanStructuralConversion.prove_application_complete
    (leftName := ``Eq) (rightName := ``Eq) rfl rfl
    (fun same => continuationValue_ne domain plain (VExpr.app.inj (VExpr.app.inj same).2).2)
    prefixNone fn fnProved fnType left leftProved leftType
  simp only [optionType,stepState,stateType,VExpr.inst] at prefixType
  obtain ⟨right,rightProved,rightType⟩ := setup.value_beta_proved arithmetic closed domainClosed
    (by trivial) (by intro u; simp [optionType]) sourceTyped sourceForm (fuel+2)
  have wholeNone : setup.basic 0 (domain::ctx) (expected plain original)
      (expected (continuationValue domain plain) (continuationValue domain original)) = none :=
    setup.basic_no_reduction _ _ rfl rfl eqFresh eqFresh rfl
  obtain ⟨equation,proved,kind⟩ := LeanStructuralConversion.prove_application_complete
    (leftName := ``Eq) (rightName := ``Eq) rfl rfl
    (fun same => continuationValue_ne domain original (VExpr.app.inj same).2) wholeNone
    prefixEq prefixProved prefixType right (by simpa only [Nat.add_assoc] using rightProved) rightType
  exact ⟨equation,proved,kind⟩

/-- Both sides of the loop normalization equality receive the same binder.
The installed structural converter has enough fuel for these fixed congruence
layers; source size and loop count do not occur in this bound. -/
theorem bind_beta_conversion (setup : Arithmetic.AliasSetup env) (arithmetic : Arithmetic.Signatures env)
    (signatures : Signatures env) (closed : ClosedConstantTypes env)
    (domainTyped : DirectTyping env 0 ctx domain (.sort (.succ .zero))) (domainClosed : domain.ClosedN 0)
    (domainNone : setup.basic 0 ctx domain domain = none)
    (plainTyped : CastTyping env 0 (SourceCasts env) (domain::ctx) plain (optionType stateType))
    (sourceTyped : CastTyping env 0 (SourceCasts env) (domain::ctx) original (optionType stepState))
    (plainForm : Arithmetic.ValueForm setup (domain::ctx) plain (optionType stateType))
    (sourceForm : Arithmetic.ValueForm setup (domain::ctx) original (optionType stepState))
    (eqDeclared : env.constants ``Eq = some eqSignature)
    (eqFresh : ∀ r ∈ setup.rules, ``Eq ≠ r.name)
    (liftFresh : ∀ r ∈ setup.rules, ``WordLoopFacts.lift ≠ r.name) :
    ∃ result, setup.conversion 0 ctx (.forallE domain (expected plain original))
      (bindPremise domain (.lam domain plain) (.lam domain original)) = some result := by
  obtain ⟨body,bodyProved,bodyType⟩ := equality_betas_proved setup arithmetic signatures closed domainClosed
    plainTyped sourceTyped plainForm sourceForm eqDeclared eqFresh liftFresh 55
  obtain ⟨dom,domProved,domType⟩ := LeanStructuralConversion.prove_reflexive_complete
    domainTyped domainNone 62 setup.exposure
  have unequal : (.forallE domain (expected plain original)) ≠
      bindPremise domain (.lam domain plain) (.lam domain original) := by
    intro same
    apply continuationValue_ne domain original
    have h := (VExpr.app.inj (VExpr.forallE.inj same).2).2
    simpa only [VExpr.lift,VExpr.liftN,domainClosed.liftN_eq (Nat.zero_le _)] using h
  have baseNone : setup.basic 0 ctx (.forallE domain (expected plain original))
      (bindPremise domain (.lam domain plain) (.lam domain original)) = none := rfl
  have targetSame : bindPremise domain (.lam domain plain) (.lam domain original) =
      .forallE domain (expected (continuationValue domain plain) (continuationValue domain original)) := by
    simp only [bindPremise,continuationValue,VExpr.lift,VExpr.liftN,domainClosed.liftN_eq (Nat.zero_le _)]
  rw [targetSame] at unequal baseNone ⊢
  obtain ⟨equation,proved,kind⟩ := LeanStructuralConversion.prove_forall_complete unequal baseNone
    dom domProved domType body bodyProved bodyType
  exact LeanStructuralConversion.conversion_of_prove equation proved kind

/-- Only the two existing monomorphic continuation binders are distinguished.
This is a proof-side index; programs remain ordinary Lean definitions. -/
inductive Binder where | state | word

def Binder.core : Binder → VExpr | .state => stateType | .word => wordType
def Binder.native : Binder → Lean.Expr | .state => WordFrontend.state | .word => WordFrontend.word

theorem Binder.represents (binder : Binder) : Represents binder.native binder.core := by
  cases binder <;> exact .constant rfl

theorem Binder.closed (binder : Binder) : binder.core.ClosedN 0 := by cases binder <;> trivial

theorem Binder.typed (binder : Binder) (signatures : Signatures env) (arithmetic : Arithmetic.Signatures env) :
    DirectTyping env 0 ctx binder.core (.sort (.succ .zero)) := by
  cases binder with
  | state => exact .constant signatures.state (by simp) rfl
  | word => exact .constant arithmetic.word (by simp) rfl

theorem Binder.basic_none (binder : Binder) (setup : Arithmetic.AliasSetup env)
    (stateFresh : ∀ r ∈ setup.rules, ``HybridWord.State ≠ r.name) :
    setup.basic 0 ctx binder.core binder.core = none := by
  cases binder with
  | state => exact setup.basic_no_reduction _ _ rfl rfl stateFresh stateFresh rfl
  | word => exact setup.basic_word_refl_none

/-- Direct command certificates need beta conversion only on the source
side; the command evaluation on the left is already in its final form. -/
theorem direct_equality_beta_proved (setup : Arithmetic.AliasSetup env) (arithmetic : Arithmetic.Signatures env)
    (signatures : Signatures env) (closed : ClosedConstantTypes env) (domainClosed : domain.ClosedN 0)
    (plainTyped : CastTyping env 0 (SourceCasts env) (domain::ctx) plain (optionType stateType))
    (sourceTyped : CastTyping env 0 (SourceCasts env) (domain::ctx) original (optionType stepState))
    (sourceForm : Arithmetic.ValueForm setup (domain::ctx) original (optionType stepState))
    (eqDeclared : env.constants ``Eq = some eqSignature)
    (eqFresh : ∀ r ∈ setup.rules, ``Eq ≠ r.name) (fuel : Nat) :
    ∃ equation, LeanStructuralConversion.prove env setup.basic setup.exposure 0 (fuel+6) (domain::ctx)
      (expected plain original) (expected plain (continuationValue domain original)) = some equation ∧
      equation.type = .sort .zero := by
  have prefixTyped := equalityPrefix_typed signatures eqDeclared plainTyped
  have prefixNone : setup.basic 0 (domain::ctx) (equalityPrefix plain) (equalityPrefix plain) = none :=
    setup.basic_no_reduction _ _ rfl rfl eqFresh eqFresh rfl
  obtain ⟨fn,fnProved,fnType⟩ := LeanStructuralConversion.prove_reflexive_cast_complete prefixTyped prefixNone
    (setup.covers_source_recursive arithmetic closed fuel)
  obtain ⟨right,rightProved,rightType⟩ := setup.value_beta_proved arithmetic closed domainClosed
    (by trivial) (by intro u; simp [optionType]) sourceTyped sourceForm fuel
  have wholeNone : setup.basic 0 (domain::ctx) (expected plain original)
      (expected plain (continuationValue domain original)) = none :=
    setup.basic_no_reduction _ _ rfl rfl eqFresh eqFresh rfl
  exact LeanStructuralConversion.prove_application_complete
    (leftName := ``Eq) (rightName := ``Eq) rfl rfl
    (fun same => continuationValue_ne domain original (VExpr.app.inj same).2)
    wholeNone fn fnProved fnType right rightProved rightType

theorem direct_beta_conversion_domain (setup : Arithmetic.AliasSetup env) (arithmetic : Arithmetic.Signatures env)
    (signatures : Signatures env) (closed : ClosedConstantTypes env)
    (domainTyped : DirectTyping env 0 ctx domain (.sort (.succ .zero)))
    (domainClosed : domain.ClosedN 0)
    (domainNone : setup.basic 0 ctx domain domain = none)
    (plainTyped : CastTyping env 0 (SourceCasts env) (domain::ctx) plain (optionType stateType))
    (sourceTyped : CastTyping env 0 (SourceCasts env) (domain::ctx) original (optionType stepState))
    (sourceForm : Arithmetic.ValueForm setup (domain::ctx) original (optionType stepState))
    (eqDeclared : env.constants ``Eq = some eqSignature)
    (eqFresh : ∀ r ∈ setup.rules, ``Eq ≠ r.name) :
    ∃ result, setup.conversion 0 ctx (.forallE domain (expected plain original))
      (.forallE domain (expected plain (continuationValue domain original))) = some result := by
  obtain ⟨body,bodyProved,bodyType⟩ := direct_equality_beta_proved setup arithmetic signatures closed domainClosed
    plainTyped sourceTyped sourceForm eqDeclared eqFresh 57
  obtain ⟨domainEq,domainProved,domainType⟩ := LeanStructuralConversion.prove_reflexive_complete
    domainTyped domainNone 62 setup.exposure
  have unequal : (VExpr.forallE domain (expected plain original)) ≠
      (.forallE domain (expected plain (continuationValue domain original))) := by
    intro h
    exact continuationValue_ne domain original (VExpr.app.inj (VExpr.forallE.inj h).2).2
  have baseNone : setup.basic 0 ctx (.forallE domain (expected plain original))
      (.forallE domain (expected plain (continuationValue domain original))) = none := rfl
  obtain ⟨equation,proved,kind⟩ := LeanStructuralConversion.prove_forall_complete unequal baseNone
    domainEq domainProved domainType body bodyProved bodyType
  exact LeanStructuralConversion.conversion_of_prove equation proved kind

theorem direct_beta_conversion (setup : Arithmetic.AliasSetup env) (arithmetic : Arithmetic.Signatures env)
    (signatures : Signatures env) (closed : ClosedConstantTypes env) (binder : Binder)
    (plainTyped : CastTyping env 0 (SourceCasts env) (binder.core::ctx) plain (optionType stateType))
    (sourceTyped : CastTyping env 0 (SourceCasts env) (binder.core::ctx) original (optionType stepState))
    (sourceForm : Arithmetic.ValueForm setup (binder.core::ctx) original (optionType stepState))
    (eqDeclared : env.constants ``Eq = some eqSignature)
    (stateFresh : ∀ r ∈ setup.rules, ``HybridWord.State ≠ r.name)
    (eqFresh : ∀ r ∈ setup.rules, ``Eq ≠ r.name) :
    ∃ result, setup.conversion 0 ctx (.forallE binder.core (expected plain original))
      (.forallE binder.core (expected plain (continuationValue binder.core original))) = some result :=
  direct_beta_conversion_domain setup arithmetic signatures closed
    (binder.typed signatures arithmetic) binder.closed (binder.basic_none setup stateFresh)
    plainTyped sourceTyped sourceForm eqDeclared eqFresh

inductive NormalizationCasts (setup : Arithmetic.AliasSetup env) : TypeCasts where
  | base {actual required : VExpr} : ProofCasts setup ctx actual required → NormalizationCasts setup ctx actual required
  | continuation (binder : Binder)
      (plainTyped : CastTyping env 0 (SourceCasts env) (binder.core::ctx) plain (optionType stateType))
      (sourceTyped : CastTyping env 0 (SourceCasts env) (binder.core::ctx) original (optionType stepState))
      (plainForm : Arithmetic.ValueForm setup (binder.core::ctx) plain (optionType stateType))
      (sourceForm : Arithmetic.ValueForm setup (binder.core::ctx) original (optionType stepState)) :
      NormalizationCasts setup ctx (.forallE binder.core (expected plain original))
        (bindPremise binder.core (.lam binder.core plain) (.lam binder.core original))

-- This is a proof-side conversion case for elaborator-generated Unit binds.
  | unit (units : UnitStep.Signatures env)
      (plainTyped : CastTyping env 0 (SourceCasts env) ctx plain (optionType stateType))
      (sourceTyped : CastTyping env 0 (SourceCasts env) (UnitStep.unitType::ctx) original (optionType stepState))
      (sourceForm : Arithmetic.ValueForm setup ctx (original.inst UnitStep.unitValue) (optionType stepState)) :
      NormalizationCasts setup ctx (expected plain (original.inst UnitStep.unitValue))
        (expected plain (.app (.lam UnitStep.unitType original) UnitStep.unitValue))

instance : Arithmetic.Includes (NormalizationCasts setup) := ⟨fun _ _ _ h => .base (.source (.arithmetic h))⟩

theorem NormalizationCasts.covered (setup : Arithmetic.AliasSetup env) (arithmetic : Arithmetic.Signatures env)
    (signatures : Signatures env) (closed : ClosedConstantTypes env)
    (consDeclared : env.constants ``List.cons = some consSignature)
    (eqDeclared : env.constants ``Eq = some eqSignature)
    (evalDeclared : env.constants ``HybridWord.Cmd.eval = some ⟨0,evalSignature⟩)
    (stateFresh : ∀ r ∈ setup.rules, ``HybridWord.State ≠ r.name)
    (eqFresh : ∀ r ∈ setup.rules, ``Eq ≠ r.name)
    (liftFresh : ∀ r ∈ setup.rules, ``WordLoopFacts.lift ≠ r.name) :
    Conversion.Covers setup.conversion 0 (NormalizationCasts setup) := by
  intro ctx actual required cast
  cases cast with
  | base cast =>
    exact ProofCasts.covered setup arithmetic closed arithmetic.word consDeclared signatures.state
      signatures.option eqDeclared evalDeclared stateFresh eqFresh ctx actual required cast
  | continuation binder plainTyped sourceTyped plainForm sourceForm =>
    exact bind_beta_conversion setup arithmetic signatures closed (binder.typed signatures arithmetic) binder.closed
      (binder.basic_none setup stateFresh) plainTyped sourceTyped plainForm sourceForm eqDeclared eqFresh liftFresh
  | unit units plainTyped sourceTyped sourceForm =>
    exact UnitStep.premise_conversion setup arithmetic signatures units closed plainTyped sourceTyped
      sourceForm eqDeclared eqFresh

end IRComparison.WordFrontend.Certificate.Step
