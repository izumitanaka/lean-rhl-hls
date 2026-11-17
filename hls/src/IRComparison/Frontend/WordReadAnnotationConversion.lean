import IRComparison.Frontend.WordBinderConversion
import IRComparison.Frontend.WordBindCompleteness

/-! Fixed-depth conversions for the Word/BV32 annotation of a do-read binder.
Only the existing Option bind application is compared; source bodies are not
normalized recursively and no source-size bound is introduced. -/
namespace IRComparison.WordFrontend.WordBinder
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic
set_option maxHeartbeats 1500000

theorem bind_header_proved (setup : AliasSetup env) (library : BindSignatures env)
    (resultTyped : ∀ ctx, DirectTyping env 0 ctx resultType (.sort (.succ .zero)))
    (resultClosed : resultType.ClosedN 0)
    (resultHead : LeanTypeReduction.constantHead resultType = some (resultName,resultLevels))
    (resultFresh : ∀ r ∈ setup.rules, resultName ≠ r.name)
    (resultBase : setup.base 0 ctx resultType resultType = none)
    (bindFresh : ∀ r ∈ setup.rules, ``Bind.bind ≠ r.name)
    (fuel : Nat) :
    ∃ equation, LeanStructuralConversion.prove env setup.basic setup.exposure 0 (fuel+3) ctx
      (optionBindHeader wordType resultType) (optionBindHeader bitvecType resultType) = some equation ∧
      equation.type = .forallE (optionType wordType)
        (.forallE (.forallE wordType (optionType resultType)) (optionType resultType)) := by
  have resultLift (n k : Nat) : resultType.liftN n k = resultType := resultClosed.liftN_eq (Nat.zero_le k)
  have resultInst (v : VExpr) (k : Nat) : resultType.inst v k = resultType := resultClosed.instN_eq (Nat.zero_le k)
  have prefixNone : setup.basic 0 ctx optionBindPrefix optionBindPrefix = none :=
    setup.basic_no_reduction _ _ rfl rfl bindFresh bindFresh rfl
  obtain ⟨prefixEq,hprefix,tprefix⟩ := LeanStructuralConversion.prove_reflexive_complete
    library.prefix_typed prefixNone fuel setup.exposure
  obtain ⟨cast,hcast,kind⟩ := setup.word_bitvec (U := 0) (ctx := ctx)
  obtain ⟨domainEq,hdomain,tdomain⟩ := LeanStructuralConversion.prove_base_complete hcast fuel setup.exposure
  rw [kind] at tdomain
  obtain ⟨applied,happlied,tapplied⟩ := LeanStructuralConversion.prove_application_complete
    (leftName := ``Bind.bind) (rightName := ``Bind.bind) rfl rfl
    (by intro h; cases (VExpr.app.inj h).2)
    (setup.basic_no_reduction _ _ rfl rfl bindFresh bindFresh rfl)
    prefixEq hprefix tprefix domainEq hdomain tdomain
  have st := resultTyped ctx
  have stateNone : setup.basic 0 ctx resultType resultType = none :=
    setup.basic_no_reduction _ _ resultHead resultHead resultFresh resultFresh resultBase
  obtain ⟨resultEq,hresult,tresult⟩ := LeanStructuralConversion.prove_reflexive_complete st stateNone (fuel+1) setup.exposure
  have nextType : applied.type = .forallE (.sort (.succ .zero))
      (.forallE (optionType wordType)
        (.forallE (.forallE wordType (optionType (.bvar 2))) (optionType (.bvar 2)))) := by
    simpa only [optionBindPrefixType,optionType,VExpr.inst,VExpr.instVar_lower,VExpr.instVar_zero,
      VExpr.instVar_succ,VExpr.lift,VExpr.liftN,wordType,liftVar,Nat.reduceAdd,Nat.reduceLT,ite_true,ite_false] using tapplied
  obtain ⟨equation,proved,typed⟩ := LeanStructuralConversion.prove_application_complete
    (leftName := ``Bind.bind) (rightName := ``Bind.bind) rfl rfl
    (by intro h; have h := (VExpr.app.inj (VExpr.app.inj h).1).2; cases h)
    (setup.basic_no_reduction _ _ rfl rfl bindFresh bindFresh rfl)
    applied happlied nextType resultEq hresult tresult
  refine ⟨equation,proved,?_⟩
  simpa only [optionType,wordType,VExpr.inst,resultInst,VExpr.instVar_lower,VExpr.instVar_zero,
    VExpr.instVar_succ,VExpr.lift,VExpr.liftN,resultLift,liftVar,Nat.reduceAdd,Nat.reduceLT,ite_true,ite_false] using typed

def bindValueAnnotated (domain first next : VExpr) (resultType : VExpr := stateType) : VExpr :=
  .app (.app (optionBindHeader domain resultType) first) next

theorem bind_value_proved {body : VExpr} (setup : AliasSetup env) (arithmetic : Signatures env)
    (library : BindSignatures env) (closed : ClosedConstantTypes env)
    (resultTyped : ∀ ctx, DirectTyping env 0 ctx resultType (.sort (.succ .zero)))
    (resultClosed : resultType.ClosedN 0)
    (resultHead : LeanTypeReduction.constantHead resultType = some (resultName,resultLevels))
    (resultFresh : ∀ r ∈ setup.rules, resultName ≠ r.name)
    (resultBase : setup.base 0 ctx resultType resultType = none)
    (bindFresh : ∀ r ∈ setup.rules, ``Bind.bind ≠ r.name)
    (firstTyped : CheckedTyping env 0 (SourceCasts env) ctx first (optionType wordType))
    (firstForm : ValueForm setup ctx first (optionType wordType))
    (bodyTyped : CastTyping env 0 (SourceCasts env) (bitvecType::ctx) body (optionType resultType))
    (fuel : Nat) :
    ∃ equation, LeanStructuralConversion.prove env setup.basic setup.exposure 0 (fuel+8) ctx
      (bindValueAnnotated wordType first (.lam bitvecType body) resultType)
      (bindValueAnnotated bitvecType first (.lam bitvecType body) resultType) = some equation ∧
      equation.type = optionType resultType := by
  have resultLift (n k : Nat) : resultType.liftN n k = resultType := resultClosed.liftN_eq (Nat.zero_le k)
  have resultInst (v : VExpr) (k : Nat) : resultType.inst v k = resultType := resultClosed.instN_eq (Nat.zero_le k)
  obtain ⟨header,hheader,theader⟩ := bind_header_proved setup library resultTyped resultClosed resultHead resultFresh resultBase bindFresh (fuel+3)
  have firstNone := setup.basic_values_none firstForm firstForm
    (by intro u; simp [optionType])
  have firstComplete : ∃ applied,
      LeanStructuralConversion.prove env setup.basic setup.exposure 0 (fuel+7) ctx
        (.app (optionBindHeader wordType resultType) first)
        (.app (optionBindHeader bitvecType resultType) first) = some applied ∧
      applied.type = .forallE (.forallE wordType (optionType resultType)) (optionType resultType) := by
    cases firstTyped with
    | exact typed =>
      obtain ⟨firstEq,hfirst,tfirst⟩ := LeanStructuralConversion.prove_reflexive_cast_complete typed firstNone
        (setup.covers_source_recursive arithmetic closed (fuel+1))
      obtain ⟨applied,happlied,tapplied⟩ := LeanStructuralConversion.prove_application_complete
        (leftName := ``Bind.bind) (rightName := ``Bind.bind) rfl rfl
        (by intro h; have h := (VExpr.app.inj (VExpr.app.inj (VExpr.app.inj h).1).1).2; cases h)
        (setup.basic_no_reduction _ _ rfl rfl bindFresh bindFresh rfl)
        header hheader theader firstEq hfirst tfirst
      exact ⟨applied,happlied,by simpa only [optionType,wordType,VExpr.inst,resultInst] using tapplied⟩
    | converted typed cast =>
      obtain ⟨firstEq,hfirst,tfirst⟩ := LeanStructuralConversion.prove_reflexive_cast_complete typed firstNone
        (setup.covers_source_recursive arithmetic closed (fuel+1))
      obtain ⟨castProof,hcastProof⟩ := setup.covers_source_recursive arithmetic closed (fuel+2) ctx _ _ cast
      obtain ⟨applied,happlied,tapplied⟩ := LeanStructuralConversion.prove_application_cast_complete
        (leftName := ``Bind.bind) (rightName := ``Bind.bind) rfl rfl
        (by intro h; have h := (VExpr.app.inj (VExpr.app.inj (VExpr.app.inj h).1).1).2; cases h)
        (setup.basic_no_reduction _ _ rfl rfl bindFresh bindFresh rfl)
        header hheader theader firstEq hfirst (fun _ => by rw [tfirst]; exact ⟨castProof,hcastProof⟩)
      exact ⟨applied,happlied,by simpa only [optionType,wordType,VExpr.inst,resultInst] using tapplied⟩
  obtain ⟨applied,happlied,tapplied⟩ := firstComplete
  have nextTyped := CastTyping.lambda (arithmetic.bitvec_typed.withCasts (SourceCasts env)) bodyTyped
  obtain ⟨nextEq,hnext,tnext⟩ := LeanStructuralConversion.prove_reflexive_cast_complete nextTyped
    (show setup.basic 0 ctx (.lam bitvecType body) (.lam bitvecType body) = none from rfl)
    (setup.covers_source_recursive arithmetic closed (fuel+2))
  have optionResult : DirectTyping env 0 [] (optionType resultType) (.sort (.succ .zero)) :=
    .application (.constant library.option (by simp [VLevel.WF]) rfl) (resultTyped [])
  obtain ⟨cast,hcast⟩ := setup.covers_source_recursive arithmetic closed (fuel+3) ctx _ _ (.wordFunction optionResult)
  obtain ⟨equation,proved,typed⟩ := LeanStructuralConversion.prove_application_cast_complete
    (leftName := ``Bind.bind) (rightName := ``Bind.bind) rfl rfl
    (by intro h; have h := (VExpr.app.inj (VExpr.app.inj (VExpr.app.inj (VExpr.app.inj h).1).1).1).2; cases h)
    (setup.basic_no_reduction _ _ rfl rfl bindFresh bindFresh rfl)
    applied happlied tapplied nextEq hnext (fun _ => by rw [tnext]; exact ⟨cast,hcast⟩)
  refine ⟨equation,proved,?_⟩
  simpa only [optionType,wordType,VExpr.inst,resultInst,VExpr.instVar_lower,VExpr.instVar_zero,
    VExpr.instVar_succ,VExpr.lift,VExpr.liftN,resultLift,liftVar,Nat.reduceAdd,Nat.reduceLT,ite_true,ite_false] using typed

theorem bind_equality_conversion {body : VExpr} (setup : AliasSetup env) (arithmetic : Signatures env)
    (library : BindSignatures env) (closed : ClosedConstantTypes env)
    (resultTyped : ∀ ctx, DirectTyping env 0 ctx resultType (.sort (.succ .zero)))
    (resultClosed : resultType.ClosedN 0)
    (resultHead : LeanTypeReduction.constantHead resultType = some (resultName,resultLevels))
    (resultFresh : ∀ r ∈ setup.rules, resultName ≠ r.name)
    (resultBase : setup.base 0 ctx resultType resultType = none)
    (bindFresh : ∀ r ∈ setup.rules, ``Bind.bind ≠ r.name)
    (eqFresh : ∀ r ∈ setup.rules, ``Eq ≠ r.name)
    (prefixTyped : CastTyping env 0 (SourceCasts env) ctx
      (.app (.app (.const ``Eq [.succ .zero]) (optionType resultType)) lhs)
      (.forallE (optionType resultType) (.sort .zero)))
    (firstTyped : CheckedTyping env 0 (SourceCasts env) ctx first (optionType wordType))
    (firstForm : ValueForm setup ctx first (optionType wordType))
    (bodyTyped : CastTyping env 0 (SourceCasts env) (bitvecType::ctx) body (optionType resultType)) :
    ∃ result, setup.conversion 0 ctx
      (equalValues (optionType resultType) lhs (bindValueAnnotated wordType first (.lam bitvecType body) resultType))
      (equalValues (optionType resultType) lhs (bindValueAnnotated bitvecType first (.lam bitvecType body) resultType)) = some result := by
  have resultLift (n k : Nat) : resultType.liftN n k = resultType := resultClosed.liftN_eq (Nat.zero_le k)
  have resultInst (v : VExpr) (k : Nat) : resultType.inst v k = resultType := resultClosed.instN_eq (Nat.zero_le k)
  have prefixNone : setup.basic 0 ctx
      (.app (.app (.const ``Eq [.succ .zero]) (optionType resultType)) lhs)
      (.app (.app (.const ``Eq [.succ .zero]) (optionType resultType)) lhs) = none :=
    setup.basic_no_reduction _ _ rfl rfl eqFresh eqFresh rfl
  obtain ⟨prefixEq,hprefix,tprefix⟩ := LeanStructuralConversion.prove_reflexive_cast_complete prefixTyped prefixNone
    (setup.covers_source_recursive arithmetic closed 58)
  obtain ⟨value,hvalue,tvalue⟩ := bind_value_proved setup arithmetic library closed resultTyped resultClosed resultHead resultFresh resultBase bindFresh
    firstTyped firstForm bodyTyped 55
  obtain ⟨equation,proved,kind⟩ := LeanStructuralConversion.prove_application_complete
    (leftName := ``Eq) (rightName := ``Eq) rfl rfl
    (by intro h
        have h := (VExpr.app.inj h).2
        have h := (VExpr.app.inj (VExpr.app.inj (VExpr.app.inj (VExpr.app.inj h).1).1).1).2
        cases h)
    (setup.basic_no_reduction _ _ rfl rfl eqFresh eqFresh rfl)
    prefixEq hprefix tprefix value hvalue tvalue
  exact LeanStructuralConversion.conversion_of_prove equation proved kind

end IRComparison.WordFrontend.WordBinder
