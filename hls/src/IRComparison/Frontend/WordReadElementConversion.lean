import IRComparison.Frontend.WordReadAnnotationTypes
import IRComparison.Frontend.WordArithmeticConversion

/-! Conversion of the element argument actually emitted for an annotated
array read. The bound counts this fixed library application spine, not source
body size or loop iterations. -/
namespace IRComparison.WordFrontend.Read
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic
set_option maxHeartbeats 1800000

def getterPrefix : VExpr := applications (.const ``GetElem?.getElem? [.zero,.zero,.zero])
  [arrayType,natType]
def getterPrefixType : VExpr := .forallE resultParameter
  (.forallE (.app (.const ``outParam [predicateAnnotation]) predicateType)
    (.forallE (applications (.const ``GetElem? [.zero,.zero,.zero]) [arrayType,natType,.bvar 1,.bvar 0])
      (.forallE arrayType (.forallE natType (optionType (.bvar 4))))))

theorem Signatures.getter_prefix_typed (signatures : Signatures env) :
    DirectTyping env 0 ctx getterPrefix getterPrefixType := by
  have getter : DirectTyping env 0 ctx (.const ``GetElem?.getElem? [.zero,.zero,.zero])
      (getSignature.type.instL [.zero,.zero,.zero]) := .constant signatures.getter (by simp [VLevel.WF]) rfl
  have first := DirectTyping.application getter signatures.array_typed
  simp only [getSignature,applications,VExpr.instL,VLevel.inst,VExpr.inst,VExpr.instVar_lower,
    VExpr.instVar_zero,VExpr.instVar_succ,arrayType,wordType,VExpr.lift,VExpr.liftN] at first
  have second := DirectTyping.application first signatures.natural_typed
  simpa only [getterPrefix,getterPrefixType,resultParameter,predicateAnnotation,predicateType,arrayType,
    wordType,natType,optionType,applications,VExpr.inst,VExpr.instVar_lower,VExpr.instVar_zero,
    VExpr.instVar_succ,VExpr.lift,VExpr.liftN] using second

theorem Signatures.dictionary_typed (signatures : Signatures env) :
    DirectTyping env 0 ctx (.app (.const ``Array.instGetElem?NatLtSize [.zero]) wordType)
      (applications dictionaryPrefix [wordType,validity]) := by
  have instanceTyped : DirectTyping env 0 ctx (.const ``Array.instGetElem?NatLtSize [.zero])
      (arrayInstanceSignature.type.instL [.zero]) := .constant signatures.instanceArray (by simp [VLevel.WF]) rfl
  have typed := DirectTyping.application instanceTyped signatures.word_typed
  simpa only [arrayInstanceSignature,dictionaryPrefix,arrayType,natType,validity,applications,
    VExpr.instL,VLevel.inst,VExpr.inst,VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ,
    wordType,VExpr.lift,VExpr.liftN] using typed

theorem element_header_proved (setup : AliasSetup env) (arithmetic : Arithmetic.Signatures env)
    (library : Signatures env) (closed : ClosedConstantTypes env)
    (getterFresh : ∀ r ∈ setup.rules, ``GetElem?.getElem? ≠ r.name)
    (instanceFresh : ∀ r ∈ setup.rules, ``Array.instGetElem?NatLtSize ≠ r.name) (fuel : Nat) :
    ∃ equation, LeanStructuralConversion.prove env setup.basic setup.exposure 0 (fuel+8) ctx
      header bitsHeader = some equation ∧
      equation.type = .forallE arrayType (.forallE natType (optionType wordType)) := by
  have notReduced {a b : VExpr}
      (ha : LeanTypeReduction.constantHead a = some (``GetElem?.getElem?,[.zero,.zero,.zero]))
      (hb : LeanTypeReduction.constantHead b = some (``GetElem?.getElem?,[.zero,.zero,.zero])) :
      setup.basic 0 ctx a b = none :=
    setup.basic_values_none (ty := wordType) (.constant ha getterFresh (by decide))
      (.constant hb getterFresh (by decide)) (by intro u h; cases h)
  obtain ⟨prefixEq,hprefix,tprefix⟩ := LeanStructuralConversion.prove_reflexive_complete
    library.getter_prefix_typed (notReduced rfl rfl) (fuel+4) setup.exposure
  obtain ⟨aliasProof,halias,aliasType⟩ := setup.word_bitvec (U := 0) (ctx := ctx)
  obtain ⟨domainEq,hdomain,tdomain⟩ := LeanStructuralConversion.prove_base_complete halias (fuel+4) setup.exposure
  rw [aliasType] at tdomain
  obtain ⟨cast,hcast⟩ := setup.covers_source_recursive arithmetic closed (fuel+1) ctx _ _ (.arithmetic .resultType)
  obtain ⟨third,hthird,tthird⟩ := LeanStructuralConversion.prove_application_cast_complete
    (fa := getterPrefix) (fb := getterPrefix) rfl rfl
    (by intro h; cases (VExpr.app.inj h).2) (notReduced rfl rfl)
    prefixEq hprefix tprefix domainEq hdomain (fun _ => by rw [tdomain]; exact ⟨cast,hcast⟩)
  obtain ⟨predEq,hpred,tpred⟩ := LeanStructuralConversion.prove_reflexive_complete
    library.validity_typed (by rfl : setup.basic 0 ctx validity validity = none) (fuel+5) setup.exposure
  have predCast : SourceCasts env ctx predicateType
      (.app (.const ``outParam [predicateAnnotation]) predicateType) :=
    .parameter predicateType (library.predicate_typed (ctx := [])) (by trivial) (by trivial) rfl
  obtain ⟨cast,hcast⟩ := setup.covers_source_recursive arithmetic closed (fuel+2) ctx _ _ predCast
  have thirdType : third.type = .forallE (.app (.const ``outParam [predicateAnnotation]) predicateType)
      (.forallE (applications dictionaryPrefix [wordType,.bvar 0])
        (.forallE arrayType (.forallE natType (optionType wordType)))) := by
    simpa only [getterPrefixType,dictionaryPrefix,predicateType,arrayType,natType,optionType,wordType,
      applications,VExpr.inst,VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.lift,VExpr.liftN] using tthird
  obtain ⟨fourth,hfourth,tfourth⟩ := LeanStructuralConversion.prove_application_cast_complete
    (fa := .app getterPrefix wordType) (fb := .app getterPrefix bitvecType) rfl rfl
    (by intro h; cases (VExpr.app.inj (VExpr.app.inj h).1).2) (notReduced rfl rfl)
    third hthird thirdType predEq hpred (fun _ => by rw [tpred]; exact ⟨cast,hcast⟩)
  have dictionaryNone : setup.basic 0 ctx
      (.app (.const ``Array.instGetElem?NatLtSize [.zero]) wordType)
      (.app (.const ``Array.instGetElem?NatLtSize [.zero]) wordType) = none :=
    setup.basic_no_reduction _ _ rfl rfl instanceFresh instanceFresh rfl
  obtain ⟨dictionaryEq,hdictionary,tdictionary⟩ := LeanStructuralConversion.prove_reflexive_complete
    library.dictionary_typed dictionaryNone (fuel+6) setup.exposure
  have fourthType : fourth.type = .forallE (applications dictionaryPrefix [wordType,validity])
      (.forallE arrayType (.forallE natType (optionType wordType))) := by
    simpa only [dictionaryPrefix,predicateType,arrayType,natType,optionType,wordType,validity,
      applications,VExpr.inst,VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.lift,VExpr.liftN] using tfourth
  obtain ⟨equation,proved,kind⟩ := LeanStructuralConversion.prove_application_complete
    (fa := .app (.app getterPrefix wordType) validity) (fb := .app (.app getterPrefix bitvecType) validity) rfl rfl
    (by intro h; cases (VExpr.app.inj (VExpr.app.inj (VExpr.app.inj h).1).1).2) (notReduced rfl rfl)
    fourth hfourth fourthType dictionaryEq hdictionary tdictionary
  exact ⟨equation,proved,by simpa only [arrayType,natType,optionType,wordType,VExpr.inst] using kind⟩

def bitsSourceCore (array index : VExpr) : VExpr := .app (.app bitsHeader array) index

theorem element_source_proved (setup : AliasSetup env) (arithmetic : Arithmetic.Signatures env)
    (library : Signatures env) (closed : ClosedConstantTypes env)
    (getterFresh : ∀ r ∈ setup.rules, ``GetElem?.getElem? ≠ r.name)
    (instanceFresh : ∀ r ∈ setup.rules, ``Array.instGetElem?NatLtSize ≠ r.name)
    (arrayTyped : DirectTyping env 0 ctx arr arrayType)
    (arrayForm : ValueForm setup ctx arr arrayType)
    (indexTyped : CastTyping env 0 (SourceCasts env) ctx index natType)
    (indexForm : ValueForm setup ctx index natType) (fuel : Nat) :
    ∃ equation, LeanStructuralConversion.prove env setup.basic setup.exposure 0 (fuel+10) ctx
      (.app (.app header arr) index) (bitsSourceCore arr index) = some equation ∧
      equation.type = optionType wordType := by
  obtain ⟨fn,hfn,tfn⟩ := element_header_proved setup arithmetic library closed getterFresh instanceFresh fuel
  obtain ⟨arrayEq,harray,tarray⟩ := LeanStructuralConversion.prove_reflexive_complete arrayTyped
    (setup.basic_values_none arrayForm arrayForm (by intro u h; cases h)) (fuel+7) setup.exposure
  obtain ⟨applied,happlied,tapplied⟩ := LeanStructuralConversion.prove_application_complete
    (fa := header) (fb := bitsHeader) rfl rfl
    (by intro h; have h := (VExpr.app.inj (VExpr.app.inj (VExpr.app.inj (VExpr.app.inj h).1).1).1).2; cases h)
    (setup.basic_no_reduction _ _ rfl rfl getterFresh getterFresh rfl)
    fn hfn tfn arrayEq harray tarray
  obtain ⟨indexEq,hindex,tindex⟩ := LeanStructuralConversion.prove_reflexive_cast_complete indexTyped
    (setup.basic_values_none indexForm indexForm (by intro u h; cases h))
    (setup.covers_source_recursive arithmetic closed (fuel+4))
  have nextType : applied.type = .forallE natType (optionType wordType) := by
    simpa only [natType,optionType,wordType,VExpr.inst] using tapplied
  obtain ⟨equation,proved,kind⟩ := LeanStructuralConversion.prove_application_complete
    (fa := .app header arr) (fb := .app bitsHeader arr) rfl rfl
    (by intro h; have h := (VExpr.app.inj (VExpr.app.inj (VExpr.app.inj (VExpr.app.inj (VExpr.app.inj h).1).1).1).1).2; cases h)
    (setup.basic_no_reduction _ _ rfl rfl getterFresh getterFresh rfl)
    applied happlied nextType indexEq hindex tindex
  exact ⟨equation,proved,by simpa only [optionType,wordType,VExpr.inst] using kind⟩

theorem element_equality_conversion (setup : AliasSetup env) (arithmetic : Arithmetic.Signatures env)
    (library : Signatures env) (closed : ClosedConstantTypes env)
    (getterFresh : ∀ r ∈ setup.rules, ``GetElem?.getElem? ≠ r.name)
    (instanceFresh : ∀ r ∈ setup.rules, ``Array.instGetElem?NatLtSize ≠ r.name)
    (eqFresh : ∀ r ∈ setup.rules, ``Eq ≠ r.name)
    (prefixTyped : CastTyping env 0 (SourceCasts env) ctx
      (.app (.app (.const ``Eq [.succ .zero]) (optionType wordType)) lhs)
      (.forallE (optionType wordType) (.sort .zero)))
    (arrayTyped : DirectTyping env 0 ctx arr arrayType)
    (arrayForm : ValueForm setup ctx arr arrayType)
    (indexTyped : CastTyping env 0 (SourceCasts env) ctx index natType)
    (indexForm : ValueForm setup ctx index natType) :
    ∃ result, setup.conversion 0 ctx
      (equalValues (optionType wordType) lhs (.app (.app header arr) index))
      (equalValues (optionType wordType) lhs (bitsSourceCore arr index)) = some result := by
  obtain ⟨prefixEq,hprefix,tprefix⟩ := LeanStructuralConversion.prove_reflexive_cast_complete prefixTyped
    (setup.basic_no_reduction _ _ rfl rfl eqFresh eqFresh rfl)
    (setup.covers_source_recursive arithmetic closed 58)
  obtain ⟨value,hvalue,tvalue⟩ := element_source_proved setup arithmetic library closed getterFresh instanceFresh
    arrayTyped arrayForm indexTyped indexForm 53
  obtain ⟨equation,proved,kind⟩ := LeanStructuralConversion.prove_application_complete
    (leftName := ``Eq) (rightName := ``Eq) rfl rfl
    (by intro h
        have h := (VExpr.app.inj h).2
        have h := (VExpr.app.inj (VExpr.app.inj (VExpr.app.inj (VExpr.app.inj (VExpr.app.inj h).1).1).1).1).2
        cases h)
    (setup.basic_no_reduction _ _ rfl rfl eqFresh eqFresh rfl)
    prefixEq hprefix tprefix value hvalue tvalue
  exact LeanStructuralConversion.conversion_of_prove equation proved kind

end IRComparison.WordFrontend.Read
