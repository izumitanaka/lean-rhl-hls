import IRComparison.Frontend.WordArithmeticTyping
import IRComparison.Frontend.LeanStructuralCompleteness
import IRComparison.Frontend.WordLoadingCompleteness

/-! Completeness of the concrete alias/structural converter used by the Word
frontend for the casts introduced by Lean's arithmetic notation. -/
namespace IRComparison.WordFrontend.Arithmetic
open Lean4Lean LeanTypeInference LeanTypeReduction Certificate

/-- The same base converter installed by `WordFrontend.load`. -/
def arithmeticBase (identity : LeanTypeAliases.Alias native ``outParam)
    (registered : env.defeqs identity.equation) : Conversion env :=
  LeanUniverseConversion.orElse
    (identity.conversion registered (LeanUniverseConversion.conversion env))
    (LeanUniverseConversion.conversion env)

private theorem reduction_preserves_base (rules : List (Rule env))
    (base : Conversion env) (accepted : base U ctx a b = some result) :
    ∃ result, LeanTypeReduction.conversion rules base U ctx a b = some result := by
  unfold LeanTypeReduction.conversion
  cases left : expose rules base U ctx a <;> simp only [left]
  · cases right : expose rules base U ctx b <;> simp only [right]
    · exact ⟨_,accepted⟩
    · split
      · exact ⟨_,rfl⟩
      · exact ⟨_,accepted⟩
  · split
    · exact ⟨_,rfl⟩
    · cases right : expose rules base U ctx b <;> simp only [right]
      · exact ⟨_,accepted⟩
      · split
        · exact ⟨_,rfl⟩
        · exact ⟨_,accepted⟩

private theorem expose_missing (source : VExpr)
    (head : constantHead source = some (name,levels))
    (rules : List (Rule env)) (absent : ∀ r ∈ rules, name ≠ r.name)
    (base : Conversion env) : expose rules base U ctx source = none := by
  have stopped := reduce_missing
    (step_constantHead_missing source head rules absent base (noExposure env) (U := U) (ctx := ctx)) 32
  simp only [expose,stopped,bind,Option.bind]

/-- The fixed type alias used by Lean's generated Boolean equality decision.
Only its Type-0 instance is needed by the accepted Word/BV32 conditions. -/
def decEqBody : VExpr := .lam (.sort (.succ .zero)) (decEqFunction (.bvar 0))
def decEqKind : VExpr := .forallE (.sort (.succ .zero))
  (.sort (.max (.succ .zero) (.succ .zero)))
def DecEqDeclaration (native : Lean.Environment) : Prop :=
  ∀ definition : Definition native ``DecidableEq,
    definition.declaration.levelParams.length = 1 ∧
    definition.body.val.instL [.succ .zero] = decEqBody ∧
    definition.type.val.instL [.succ .zero] = decEqKind

/-- Declaration conditions, not successful-checker assumptions. The frontend's
four delta rules meet these conditions when the user declaration has a fresh
name, and the Word declaration is the installed `BitVec 32` abbreviation. -/
structure AliasSetup (env : VEnv) where
  native : Lean.Environment
  identity : LeanTypeAliases.Alias native ``outParam
  identityRegistered : env.defeqs identity.equation
  leadingRules : List (Rule env)
  wordRule : Rule env
  trailingRules : List (Rule env)
  declaredRules : ∀ r ∈ leadingRules ++ wordRule :: trailingRules, env.constants r.name =
    some ⟨r.definition.declaration.levelParams.length,r.definition.type.val⟩
  decEqView : ∃ (beforeRules : List (Rule env)) (r : Rule env) (suffix : List (Rule env)),
    leadingRules ++ wordRule :: trailingRules = beforeRules ++ r :: suffix ∧
    r.name = ``DecidableEq ∧ r.definition.declaration.levelParams.length = 1 ∧
    r.definition.body.val.instL [.succ .zero] = decEqBody ∧
    r.definition.type.val.instL [.succ .zero] = decEqKind ∧
    ∀ before ∈ beforeRules, r.name ≠ before.name
  wordName : wordRule.name = ``HybridWord.Word
  wordMonomorphic : wordRule.definition.declaration.levelParams.length = 0
  wordBody : wordRule.definition.body.val.instL [] = bitvecType
  wordKind : wordRule.definition.type.val.instL [] = .sort (.succ .zero)
  wordFirst : ∀ r ∈ leadingRules, wordRule.name ≠ r.name
  irreducibleBitVec : ∀ r ∈ leadingRules ++ wordRule :: trailingRules, ``BitVec ≠ r.name
  irreducibleOfNat : ∀ r ∈ leadingRules ++ wordRule :: trailingRules, ``OfNat ≠ r.name
  irreducibleNumeral : ∀ n ∈ [``Nat.zero,``Nat.succ,``Nat.mul],
    ∀ r ∈ leadingRules ++ wordRule :: trailingRules, n ≠ r.name
  irreducibleNeg : ∀ r ∈ leadingRules ++ wordRule :: trailingRules, ``Neg ≠ r.name
  irreducibleReadClass : ∀ r ∈ leadingRules ++ wordRule :: trailingRules, ``GetElem? ≠ r.name
  irreducibleOption : ∀ r ∈ leadingRules ++ wordRule :: trailingRules, ``Option ≠ r.name
  irreducibleHeterogeneous : ∀ op : Binary, ∀ r ∈ leadingRules ++ wordRule :: trailingRules,
    op.heterogeneous ≠ r.name
  irreducibleClass : ∀ op : Binary, ∀ r ∈ leadingRules ++ wordRule :: trailingRules,
    op.className ≠ r.name

def AliasSetup.rules (setup : AliasSetup env) := setup.leadingRules ++ setup.wordRule :: setup.trailingRules

def AliasSetup.base (setup : AliasSetup env) : Conversion env :=
  arithmeticBase setup.identity setup.identityRegistered

def AliasSetup.basic (setup : AliasSetup env) : Conversion env :=
  LeanTypeReduction.conversion setup.rules setup.base

def AliasSetup.exposure (setup : AliasSetup env) : Exposure env :=
  fun U ctx e => expose setup.rules setup.basic U ctx e

def AliasSetup.conversion (setup : AliasSetup env) : Conversion env :=
  LeanStructuralConversion.conversion env setup.basic setup.exposure

theorem AliasSetup.basic_no_reduction (setup : AliasSetup env) (a b : VExpr)
    (headA : constantHead a = some (na,la)) (headB : constantHead b = some (nb,lb))
    (absentA : ∀ r ∈ setup.rules, na ≠ r.name) (absentB : ∀ r ∈ setup.rules, nb ≠ r.name)
    (noBase : setup.base U ctx a b = none) : setup.basic U ctx a b = none := by
  have left := expose_missing a headA setup.rules absentA setup.base (U := U) (ctx := ctx)
  have right := expose_missing b headB setup.rules absentB setup.base (U := U) (ctx := ctx)
  simp only [AliasSetup.basic,LeanTypeReduction.conversion,left,right,noBase,bind,Option.bind]

/-- The two heads of source computations used by ordinary elaborated bodies:
a library operation or an administrative let/beta application. This is a
proof-side shape witness, not a new input AST or a new parser restriction. -/
inductive ValueForm (setup : AliasSetup env) (ctx : List VExpr) : VExpr → VExpr → Prop where
  | bound : ValueForm setup ctx (.bvar n) ty
  | constant (head : constantHead source = some (name,levels))
      (fresh : ∀ r ∈ setup.rules, name ≠ r.name) (notAlias : name ≠ ``outParam) :
      ValueForm setup ctx source ty
  | declaredConstant (declared : env.constants name = some signature) (notAlias : name ≠ ``outParam) :
      ValueForm setup ctx (.const name levels) (signature.type.instL levels)
  | beta {body : VExpr} (bodyTyped : CastTyping env 0 (SourceCasts env) (domain::ctx) body resultType) :
      ValueForm setup ctx (.app (.lam domain body) arg) (resultType.inst arg)
  | application (function : ValueForm setup ctx fn (.forallE domain codomain)) :
      ValueForm setup ctx (.app fn arg) (codomain.inst arg)

theorem ValueForm.notLambda {setup : AliasSetup env} (form : ValueForm setup ctx source ty) :
    ∀ domain body, source ≠ .lam domain body := by
  intro domain body same
  cases same
  cases form with
  | constant head _ _ => cases head

theorem ValueForm.step_kind_rules {setup : AliasSetup env} (form : ValueForm setup ctx source ty)
    (rules : List (Rule env)) (included : ∀ r ∈ rules, r ∈ setup.rules)
    (conv : Conversion env) (exposure : Exposure env)
    (stepped : step rules conv 0 ctx exposure source = some result) : result.val.2 = ty := by
  induction form with
  | constant head fresh notAlias =>
    have stopped := step_constantHead_missing _ head rules
      (fun r member => fresh r (included r member)) conv exposure (U := 0) (ctx := ctx)
    rw [stopped] at stepped
    cases stepped
  | declaredConstant declared notAlias =>
    exact unfoldConstant_kind rules (fun r hr => setup.declaredRules r (included r hr)) declared stepped
  | beta bodyTyped => exact step_beta_kind bodyTyped stepped
  | bound => cases stepped
  | application function ih =>
    exact step_application_kind function.notLambda (fun _ success => ih success) stepped

theorem ValueForm.step_kind {setup : AliasSetup env} (form : ValueForm setup ctx source ty)
    (conv : Conversion env) (exposure : Exposure env)
    (stepped : step [] conv 0 ctx exposure source = some result) : result.val.2 = ty := by
  exact form.step_kind_rules [] (by simp) conv exposure stepped

theorem ValueForm.expose_none {setup : AliasSetup env} (form : ValueForm setup ctx source ty)
    (notSort : ∀ u, ty ≠ .sort u) (conv : Conversion env) :
    expose setup.rules conv 0 ctx source = none := by
  exact expose_not_sort
    (fun _ success u => by
      rw [form.step_kind_rules setup.rules (fun _ h => h) conv _ success]
      exact notSort u) 31

theorem ValueForm.alias_none {setup : AliasSetup env} (form : ValueForm setup ctx source ty) :
    setup.identity.expand setup.identityRegistered 0 ctx source (LeanUniverseConversion.conversion env) = none := by
  cases form with
  | constant head fresh notAlias =>
    exact setup.identity.expand_other_head setup.identityRegistered head notAlias _
  | declaredConstant declared notAlias =>
    exact setup.identity.expand_other_head setup.identityRegistered rfl notAlias _
  | beta bodyTyped => rfl
  | bound => rfl
  | application function =>
    generalize kind : VExpr.forallE _ _ = functionType at function
    cases function with
    | bound => rfl
    | beta => rfl
    | application => rfl
    | declaredConstant declared notAlias =>
      exact setup.identity.expand_other_head setup.identityRegistered rfl notAlias _
    | constant head fresh notAlias =>
      exact setup.identity.expand_other_head setup.identityRegistered
        (by simpa only [constantHead] using head) notAlias _

/-- Application spines preserve the value-head invariant without a depth
bound on administrative helper arguments. -/
theorem ValueForm.arguments (form : ValueForm setup ctx source ty)
    (arguments : ArgumentsCasts env 0 (SourceCasts env) ctx ty args resultType) :
    ValueForm setup ctx (LeanTyped.applications source args) resultType := by
  induction arguments generalizing source with
  | nil => exact form
  | cons argument rest ih => exact ih (.application form)

/-- The same value-shape argument works with convertible argument types.
Static telescope closure is used only to identify the instantiated codomain. -/
theorem ValueForm.checkedArguments
    (form : ValueForm setup ctx source (domains.foldr VExpr.forallE resultType))
    (arguments : List.Forall₂ (fun domain arg =>
      CheckedTyping env 0 (SourceCasts env) ctx arg domain) domains args)
    (typesClosed : ∀ n, ((domains.drop n).foldr VExpr.forallE resultType).ClosedN 0) :
    ValueForm setup ctx (LeanTyped.applications source args) resultType := by
  induction arguments generalizing source with
  | nil => exact form
  | @cons domain arg domains args typed rest ih =>
    have tailTypes : ∀ n, ((domains.drop n).foldr VExpr.forallE resultType).ClosedN 0 := by
      intro n
      simpa only [List.drop_succ_cons] using typesClosed (n+1)
    have tailClosed := tailTypes 0
    simp only [List.drop_zero] at tailClosed
    apply ih
    · simpa only [tailClosed.instN_eq (Nat.zero_le _)] using
        (ValueForm.application (arg := arg) form)
    · exact tailTypes

theorem ValueForm.notSort (form : ValueForm setup ctx source ty) :
    ∀ u, source ≠ .sort u := by
  intro u same
  cases same
  cases form with
  | constant head _ _ => cases head

/-- Value expressions cannot enter type-alias or universe conversion. -/
theorem AliasSetup.basic_values_none_of_types (setup : AliasSetup env)
    (left : ValueForm setup ctx a ty) (right : ValueForm setup ctx b otherType)
    (notSort : ∀ u, ty ≠ .sort u) (otherNotSort : ∀ u, otherType ≠ .sort u) : setup.basic 0 ctx a b = none := by
  have leftExpose := left.expose_none notSort setup.base
  have rightExpose := right.expose_none otherNotSort setup.base
  have leftAlias := left.alias_none
  have rightAlias := right.alias_none
  have universeNone : LeanUniverseConversion.conversion env 0 ctx a b = none := by
    cases a <;> try rfl
    exact False.elim (left.notSort _ rfl)
  simp only [AliasSetup.basic,LeanTypeReduction.conversion,leftExpose,rightExpose]
  simp only [AliasSetup.base,arithmeticBase,LeanUniverseConversion.orElse,
    LeanTypeAliases.Alias.conversion,leftAlias,rightAlias,universeNone,
    Option.orElse,bind,Option.bind]


theorem AliasSetup.basic_values_none (setup : AliasSetup env)
    (left : ValueForm setup ctx a ty) (right : ValueForm setup ctx b ty)
    (notSort : ∀ u, ty ≠ .sort u) : setup.basic 0 ctx a b = none :=
  setup.basic_values_none_of_types left right notSort notSort

/-- A value-valued source, including a leading let, cannot be mistaken for a
type alias when compared with its continuation application. -/
theorem AliasSetup.basic_beta_none {body : VExpr} (setup : AliasSetup env)
    (bodyTyped : CastTyping env 0 (SourceCasts env) (domain::ctx) body resultType)
    (notSort : ∀ u, resultType.inst arg ≠ .sort u)
    (form : ValueForm setup ctx (body.inst arg) (resultType.inst arg)) :
    setup.basic 0 ctx (body.inst arg) (.app (.lam domain body) arg) = none := by
  have left := form.expose_none notSort setup.base
  have right := expose_beta_not_sort bodyTyped notSort setup.rules setup.base 31
  have noAlias := form.alias_none
  have aliasNone : setup.identity.conversion setup.identityRegistered
      (LeanUniverseConversion.conversion env) 0 ctx (body.inst arg) (.app (.lam domain body) arg) = none := by
    simp only [LeanTypeAliases.Alias.conversion,noAlias]
    simp only [LeanTypeAliases.Alias.expand,bind,Option.bind,pure,Option.pure_def]
  have universeNone (a : VExpr) : LeanUniverseConversion.conversion env 0 ctx a
      (.app (.lam domain body) arg) = none := by cases a <;> rfl
  simp only [AliasSetup.basic,LeanTypeReduction.conversion,left,right,bind,Option.bind]
  simp only [AliasSetup.base,arithmeticBase,LeanUniverseConversion.orElse,aliasNone,universeNone,
    Option.orElse,bind,Option.bind,pure,Option.pure_def]

/-- The native loop continuation has two arguments. Its application is a
value, so type-alias probing must leave it to the structural converter. -/
theorem AliasSetup.basic_beta2_none {body : VExpr} (setup : AliasSetup env)
    (bodyTyped : CastTyping env 0 (SourceCasts env) (firstDomain::ctx)
      (.lam secondDomain body) (.forallE secondDomain resultType))
    (notSort : ∀ u, (resultType.inst firstArg 1).inst secondArg ≠ .sort u)
    (form : ValueForm setup ctx ((body.inst firstArg 1).inst secondArg)
      ((resultType.inst firstArg 1).inst secondArg)) :
    setup.basic 0 ctx ((body.inst firstArg 1).inst secondArg)
      (.app (.app (.lam firstDomain (.lam secondDomain body)) firstArg) secondArg) = none := by
  have left := form.expose_none notSort setup.base
  have right := expose_beta2_not_sort bodyTyped notSort setup.rules setup.base 31
  have noAlias := form.alias_none
  have aliasNone : setup.identity.conversion setup.identityRegistered
      (LeanUniverseConversion.conversion env) 0 ctx ((body.inst firstArg 1).inst secondArg)
      (.app (.app (.lam firstDomain (.lam secondDomain body)) firstArg) secondArg) = none := by
    simp only [LeanTypeAliases.Alias.conversion,noAlias]
    simp only [LeanTypeAliases.Alias.expand,bind,Option.bind,pure,Option.pure_def]
  have universeNone (a : VExpr) : LeanUniverseConversion.conversion env 0 ctx a
      (.app (.app (.lam firstDomain (.lam secondDomain body)) firstArg) secondArg) = none := by
    cases a <;> rfl
  simp only [AliasSetup.basic,LeanTypeReduction.conversion,left,right,bind,Option.bind]
  simp only [AliasSetup.base,arithmeticBase,LeanUniverseConversion.orElse,aliasNone,universeNone,
    Option.orElse,bind,Option.bind,pure,Option.pure_def]

private theorem basic_class_none (setup : AliasSetup env) (name : Lean.Name)
    (notAlias : name ≠ ``outParam) (absent : ∀ r ∈ setup.rules, name ≠ r.name) (a b : VExpr) :
    setup.basic U ctx (.app (.const name [.zero]) a) (.app (.const name [.zero]) b) = none := by
  apply AliasSetup.basic_no_reduction setup _ _ rfl rfl absent absent
  simp [AliasSetup.base,arithmeticBase,LeanUniverseConversion.orElse,
    LeanTypeAliases.Alias.conversion,LeanTypeAliases.Alias.expand,
    LeanUniverseConversion.conversion,notAlias]

private theorem basic_class_refl_none (setup : AliasSetup env) (name : Lean.Name)
    (absent : ∀ r ∈ setup.rules, name ≠ r.name) :
    setup.basic U ctx (.const name [.zero]) (.const name [.zero]) = none := by
  exact AliasSetup.basic_no_reduction setup _ _ rfl rfl absent absent rfl

private theorem numeral_basic_none (setup : AliasSetup env) (n : Nat) :
    setup.basic U ctx (LeanTyped.numeral n) (LeanTyped.numeral n) = none := by
  apply LeanTyped.numeral_induction (fun e => setup.basic U ctx e e = none)
  · exact AliasSetup.basic_no_reduction setup _ _ rfl rfl
      (setup.irreducibleNumeral ``Nat.zero (by simp)) (setup.irreducibleNumeral ``Nat.zero (by simp)) rfl
  · intro a _
    exact AliasSetup.basic_no_reduction setup _ _ rfl rfl
      (setup.irreducibleNumeral ``Nat.succ (by simp)) (setup.irreducibleNumeral ``Nat.succ (by simp)) rfl
  · intro a _
    exact AliasSetup.basic_no_reduction setup _ _ rfl rfl
      (setup.irreducibleNumeral ``Nat.mul (by simp)) (setup.irreducibleNumeral ``Nat.mul (by simp)) rfl

theorem AliasSetup.bitvec_word (setup : AliasSetup env) :
    ∃ result, setup.basic U ctx bitvecType wordType = some result ∧ result.val = .succ .zero := by
  have head : constantHead (setup.wordRule.definition.body.val.instL []) = some (``BitVec,[]) := by
    rw [setup.wordBody]; rfl
  have complete := conversion_alias_right_exact (levels := [])
    setup.leadingRules setup.trailingRules setup.wordRule setup.wordFirst (by simp)
    setup.wordMonomorphic.symm head setup.irreducibleBitVec setup.wordKind setup.base (U := U) (ctx := ctx)
  rw [setup.wordBody,setup.wordName] at complete
  exact complete

/-- Comparing Word with itself does not produce a nontrivial alias cast.
The structural converter therefore reaches its reflexivity case. -/
theorem AliasSetup.basic_word_refl_none (setup : AliasSetup env) :
    setup.basic U ctx wordType wordType = none := by
  have head : constantHead (setup.wordRule.definition.body.val.instL []) = some (``BitVec,[]) := by
    rw [setup.wordBody]; rfl
  obtain ⟨⟨⟨term,level⟩,correct⟩,expanded,same⟩ := expose_alias_complete
    (levels := []) setup.leadingRules setup.trailingRules setup.wordRule setup.wordFirst
    (by simp) setup.wordMonomorphic.symm head setup.irreducibleBitVec setup.wordKind
    setup.base 31 (U := U) (ctx := ctx)
  rw [setup.wordBody] at same
  dsimp only at same
  cases same
  unfold AliasSetup.basic wordType
  rw [← setup.wordName]
  simp only [AliasSetup.rules,LeanTypeReduction.conversion,expanded,bind,Option.bind,
    bitvecType,VExpr.noConfusion,reduceDIte]
  rfl

/-- The two source binder types cannot be confused by the concrete converter.
This follows from the Word abbreviation and the absence of a State unfolding
rule, rather than assuming that a compatibility test failed. -/
theorem AliasSetup.word_state_none (setup : AliasSetup env)
    (stateFresh : ∀ r ∈ setup.rules, ``HybridWord.State ≠ r.name) :
    setup.conversion 0 ctx wordType stateType = none := by
  have head : constantHead (setup.wordRule.definition.body.val.instL []) = some (``BitVec,[]) := by
    rw [setup.wordBody]; rfl
  obtain ⟨⟨⟨term,level⟩,correct⟩,expanded,same⟩ := expose_alias_complete
    (levels := []) setup.leadingRules setup.trailingRules setup.wordRule setup.wordFirst
    (by simp) setup.wordMonomorphic.symm head setup.irreducibleBitVec setup.wordKind
    setup.base 31 (U := 0) (ctx := ctx)
  rw [setup.wordBody] at same
  dsimp only at same
  cases same
  have untouched : expose setup.rules setup.base 0 ctx stateType = none :=
    expose_missing _ rfl _ stateFresh _
  simp only [AliasSetup.rules] at untouched
  have basicNone : setup.basic 0 ctx wordType stateType = none := by
    unfold AliasSetup.basic wordType
    rw [← setup.wordName]
    simp only [AliasSetup.rules,LeanTypeReduction.conversion,expanded,untouched,bind,Option.bind,
      bitvecType,stateType,VExpr.noConfusion,reduceDIte]
    simp [AliasSetup.base,arithmeticBase,LeanUniverseConversion.orElse,
      LeanTypeAliases.Alias.conversion,LeanTypeAliases.Alias.expand,
      LeanUniverseConversion.conversion,setup.wordName]
    simp only [AliasSetup.base,arithmeticBase,stateType] at untouched
    rw [untouched]
  have noWord (nested : Conversion env) : step [] nested 0 ctx setup.exposure wordType = none :=
    step_constantHead_missing _ rfl [] (by simp) nested setup.exposure
  have noState (nested : Conversion env) : step [] nested 0 ctx setup.exposure stateType = none :=
    step_constantHead_missing _ rfl [] (by simp) nested setup.exposure
  have proved : LeanStructuralConversion.prove env setup.basic setup.exposure 0 64 ctx wordType stateType = none := by
    rw [LeanStructuralConversion.prove]
    simp only [basicNone,noWord,noState,bind,Option.bind,pure,Option.pure_def]
    rfl
  simp only [AliasSetup.conversion,LeanStructuralConversion.conversion,LeanStructuralConversion.ordinary,Option.orElse_some,Option.orElse_none,basicNone,proved,
    bind,Option.bind,pure,Option.pure_def]
  rfl

/-- Function-valued locals bypass scalar/state binders. These failures follow
from their independent function type; callers do not assume a failed test. -/
theorem AliasSetup.function_state_none (setup : AliasSetup env)
    (stateFresh : ∀ r ∈ setup.rules, ``HybridWord.State ≠ r.name) :
    setup.conversion 0 ctx (.forallE domain codomain) stateType = none := by
  have noState := expose_missing (U := 0) (ctx := ctx) stateType rfl setup.rules stateFresh setup.base
  have noFunction : expose setup.rules setup.base 0 ctx (.forallE domain codomain) = none := rfl
  have noBasic : setup.basic 0 ctx (.forallE domain codomain) stateType = none := by
    simp only [AliasSetup.basic,LeanTypeReduction.conversion,noFunction,noState]
    rfl
  have proved : LeanStructuralConversion.prove env setup.basic setup.exposure 0 64 ctx
      (.forallE domain codomain) stateType = none := by
    rw [LeanStructuralConversion.prove]
    simp only [noBasic,bind,Option.bind,pure,Option.pure_def]
    rfl
  simp only [AliasSetup.conversion,LeanStructuralConversion.conversion,LeanStructuralConversion.ordinary,Option.orElse_some,Option.orElse_none,noBasic,proved,
    bind,Option.bind,pure,Option.pure_def]
  rfl

theorem AliasSetup.function_word_none (setup : AliasSetup env) :
    setup.conversion 0 ctx (.forallE domain codomain) wordType = none := by
  have head : constantHead (setup.wordRule.definition.body.val.instL []) = some (``BitVec,[]) := by
    rw [setup.wordBody]; rfl
  obtain ⟨⟨⟨term,level⟩,correct⟩,expanded,same⟩ := expose_alias_complete
    (levels := []) setup.leadingRules setup.trailingRules setup.wordRule setup.wordFirst
    (by simp) setup.wordMonomorphic.symm head setup.irreducibleBitVec setup.wordKind
    setup.base 31 (U := 0) (ctx := ctx)
  rw [setup.wordBody] at same
  dsimp only at same
  cases same
  have noFunction : expose setup.rules setup.base 0 ctx (.forallE domain codomain) = none := rfl
  have noBasic : setup.basic 0 ctx (.forallE domain codomain) wordType = none := by
    unfold AliasSetup.basic
    simp only [LeanTypeReduction.conversion,noFunction]
    unfold wordType
    rw [← setup.wordName]
    simp only [AliasSetup.rules,expanded,bitvecType,VExpr.noConfusion,reduceDIte]
    rfl
  have proved : LeanStructuralConversion.prove env setup.basic setup.exposure 0 64 ctx
      (.forallE domain codomain) wordType = none := by
    rw [LeanStructuralConversion.prove]
    simp only [noBasic,bind,Option.bind,pure,Option.pure_def]
    rfl
  simp only [AliasSetup.conversion,LeanStructuralConversion.conversion,LeanStructuralConversion.ordinary,Option.orElse_some,Option.orElse_none,noBasic,proved,
    bind,Option.bind,pure,Option.pure_def]
  rfl


private theorem prove_word_argument (setup : AliasSetup env) (name : Lean.Name)
    (notAlias : name ≠ ``outParam) (absent : ∀ r ∈ setup.rules, name ≠ r.name)
    (typed : DirectTyping env 0 ctx (.const name [.zero]) (.forallE (.sort (.succ .zero)) resultType))
    (fuel : Nat) :
    ∃ equation, LeanStructuralConversion.prove env setup.basic setup.exposure 0 (fuel+2) ctx
      (.app (.const name [.zero]) bitvecType) (.app (.const name [.zero]) wordType) = some equation ∧
      equation.type = resultType.inst bitvecType := by
  obtain ⟨fn,fnProved,fnType⟩ := LeanStructuralConversion.prove_reflexive_complete
    typed (basic_class_refl_none setup name absent) fuel setup.exposure
  obtain ⟨cast,castProved,castLevel⟩ := setup.bitvec_word (U := 0) (ctx := ctx)
  obtain ⟨arg,argProved,argType⟩ := LeanStructuralConversion.prove_base_complete
    castProved fuel setup.exposure
  rw [castLevel] at argType
  exact LeanStructuralConversion.prove_application_complete
    (leftName := name) (rightName := name) rfl rfl
    (by intro h; have := VExpr.app.inj h; cases this.2)
    (basic_class_none setup name notAlias absent bitvecType wordType)
    fn fnProved fnType arg argProved argType

/-- All arithmetic casts need at most three structural layers. Source term
size and numeral magnitude do not enter this bound. -/
theorem AliasSetup.proves (setup : AliasSetup env) (signatures : Signatures env)
    (cast : Casts ctx actual expected) (fuel : Nat) :
    ∃ equation, LeanStructuralConversion.prove env setup.basic setup.exposure 0 (fuel+3)
      ctx actual expected = some equation ∧ ∃ u, equation.type = .sort u := by
  cases cast with
  | bitvecValue =>
    obtain ⟨result,accepted,_⟩ := setup.bitvec_word (U := 0) (ctx := ctx)
    obtain ⟨equation,proved,kind⟩ := LeanStructuralConversion.prove_base_complete accepted (fuel+2) setup.exposure
    exact ⟨equation,proved,_,kind⟩
  | resultType =>
    obtain ⟨result,accepted⟩ := setup.identity.conversion_right_complete setup.identityRegistered
      (U := 0) (ctx := ctx) (u := .succ (.succ .zero)) (arg := .sort (.succ .zero))
      (by simp [VLevel.WF]) (DirectTyping.sort (by simp [VLevel.WF]))
      (LeanUniverseConversion.conversion env)
    have acceptedBase : setup.base 0 ctx (.sort (.succ .zero)) resultParameter = some result := by
      simp only [AliasSetup.base,arithmeticBase,LeanUniverseConversion.orElse,resultParameter,accepted,Option.orElse]
    obtain ⟨reduced,acceptedReduced⟩ := reduction_preserves_base setup.rules setup.base acceptedBase
    obtain ⟨equation,proved,kind⟩ := LeanStructuralConversion.prove_base_complete
      acceptedReduced (fuel+2) setup.exposure
    exact ⟨equation,proved,_,kind⟩
  | wordInstance op =>
    have classTyped : DirectTyping env 0 ctx (.const op.className [.zero])
        (.forallE (.sort (.succ .zero)) (.sort (.succ .zero))) :=
      .constant (signatures.classes op) (by simp [VLevel.WF]) rfl
    obtain ⟨equation,proved,kind⟩ := prove_word_argument setup op.className
      (by cases op <;> decide) (setup.irreducibleClass op) classTyped (fuel+1)
    exact ⟨equation,proved,_,kind⟩
  | negInstance =>
    have classTyped : DirectTyping env 0 ctx (.const ``Neg [.zero])
        (.forallE (.sort (.succ .zero)) (.sort (.succ .zero))) :=
      .constant signatures.negClass (by simp [VLevel.WF]) rfl
    obtain ⟨equation,proved,kind⟩ := prove_word_argument setup ``Neg (by decide)
      setup.irreducibleNeg classTyped (fuel+1)
    exact ⟨equation,proved,_,kind⟩
  | literalInstance n =>
    have classTyped : DirectTyping env 0 ctx (.const ``OfNat [.zero])
        (.forallE (.sort (.succ .zero)) (.forallE natType (.sort (.succ .zero)))) :=
      .constant signatures.ofNatClass (by simp [VLevel.WF]) rfl
    obtain ⟨fn,fnProved,fnType⟩ := prove_word_argument setup ``OfNat (by decide)
      setup.irreducibleOfNat classTyped fuel
    have noBase : setup.basic 0 ctx
        (LeanTyped.applications (.const ``OfNat [.zero]) [bitvecType,LeanTyped.numeral n])
        (LeanTyped.applications (.const ``OfNat [.zero]) [wordType,LeanTyped.numeral n]) = none :=
      AliasSetup.basic_no_reduction setup _ _ rfl rfl setup.irreducibleOfNat setup.irreducibleOfNat rfl
    obtain ⟨arg,argProved,argType⟩ := LeanStructuralConversion.prove_reflexive_complete
      (signatures.literals.numeral_typed (U := 0) (ctx := ctx) n)
      (numeral_basic_none setup n) (fuel+1) setup.exposure
    obtain ⟨equation,proved,kind⟩ := LeanStructuralConversion.prove_application_complete
      (leftName := ``OfNat) (rightName := ``OfNat) rfl rfl
      (by intro h; have h := (VExpr.app.inj h).1; have h := (VExpr.app.inj h).2; cases h)
      noBase fn fnProved fnType arg argProved argType
    exact ⟨equation,proved,_,kind⟩

theorem AliasSetup.covers (setup : AliasSetup env) (signatures : Signatures env) :
    Conversion.Covers setup.conversion 0 Casts := by
  intro ctx actual expected cast
  obtain ⟨equation,proved,u,kind⟩ := setup.proves signatures cast 61
  exact LeanStructuralConversion.conversion_of_prove equation proved kind

/-- Coverage also holds inside the structural converter. Thus beta checking
of source continuations can infer arithmetic bodies using the same casts. -/
theorem AliasSetup.covers_recursive (setup : AliasSetup env) (signatures : Signatures env)
    (fuel : Nat) : Conversion.Covers
      (LeanStructuralConversion.recursiveConversion env setup.basic setup.exposure (fuel+3)) 0 Casts := by
  intro ctx actual expected cast
  obtain ⟨equation,proved,u,kind⟩ := setup.proves signatures cast fuel
  exact LeanStructuralConversion.recursive_conversion_of_prove equation proved kind

/-- The source-value cast is the opposite direction to the arithmetic
instance cast, and is needed when an index uses `BitVec.toNat`. -/
theorem AliasSetup.word_bitvec (setup : AliasSetup env) :
    ∃ result, setup.basic U ctx wordType bitvecType = some result ∧ result.val = .succ .zero := by
  have head : constantHead (setup.wordRule.definition.body.val.instL []) = some (``BitVec,[]) := by
    rw [setup.wordBody]; rfl
  have complete := conversion_alias_left_exact (levels := [])
    setup.leadingRules setup.trailingRules setup.wordRule setup.wordFirst (by simp)
    setup.wordMonomorphic.symm head setup.irreducibleBitVec setup.wordKind setup.base (U := U) (ctx := ctx)
  rw [setup.wordBody,setup.wordName] at complete
  exact complete

private theorem AliasSetup.base_alias (setup : AliasSetup env)
    (accepted : setup.identity.conversion setup.identityRegistered
      (LeanUniverseConversion.conversion env) U ctx a b = some result) :
    setup.base U ctx a b = some result := by
  simp only [AliasSetup.base,arithmeticBase,LeanUniverseConversion.orElse,accepted,Option.orElse]

/-- Universe conversion needed by the fixed equality alias, independent of
source parsing or the structural converter's success. -/
theorem AliasSetup.base_universe (setup : AliasSetup env)
    (left : u.WF 0) (right : v.WF 0) (same : u.eval [] = v.eval []) :
    ∃ result, setup.base 0 ctx (.sort u) (.sort v) = some result := by
  obtain ⟨result,accepted⟩ := LeanUniverseConversion.conversion_complete left right same env 0 ctx
  exact ⟨result,by simpa only [AliasSetup.base,arithmeticBase,LeanUniverseConversion.orElse,
    LeanTypeAliases.Alias.conversion,LeanTypeAliases.Alias.expand,bind,Option.bind,Option.orElse] using accepted⟩

/-- Only the standard Boolean instance is exposed here. Its body and both
checks are derived from fixed library declarations. -/
theorem AliasSetup.decision_step (setup : AliasSetup env)
    (equality : env.constants ``Eq = some eqSignature)
    (decidable : env.constants ``Decidable = some decidableSignature)
    (boolean : env.constants ``Bool = some ⟨0,.sort (.succ .zero)⟩) :
    ∃ result, step setup.rules setup.base 0 ctx (noExposure env)
      (.app (.const ``DecidableEq [.succ .zero]) boolType) = some result ∧
      result.val = (decEqFunction boolType,.sort (.max (.succ .zero) (.succ .zero))) := by
  obtain ⟨beforeRules,r,afterRules,rulesEq,name,arity,body,kind,first⟩ := setup.decEqView
  have unfolded := unfoldConstant_present beforeRules afterRules r first
    (levels := [.succ .zero]) (U := 0) (ctx := ctx) (by simp [VLevel.WF]) (by simp [arity])
  change setup.rules = _ at rulesEq
  simp only [← rulesEq,body,kind] at unfolded
  have unfolded : ∃ result, unfoldConstant setup.rules 0 ctx ``DecidableEq [.succ .zero] = some result ∧
      result.val = (decEqBody,decEqKind) :=
    (congrArg (fun n => ∃ result, unfoldConstant setup.rules 0 ctx n [.succ .zero] = some result ∧
      result.val = (decEqBody,decEqKind)) name).mp unfolded
  obtain ⟨⟨⟨value,ty⟩,correct⟩,unfolded,same⟩ := unfolded
  dsimp only at same
  cases same
  have booleanTyped : DirectTyping env 0 ctx boolType (.sort (.succ .zero)) :=
    .constant boolean (by simp) rfl
  obtain ⟨argProof,argChecked⟩ := booleanTyped.check_complete setup.base (noExposure env)
  let universeCast : TypeCasts := fun _ a b =>
    a = .sort (.imax (.succ .zero) (.imax (.succ .zero) (.succ .zero))) ∧
    b = .sort (.max (.succ .zero) (.succ .zero))
  have coverage : Conversion.Covers setup.base 0 universeCast := by
    intro scope a b cast
    rcases cast with ⟨rfl,rfl⟩
    exact setup.base_universe (by simp [VLevel.WF]) (by simp [VLevel.WF]) rfl
  have tailTyped : CheckedTyping env 0 universeCast (.sort (.succ .zero)::ctx)
      (decEqFunction (.bvar 0)) (.sort (.max (.succ .zero) (.succ .zero))) :=
    .converted ((decEqTail_typed equality decidable).withCasts universeCast) ⟨rfl,rfl⟩
  obtain ⟨tailProof,tailChecked⟩ := tailTyped.check_complete
    (known := noKnownTypes env 0) (by intro _ _ _ h; cases h) coverage (noExposure env)
  simp only [step,unfolded,decEqBody,decEqKind,bind,Option.bind,argChecked,
    dif_pos rfl,dite_true,tailChecked,pure,Option.pure_def]
  exact ⟨_,rfl,rfl⟩

theorem AliasSetup.decision_function (setup : AliasSetup env)
    (equality : env.constants ``Eq = some eqSignature)
    (decidable : env.constants ``Decidable = some decidableSignature)
    (boolean : env.constants ``Bool = some ⟨0,.sort (.succ .zero)⟩) :
    ∃ result, setup.basic 0 ctx (.app (.const ``DecidableEq [.succ .zero]) boolType)
      (decEqFunction boolType) = some result := by
  obtain ⟨⟨⟨value,ty⟩,correct⟩,stepped,same⟩ := setup.decision_step equality decidable boolean (ctx := ctx)
  dsimp only at same
  cases same
  have stopped : step setup.rules setup.base 0 ctx (noExposure env) (decEqFunction boolType) = none := rfl
  have reduced : ∃ result, reduce setup.rules setup.base 0 ctx (noExposure env) 32
      (.app (.const ``DecidableEq [.succ .zero]) boolType) = some result ∧
      result.val = (decEqFunction boolType,.sort (.max (.succ .zero) (.succ .zero))) := by
    rw [reduce]
    simp only [stepped,reduce_missing stopped,bind,Option.bind]
    exact ⟨_,rfl,rfl⟩
  obtain ⟨⟨⟨value,ty⟩,correct⟩,reduced,same⟩ := reduced
  dsimp only at same
  cases same
  have exposed : ∃ result, expose setup.rules setup.base 0 ctx
      (.app (.const ``DecidableEq [.succ .zero]) boolType) = some result ∧
      result.val = (decEqFunction boolType,.max (.succ .zero) (.succ .zero)) := by
    simp only [expose,reduced,bind,Option.bind,pure]
    exact ⟨_,rfl,rfl⟩
  obtain ⟨⟨⟨value,u⟩,proof⟩,expanded,same⟩ := exposed
  dsimp only at same
  cases same
  simp only [AliasSetup.basic,LeanTypeReduction.conversion,expanded,bind,Option.bind,dif_pos rfl,pure]
  exact ⟨_,rfl⟩

/-- Only a type-parameter sort needs conversion in a closed arithmetic class
application. This fixed alias is accepted by the base converter itself. -/
def ParameterCast : TypeCasts := fun _ actual expected =>
  actual = .sort (.succ .zero) ∧ expected = resultParameter

theorem AliasSetup.parameter_covered (setup : AliasSetup env) :
    Conversion.Covers setup.basic 0 ParameterCast := by
  intro ctx actual expected h
  rcases h with ⟨rfl,rfl⟩
  obtain ⟨result,accepted⟩ := setup.identity.conversion_right_complete setup.identityRegistered
    (U := 0) (ctx := ctx) (u := .succ (.succ .zero)) (arg := .sort (.succ .zero))
    (by simp [VLevel.WF]) (DirectTyping.sort (by simp [VLevel.WF]))
    (LeanUniverseConversion.conversion env)
  exact reduction_preserves_base setup.rules setup.base (setup.base_alias accepted)

theorem AliasSetup.spelling_proved (setup : AliasSetup env) (library : Signatures env)
    (left : WordSpelling a) (right : WordSpelling b) (fuel : Nat) :
    ∃ eq, LeanStructuralConversion.prove env setup.basic setup.exposure 0 (fuel+1) ctx a b = some eq ∧
      eq.type = .sort (.succ .zero) := by
  cases left <;> cases right
  · exact LeanStructuralConversion.prove_reflexive_complete
      (.constant library.word (by simp) rfl) setup.basic_word_refl_none fuel setup.exposure
  · obtain ⟨cast,done,ty⟩ := setup.word_bitvec (U := 0) (ctx := ctx)
    obtain ⟨eq,done,tyEq⟩ := LeanStructuralConversion.prove_base_complete done fuel setup.exposure
    exact ⟨eq,done,by rw [tyEq,ty]⟩
  · obtain ⟨cast,done,ty⟩ := setup.bitvec_word (U := 0) (ctx := ctx)
    obtain ⟨eq,done,tyEq⟩ := LeanStructuralConversion.prove_base_complete done fuel setup.exposure
    exact ⟨eq,done,by rw [tyEq,ty]⟩
  · exact LeanStructuralConversion.prove_reflexive_complete library.bitvec_typed
      (setup.basic_no_reduction _ _ rfl rfl setup.irreducibleBitVec setup.irreducibleBitVec rfl) fuel setup.exposure

private theorem annotated_application
    (setup : AliasSetup env)
    (leftHead : constantHead fa = some (name,levels)) (rightHead : constantHead fb = some (name,levels))
    (absent : ∀ r ∈ setup.rules, name ≠ r.name) (notAlias : name ≠ ``outParam)
    (leftTyped : CastTyping env 0 ParameterCast ctx (.app fa xa) (codomain.inst xa))
    (function : LeanStructuralConversion.Equation env 0 ctx fa fb)
    (hf : LeanStructuralConversion.prove env setup.basic setup.exposure 0 fuel ctx fa fb = some function)
    (tf : function.type = .forallE domain codomain)
    (argument : LeanStructuralConversion.Equation env 0 ctx xa xb)
    (ha : LeanStructuralConversion.prove env setup.basic setup.exposure 0 fuel ctx xa xb = some argument)
    (ta : argument.type = domain ∨ ParameterCast ctx argument.type domain) :
    ∃ result, LeanStructuralConversion.prove env setup.basic setup.exposure 0 (fuel+1) ctx
      (.app fa xa) (.app fb xb) = some result ∧ result.type = codomain.inst xa := by
  have noBase : setup.basic 0 ctx (.app fa xa) (.app fb xb) = none :=
    setup.basic_values_none (ty := wordType)
      (.constant (show constantHead (.app fa xa) = _ from leftHead) absent notAlias)
      (.constant (show constantHead (.app fb xb) = _ from rightHead) absent notAlias)
      (by intro u h; cases h)
  by_cases same : VExpr.app fa xa = .app fb xb
  · rw [← same] at noBase ⊢
    exact LeanStructuralConversion.prove_reflexive_cast_complete leftTyped noBase
      (LeanStructuralConversion.recursive_covers_base setup.parameter_covered fuel setup.exposure)
  · apply LeanStructuralConversion.prove_application_cast_complete leftHead rightHead same noBase
      function hf tf argument ha
    intro unequal
    cases ta with
    | inl h => exact False.elim (unequal h)
    | inr h => exact LeanStructuralConversion.recursive_covers_base setup.parameter_covered fuel setup.exposure _ _ _ h

/-- Three fixed class arguments use four congruence levels. Arbitrary operand
expressions do not occur in this closed type conversion. -/
theorem AliasSetup.heterogeneous_proved (setup : AliasSetup env) (library : Signatures env)
    (op : Binary) (a : WordSpelling a1) (b : WordSpelling b1) (c : WordSpelling c1)
    (d : WordSpelling a2) (e : WordSpelling b2) (f : WordSpelling c2) (fuel : Nat) :
    ∃ eq, LeanStructuralConversion.prove env setup.basic setup.exposure 0 (fuel+4) ctx
      (op.classApplication a1 b1 c1) (op.classApplication a2 b2 c2) = some eq ∧
      eq.type = .sort (.max (.max (.succ .zero) (.succ .zero)) (.succ .zero)) := by
  let resultSort : VExpr := .sort (.max (.max (.succ .zero) (.succ .zero)) (.succ .zero))
  have headTyped : DirectTyping env 0 ctx (.const op.heterogeneous [.zero,.zero,.zero])
      (.forallE (.sort (.succ .zero)) (.forallE (.sort (.succ .zero)) (.forallE resultParameter resultSort))) :=
    .constant (library.heterogeneous op) (by simp [VLevel.WF]) rfl
  have noBase : setup.basic 0 ctx (.const op.heterogeneous [.zero,.zero,.zero])
      (.const op.heterogeneous [.zero,.zero,.zero]) = none := by
    apply setup.basic_no_reduction _ _ rfl rfl (setup.irreducibleHeterogeneous op) (setup.irreducibleHeterogeneous op)
    cases op <;> rfl
  obtain ⟨h,hh,th⟩ := LeanStructuralConversion.prove_reflexive_complete headTyped noBase fuel setup.exposure
  obtain ⟨aa,ha,ta⟩ := setup.spelling_proved library a d fuel
  have aTyped := DirectTyping.application headTyped (a.typed library)
  have typeA : (VExpr.forallE (.sort (.succ .zero)) (.forallE resultParameter resultSort)).inst a1 =
      .forallE (.sort (.succ .zero)) (.forallE resultParameter resultSort) := rfl
  obtain ⟨h1,hh1,th1⟩ := annotated_application setup (name := op.heterogeneous) rfl rfl
    (setup.irreducibleHeterogeneous op) (by cases op <;> decide)
    (aTyped.withCasts ParameterCast) h hh th aa ha (.inl ta)
  rw [typeA] at th1
  obtain ⟨bb,hb,tb⟩ := setup.spelling_proved library b e (fuel+1)
  change DirectTyping env 0 ctx _ (.forallE (.sort (.succ .zero)) (.forallE resultParameter resultSort)) at aTyped
  have bTyped := DirectTyping.application aTyped (b.typed library)
  obtain ⟨h2,hh2,th2⟩ := annotated_application setup (name := op.heterogeneous) rfl rfl
    (setup.irreducibleHeterogeneous op) (by cases op <;> decide)
    (bTyped.withCasts ParameterCast) h1 hh1 th1 bb hb (.inl tb)
  have typeB : (VExpr.forallE resultParameter resultSort).inst b1 = .forallE resultParameter resultSort := rfl
  change h2.type = .forallE resultParameter resultSort at th2
  change DirectTyping env 0 ctx _ (.forallE resultParameter resultSort) at bTyped
  obtain ⟨cc,hc,tc⟩ := setup.spelling_proved library c f (fuel+2)
  have cTyped := CastTyping.convertedApplication (bTyped.withCasts ParameterCast)
    ((c.typed library).withCasts ParameterCast) (show ParameterCast ctx (.sort (.succ .zero)) resultParameter from ⟨rfl,rfl⟩)
  obtain ⟨h3,hh3,th3⟩ := annotated_application setup (name := op.heterogeneous) rfl rfl
    (setup.irreducibleHeterogeneous op) (by cases op <;> decide)
    cTyped h2 hh2 th2 cc hc (.inr ⟨tc,rfl⟩)
  exact ⟨h3,hh3,th3⟩

theorem AliasSetup.proves_source (setup : AliasSetup env) (signatures : Signatures env)
    (closed : ClosedConstantTypes env) (cast : SourceCasts env ctx actual expected) (fuel : Nat) :
    ∃ equation, LeanStructuralConversion.prove env setup.basic setup.exposure 0 (fuel+4)
      ctx actual expected = some equation ∧ ∃ u, equation.type = .sort u := by
  cases cast with
  | heterogeneous op a b c d e f =>
    obtain ⟨eq,done,ty⟩ := setup.heterogeneous_proved signatures op a b c d e f fuel
    exact ⟨eq,done,_,ty⟩
  | arithmetic cast => exact setup.proves signatures cast (fuel+1)
  | readDictionary d =>
    have signatureClosed : (VExpr.forallE resultParameter
        (.forallE (.app (.const ``outParam [d.annotation]) d.domain) (.sort d.resultKind))).ClosedN 0 :=
      ⟨by trivial,⟨⟨by trivial,d.domainClosed.mono (by decide)⟩,by trivial⟩⟩
    have prefixTyped := d.prefixTyped.in_context closed signatureClosed ctx
    have noReduction {a b : VExpr} (ha : constantHead a = some (``GetElem?, d.levels))
        (hb : constantHead b = some (``GetElem?, d.levels)) : setup.basic 0 ctx a b = none :=
      setup.basic_values_none (ty := wordType)
        (.constant ha setup.irreducibleReadClass (by decide))
        (.constant hb setup.irreducibleReadClass (by decide)) (by intro u h; cases h)
    have prefixNone : setup.basic 0 ctx d.function d.function = none :=
      noReduction d.head d.head
    obtain ⟨prefixEq,hprefix,tprefix⟩ := LeanStructuralConversion.prove_reflexive_complete
      prefixTyped prefixNone (fuel+1) setup.exposure
    obtain ⟨wordCast,hword,wordKind⟩ := setup.word_bitvec (U := 0) (ctx := ctx)
    obtain ⟨wordEq,harg,targ⟩ := LeanStructuralConversion.prove_base_complete hword (fuel+1) setup.exposure
    rw [wordKind] at targ
    obtain ⟨parameter,hparameter⟩ := setup.identity.conversion_right_complete setup.identityRegistered
      (U := 0) (ctx := ctx) (u := .succ (.succ .zero)) (arg := .sort (.succ .zero))
      (by simp [VLevel.WF]) (DirectTyping.sort (by simp [VLevel.WF]))
      (LeanUniverseConversion.conversion env)
    have baseParameter : setup.base 0 ctx (.sort (.succ .zero)) resultParameter = some parameter := by
      simp only [AliasSetup.base,arithmeticBase,LeanUniverseConversion.orElse,resultParameter,hparameter,Option.orElse]
    obtain ⟨parameter,accepted⟩ := reduction_preserves_base setup.rules setup.base baseParameter
    change setup.basic 0 ctx (.sort (.succ .zero)) resultParameter = some parameter at accepted
    have ready : ∃ cast, LeanStructuralConversion.recursiveConversion env setup.basic setup.exposure ((fuel+1)+1) 0 ctx (.sort (.succ .zero)) resultParameter = some cast := by
      simp only [LeanStructuralConversion.recursiveConversion,LeanStructuralConversion.withSearch,accepted,bind,Option.bind]
      exact ⟨_,rfl⟩
    obtain ⟨cast,hcast⟩ := ready
    obtain ⟨applied,happlied,tapplied⟩ := LeanStructuralConversion.prove_application_cast_complete
      (leftName := ``GetElem?) (rightName := ``GetElem?) d.head d.head
      (by intro h; cases (VExpr.app.inj h).2)
      (noReduction d.head d.head)
      prefixEq hprefix tprefix wordEq harg (fun _ => by rw [targ]; exact ⟨cast,hcast⟩)
    have predicateTyped := d.predicateTyped.in_context closed d.domainClosed ctx
    have predicateNone : setup.basic 0 ctx d.predicate d.predicate = none := by
      obtain ⟨a,b,h⟩ := d.predicateLambda
      rw [h]; rfl
    obtain ⟨predicateEq,hpredicate,tpredicate⟩ := LeanStructuralConversion.prove_reflexive_complete
      predicateTyped predicateNone ((fuel+1)+1) setup.exposure
    obtain ⟨parameter,hparameter⟩ := setup.identity.conversion_right_universe_complete setup.identityRegistered
      (d.domainTyped.in_context closed (by trivial) ctx) d.kindClosed d.annotationClosed d.sameKind
    obtain ⟨parameter,accepted⟩ := reduction_preserves_base setup.rules setup.base (setup.base_alias hparameter)
    change setup.basic 0 ctx d.domain (.app (.const ``outParam [d.annotation]) d.domain) = some parameter at accepted
    have ready : ∃ cast, LeanStructuralConversion.recursiveConversion env setup.basic setup.exposure ((fuel+1)+2) 0 ctx d.domain (.app (.const ``outParam [d.annotation]) d.domain) = some cast := by
      simp only [LeanStructuralConversion.recursiveConversion,LeanStructuralConversion.withSearch,accepted,bind,Option.bind]
      exact ⟨_,rfl⟩
    obtain ⟨cast,hcast⟩ := ready
    have appliedType : applied.type = .forallE (.app (.const ``outParam [d.annotation]) d.domain) (.sort d.resultKind) := by
      simpa only [VExpr.inst,d.domainClosed.instN_eq (Nat.zero_le _)] using tapplied
    obtain ⟨equation,proved,kind⟩ := LeanStructuralConversion.prove_application_cast_complete
      (fa := .app d.function wordType) (fb := .app d.function bitvecType)
      (leftName := ``GetElem?) (rightName := ``GetElem?) d.head d.head
      (by intro h; cases (VExpr.app.inj (VExpr.app.inj h).1).2)
      (noReduction d.head d.head)
      applied happlied appliedType predicateEq hpredicate
      (fun _ => by rw [tpredicate]; exact ⟨cast,hcast⟩)
    exact ⟨equation,proved,_,kind⟩
  | decisionInstance declared =>
    cases accepted : setup.basic 0 ctx (.app (.const ``DecidableEq [.succ .zero]) bitvecType)
        (.app (.const ``DecidableEq [.succ .zero]) wordType) with
    | some result =>
      obtain ⟨equation,proved,kind⟩ := LeanStructuralConversion.prove_base_complete accepted ((fuel+1)+2) setup.exposure
      exact ⟨equation,proved,_,kind⟩
    | none =>
      have header : DirectTyping env 0 ctx (.const ``DecidableEq [.succ .zero]) decEqKind :=
        .constant declared (by simp [VLevel.WF]) rfl
      have form : ValueForm setup ctx (.const ``DecidableEq [.succ .zero]) decEqKind :=
        .declaredConstant declared (by decide)
      have baseNone := setup.basic_values_none form form (by intro u; simp [decEqKind])
      obtain ⟨fn,hfn,tfn⟩ := LeanStructuralConversion.prove_reflexive_complete header baseNone ((fuel+1)+1) setup.exposure
      obtain ⟨cast,hcast,kind⟩ := setup.bitvec_word (U := 0) (ctx := ctx)
      obtain ⟨arg,harg,targ⟩ := LeanStructuralConversion.prove_base_complete hcast ((fuel+1)+1) setup.exposure
      rw [kind] at targ
      obtain ⟨equation,proved,typed⟩ := LeanStructuralConversion.prove_application_complete
        (leftName := ``DecidableEq) (rightName := ``DecidableEq) rfl rfl
        (by intro h; cases (VExpr.app.inj h).2) accepted fn hfn tfn arg harg targ
      exact ⟨equation,proved,_,typed⟩
  | decisionFunction equality decidable boolean =>
    obtain ⟨result,accepted⟩ := setup.decision_function equality decidable boolean (ctx := ctx)
    obtain ⟨equation,proved,kind⟩ := LeanStructuralConversion.prove_base_complete accepted ((fuel+1)+2) setup.exposure
    exact ⟨equation,proved,_,kind⟩
  | wordValue =>
    obtain ⟨result,accepted,_⟩ := setup.word_bitvec (U := 0) (ctx := ctx)
    obtain ⟨equation,proved,kind⟩ := LeanStructuralConversion.prove_base_complete accepted ((fuel+1)+2) setup.exposure
    exact ⟨equation,proved,_,kind⟩
  | wordOption declared =>
    have header : DirectTyping env 0 ctx (.const ``Option [.zero])
        (.forallE (.sort (.succ .zero)) (.sort (.succ .zero))) :=
      .constant declared (by simp [VLevel.WF]) rfl
    obtain ⟨fn,hfn,tfn⟩ := LeanStructuralConversion.prove_reflexive_complete header
      (basic_class_refl_none setup ``Option setup.irreducibleOption) ((fuel+1)+1) setup.exposure
    obtain ⟨cast,hcast,kind⟩ := setup.word_bitvec (U := 0) (ctx := ctx)
    obtain ⟨arg,harg,targ⟩ := LeanStructuralConversion.prove_base_complete hcast ((fuel+1)+1) setup.exposure
    rw [kind] at targ
    obtain ⟨equation,proved,typed⟩ := LeanStructuralConversion.prove_application_complete
      (leftName := ``Option) (rightName := ``Option) rfl rfl
      (by intro h; cases (VExpr.app.inj h).2)
      (basic_class_none setup ``Option (by decide) setup.irreducibleOption wordType bitvecType)
      fn hfn tfn arg harg targ
    exact ⟨equation,proved,_,typed⟩
  | bitvecOption declared =>
    have header : DirectTyping env 0 ctx (.const ``Option [.zero])
        (.forallE (.sort (.succ .zero)) (.sort (.succ .zero))) :=
      .constant declared (by simp [VLevel.WF]) rfl
    obtain ⟨fn,hfn,tfn⟩ := LeanStructuralConversion.prove_reflexive_complete header
      (basic_class_refl_none setup ``Option setup.irreducibleOption) ((fuel+1)+1) setup.exposure
    obtain ⟨cast,hcast,kind⟩ := setup.bitvec_word (U := 0) (ctx := ctx)
    obtain ⟨arg,harg,targ⟩ := LeanStructuralConversion.prove_base_complete hcast ((fuel+1)+1) setup.exposure
    rw [kind] at targ
    obtain ⟨equation,proved,typed⟩ := LeanStructuralConversion.prove_application_complete
      (leftName := ``Option) (rightName := ``Option) rfl rfl
      (by intro h; cases (VExpr.app.inj h).2)
      (basic_class_none setup ``Option (by decide) setup.irreducibleOption bitvecType wordType)
      fn hfn tfn arg harg targ
    exact ⟨equation,proved,_,typed⟩
  | wordFunction resultTyped =>
    obtain ⟨cast,hcast,kind⟩ := setup.bitvec_word (U := 0) (ctx := ctx)
    obtain ⟨domain,hdomain,tdomain⟩ := LeanStructuralConversion.prove_base_complete hcast ((fuel+1)+1) setup.exposure
    rw [kind] at tdomain
    have typed := resultTyped.in_context closed (by trivial) (bitvecType::ctx)
    have absent {valueType : VExpr} : setup.basic 0 (bitvecType::ctx) (optionType valueType) (optionType valueType) = none :=
      setup.basic_no_reduction _ _ rfl rfl setup.irreducibleOption setup.irreducibleOption rfl
    obtain ⟨body,hbody,tbody⟩ := LeanStructuralConversion.prove_reflexive_complete typed absent ((fuel+1)+1) setup.exposure
    obtain ⟨equation,proved,kind⟩ := LeanStructuralConversion.prove_forall_complete
      (by intro h; cases (VExpr.forallE.inj h).1)
      (show setup.basic 0 ctx (.forallE bitvecType _) (.forallE wordType _) = none from rfl)
      domain hdomain tdomain body hbody tbody
    exact ⟨equation,proved,_,kind⟩
  | levelEquality actualClosed expectedClosed sameUniverse =>
    obtain ⟨result,accepted⟩ := LeanUniverseConversion.conversion_complete
      actualClosed expectedClosed sameUniverse env 0 ctx
    have baseAccepted : setup.base 0 ctx _ _ = some result := by
      simpa only [AliasSetup.base,arithmeticBase,LeanUniverseConversion.orElse,
        LeanTypeAliases.Alias.conversion,LeanTypeAliases.Alias.expand,bind,Option.bind,Option.orElse] using accepted
    obtain ⟨reduced,reducedAccepted⟩ := reduction_preserves_base setup.rules setup.base baseAccepted
    obtain ⟨equation,proved,kind⟩ := LeanStructuralConversion.prove_base_complete reducedAccepted ((fuel+1)+2) setup.exposure
    exact ⟨equation,proved,_,kind⟩
  | parameter argument typed actualClosed expectedClosed sameUniverse =>
    obtain ⟨result,accepted⟩ := setup.identity.conversion_right_universe_complete setup.identityRegistered
      (typed.in_context closed (by trivial) ctx) actualClosed expectedClosed sameUniverse
    obtain ⟨reduced,reducedAccepted⟩ := reduction_preserves_base setup.rules setup.base (setup.base_alias accepted)
    obtain ⟨equation,proved,kind⟩ := LeanStructuralConversion.prove_base_complete reducedAccepted ((fuel+1)+2) setup.exposure
    exact ⟨equation,proved,_,kind⟩

theorem AliasSetup.covers_source (setup : AliasSetup env) (signatures : Signatures env)
    (closed : ClosedConstantTypes env) : Conversion.Covers setup.conversion 0 (SourceCasts env) := by
  intro ctx actual expected cast
  obtain ⟨equation,proved,u,kind⟩ := setup.proves_source signatures closed cast 60
  exact LeanStructuralConversion.conversion_of_prove equation proved kind

theorem AliasSetup.covers_source_ordinary (setup : AliasSetup env) (signatures : Signatures env)
    (closed : ClosedConstantTypes env) : Conversion.Covers
      (LeanStructuralConversion.ordinary env setup.basic setup.exposure) 0 (SourceCasts env) := by
  intro ctx actual expected cast
  obtain ⟨equation,proved,u,kind⟩ := setup.proves_source signatures closed cast 60
  exact LeanStructuralConversion.ordinary_of_prove equation proved kind

theorem AliasSetup.covers_source_recursive (setup : AliasSetup env) (signatures : Signatures env)
    (closed : ClosedConstantTypes env) (fuel : Nat) : Conversion.Covers
      (LeanStructuralConversion.recursiveConversion env setup.basic setup.exposure (fuel+4)) 0 (SourceCasts env) := by
  intro ctx actual expected cast
  obtain ⟨equation,proved,u,kind⟩ := setup.proves_source signatures closed cast fuel
  exact LeanStructuralConversion.recursive_conversion_of_prove equation proved kind

/-- Applying an abstracted continuation to its own variable is one beta step.
This proof is shared by body certificates and `for`-body normalization. -/
def continuationValue (domain value : VExpr) : VExpr :=
  .app (.lam domain (value.liftN 1 1)) (.bvar 0)

theorem continuationValue_ne (domain value : VExpr) : value ≠ continuationValue domain value := by
  intro same
  have bound := VExpr.sizeOf_liftN (n := 1) value 1
  have sized := congrArg sizeOf same
  change sizeOf value = 1 + (1 + sizeOf domain + sizeOf (value.liftN 1 1)) +
    (1 + sizeOf (0 : Nat)) at sized
  omega

theorem AliasSetup.value_beta_proved (setup : AliasSetup env) (signatures : Signatures env)
    (closed : ClosedConstantTypes env) (domainClosed : domain.ClosedN 0)
    (resultClosed : resultType.ClosedN 0) (notSort : ∀ u, resultType ≠ .sort u)
    (typed : CastTyping env 0 (SourceCasts env) (domain::ctx) value resultType)
    (form : ValueForm setup (domain::ctx) value resultType) (fuel : Nat) :
    ∃ equation, LeanStructuralConversion.prove env setup.basic setup.exposure 0 (fuel+5) (domain::ctx)
      value (continuationValue domain value) = some equation ∧ equation.type = resultType := by
  have lifted : CastTyping env 0 (SourceCasts env) (domain::domain::ctx)
      (value.liftN 1 1) resultType := by
    simpa only [domainClosed.liftN_eq (Nat.zero_le _),resultClosed.liftN_eq (Nat.zero_le _)] using
      typed.weakN closed SourceCasts.closed (Ctx.LiftN.succ Ctx.LiftN.one)
  have argument : CastTyping env 0 (SourceCasts env) (domain::ctx) (.bvar 0) domain := by
    simpa only [domainClosed.lift_eq] using (CastTyping.bvar (casts := SourceCasts env)
      (env := env) (U := 0) (Lookup.zero (ty := domain) (Γ := ctx)))
  have unbeta : (value.liftN 1 1).inst (.bvar 0) = value := VExpr.instN_bvar0 value 0
  have substituted : ValueForm setup (domain::ctx)
      ((value.liftN 1 1).inst (.bvar 0)) (resultType.inst (.bvar 0)) := by
    simpa only [unbeta,resultClosed.instN_eq (Nat.zero_le _)] using form
  have notAlias := setup.basic_beta_none lifted (arg := .bvar 0)
    (by simpa only [resultClosed.instN_eq (Nat.zero_le _)] using notSort) substituted
  have complete := LeanStructuralConversion.prove_beta_right_cast_complete lifted argument
    (setup.covers_source_recursive signatures closed fuel)
    (by intro result step; exact substituted.step_kind _ _ step)
    (by simpa only [unbeta] using continuationValue_ne domain value) notAlias
  obtain ⟨equation,proved,kind⟩ := LeanStructuralConversion.prove_left_congr unbeta complete
  exact ⟨equation,proved,by simpa only [resultClosed.instN_eq (Nat.zero_le _)] using kind⟩

/-- A lexical let substitutes an already typed scalar value. Its one beta
step has a fixed conversion depth, independently of the surrounding syntax. -/
theorem AliasSetup.scalar_beta_checked_domain_types {body arg : VExpr} (setup : AliasSetup env) (signatures : Signatures env)
    (closed : ClosedConstantTypes env)
    (domainTyped : DirectTyping env 0 ctx domain (.sort (.succ .zero)))
    (resultClosed : resultType.ClosedN 0) (notSort : ∀ u, resultType ≠ .sort u)
    (bodyTyped : CastTyping env 0 (SourceCasts env) (domain::ctx) body resultType)
    (argTyped : CheckedTyping env 0 (SourceCasts env) ctx arg domain)
    (leftNotSort : ∀ u, leftType ≠ .sort u)
    (form : ValueForm setup ctx (body.inst arg) leftType) (fuel : Nat) :
    ∃ equation, LeanStructuralConversion.prove env setup.basic setup.exposure 0 (fuel+5) ctx
      (body.inst arg) (.app (.lam domain body) arg) = some equation ∧ (equation.type = leftType ∨ equation.type = resultType) := by
  have sourceForm : ValueForm setup ctx (.app (.lam domain body) arg) resultType := by
    simpa only [resultClosed.instN_eq (Nat.zero_le _)] using (ValueForm.beta (setup := setup) bodyTyped (arg := arg))
  have noAlias := setup.basic_values_none_of_types form sourceForm leftNotSort notSort
  by_cases same : body.inst arg = .app (.lam domain body) arg
  · have applied := CastTyping.checkedApplication (.lambda (domainTyped.withCasts _) bodyTyped) argTyped
    have substituted : CastTyping env 0 (SourceCasts env) ctx (body.inst arg) resultType := by
      simpa only [← same,resultClosed.instN_eq (Nat.zero_le _)] using applied
    have notAlias : setup.basic 0 ctx (body.inst arg) (body.inst arg) = none := by
      exact (congrArg (fun rhs => setup.basic 0 ctx (body.inst arg) rhs = none) same).mpr noAlias
    obtain ⟨equation,success,kind⟩ := LeanStructuralConversion.prove_reflexive_cast_complete substituted
      notAlias (setup.covers_source_recursive signatures closed fuel)
    exact (congrArg (fun rhs => ∃ e : LeanStructuralConversion.Equation env 0 ctx (body.inst arg) rhs,
      LeanStructuralConversion.prove env setup.basic setup.exposure 0 (fuel+5) ctx
        (body.inst arg) rhs = some e ∧ (e.type = leftType ∨ e.type = resultType)) same).mp ⟨equation,success,Or.inr kind⟩
  · have coverage := setup.covers_source_recursive signatures closed fuel
    obtain ⟨right,stepped,value⟩ := LeanTypeReduction.step_beta_checked_complete bodyTyped argTyped coverage [] setup.exposure
    obtain ⟨equation,success,kind⟩ := LeanStructuralConversion.prove_reduction_right_complete_types
      right stepped (congrArg Prod.fst value) (congrArg Prod.snd value)
      (fun result h => form.step_kind _ _ h) same noAlias
    exact ⟨equation,success,by simpa only [resultClosed.instN_eq (Nat.zero_le _)] using kind⟩

theorem AliasSetup.scalar_beta_checked_domain_proved {body arg : VExpr} (setup : AliasSetup env) (signatures : Signatures env)
    (closed : ClosedConstantTypes env)
    (domainTyped : DirectTyping env 0 ctx domain (.sort (.succ .zero)))
    (resultClosed : resultType.ClosedN 0) (notSort : ∀ u, resultType ≠ .sort u)
    (bodyTyped : CastTyping env 0 (SourceCasts env) (domain::ctx) body resultType)
    (argTyped : CheckedTyping env 0 (SourceCasts env) ctx arg domain)
    (form : ValueForm setup ctx (body.inst arg) resultType) (fuel : Nat) :
    ∃ equation, LeanStructuralConversion.prove env setup.basic setup.exposure 0 (fuel+5) ctx
      (body.inst arg) (.app (.lam domain body) arg) = some equation ∧ equation.type = resultType := by
  obtain ⟨equation,success,kind⟩ := setup.scalar_beta_checked_domain_types signatures closed
    domainTyped resultClosed notSort bodyTyped argTyped notSort form fuel
  exact ⟨equation,success,kind.elim id id⟩

/-- A helper's entire argument spine reduces in the existing weak-head
step. Arity does not consume the converter's search budget. All premises are
source typing/shape, never reduction or parser success. -/
theorem AliasSetup.helper_proved {body : VExpr} (setup : AliasSetup env)
    (signatures : Signatures env) (closed : ClosedConstantTypes env)
    (bodyTyped : CastTyping env 0 (SourceCasts env) (domain::ctx) body bodyType)
    (argument : CastTyping env 0 (SourceCasts env) ctx arg domain)
    (arguments : ArgumentsCasts env 0 (SourceCasts env) ctx (bodyType.inst arg) args resultType)
    (form : ValueForm setup ctx (args.foldl applyReduced (body.inst arg)) resultType)
    (notSort : ∀ u, resultType ≠ .sort u) (fuel : Nat) :
    ∃ equation, LeanStructuralConversion.prove env setup.basic setup.exposure 0 (fuel+5) ctx
      (args.foldl applyReduced (body.inst arg))
      (LeanTyped.applications (.app (.lam domain body) arg) args) = some equation ∧
      equation.type = resultType := by
  have coverage := setup.covers_source_recursive signatures closed fuel
  obtain ⟨first,firstStep,firstValue⟩ := step_beta_cast_complete bodyTyped argument coverage [] setup.exposure
  have typed : CastTyping env 0 (SourceCasts env) ctx first.val.1 (bodyType.inst arg) := by
    rw [congrArg Prod.fst firstValue]
    exact bodyTyped.instantiate closed SourceCasts.closed argument
  obtain ⟨result,stepped,kind,resultTyped,value⟩ := arguments.step_complete closed SourceCasts.closed
    coverage first firstStep (congrArg Prod.snd firstValue) typed
  have target : result.val.1 = args.foldl applyReduced (body.inst arg) := by
    simpa only [congrArg Prod.fst firstValue] using value
  have sourceForm := (ValueForm.beta (setup := setup) bodyTyped (arg := arg)).arguments arguments
  have noAlias := setup.basic_values_none form sourceForm notSort
  by_cases same : args.foldl applyReduced (body.inst arg) =
      LeanTyped.applications (.app (.lam domain body) arg) args
  · have typedResult := target ▸ resultTyped
    rw [← same] at noAlias ⊢
    exact LeanStructuralConversion.prove_reflexive_cast_complete typedResult noAlias coverage
  · exact LeanStructuralConversion.prove_reduction_right_complete result stepped target kind
      (fun _ success => form.step_kind _ _ success) same noAlias

/-- Mixed-annotation helper calls use the actual conversion checks at every
argument. The intermediate function types come from source typing under the
corresponding substitution, not from an assumed successful reduction. -/
theorem AliasSetup.helper_checked_proved {body : VExpr} (setup : AliasSetup env)
    (signatures : Signatures env) (closed : ClosedConstantTypes env)
    (bodyTyped : CastTyping env 0 (SourceCasts env) (domain::ctx) body
      (domains.foldr VExpr.forallE resultType))
    (argument : CheckedTyping env 0 (SourceCasts env) ctx arg domain)
    (arguments : List.Forall₂ (fun domain arg =>
      CheckedTyping env 0 (SourceCasts env) ctx arg domain) domains args)
    (typesClosed : ∀ n, ((domains.drop n).foldr VExpr.forallE resultType).ClosedN 0)
    (prefixTyped : ∀ before after, args = before ++ after → after ≠ [] →
      CastTyping env 0 (SourceCasts env) ctx (before.foldl applyReduced (body.inst arg))
        ((domains.drop before.length).foldr VExpr.forallE resultType))
    (normalizedTyped : CastTyping env 0 (SourceCasts env) ctx
      (args.foldl applyReduced (body.inst arg)) resultType)
    (form : ValueForm setup ctx (args.foldl applyReduced (body.inst arg)) resultType)
    (notSort : ∀ u, resultType ≠ .sort u) (fuel : Nat) :
    ∃ equation, LeanStructuralConversion.prove env setup.basic setup.exposure 0 (fuel+5) ctx
      (args.foldl applyReduced (body.inst arg))
      (LeanTyped.applications (.app (.lam domain body) arg) args) = some equation ∧
      equation.type = resultType := by
  have coverage := setup.covers_source_recursive signatures closed fuel
  obtain ⟨first,firstStep,firstValue⟩ := step_beta_checked_complete bodyTyped argument coverage [] setup.exposure
  have initialClosed := typesClosed 0
  simp only [List.drop_zero] at initialClosed
  have firstType : first.val.2 = domains.foldr VExpr.forallE resultType := by
    simpa only [initialClosed.instN_eq (Nat.zero_le _)] using congrArg Prod.snd firstValue
  obtain ⟨result,stepped,kind,value⟩ := step_checked_spine_complete arguments typesClosed
    prefixTyped coverage first firstStep firstType (congrArg Prod.fst firstValue)
  have initialForm : ValueForm setup ctx (.app (.lam domain body) arg)
      (domains.foldr VExpr.forallE resultType) := by
    simpa only [initialClosed.instN_eq (Nat.zero_le _)] using
      (ValueForm.beta (setup := setup) bodyTyped (arg := arg))
  have sourceForm := initialForm.checkedArguments arguments typesClosed
  have noAlias := setup.basic_values_none form sourceForm notSort
  by_cases same : args.foldl applyReduced (body.inst arg) =
      LeanTyped.applications (.app (.lam domain body) arg) args
  · rw [← same] at noAlias ⊢
    exact LeanStructuralConversion.prove_reflexive_cast_complete normalizedTyped noAlias coverage
  · exact LeanStructuralConversion.prove_reduction_right_complete result stepped value kind
      (fun _ success => form.step_kind _ _ success) same noAlias

theorem AliasSetup.scalar_beta_checked_proved {body arg : VExpr} (setup : AliasSetup env) (signatures : Signatures env)
    (closed : ClosedConstantTypes env)
    (bodyTyped : CastTyping env 0 (SourceCasts env) (wordType::ctx) body wordType)
    (argTyped : CheckedTyping env 0 (SourceCasts env) ctx arg wordType)
    (form : ValueForm setup ctx (body.inst arg) wordType) (fuel : Nat) :
    ∃ equation, LeanStructuralConversion.prove env setup.basic setup.exposure 0 (fuel+5) ctx
      (body.inst arg) (.app (.lam wordType body) arg) = some equation ∧ equation.type = wordType :=
  setup.scalar_beta_checked_domain_proved signatures closed
    (.constant signatures.word (by simp) rfl) (by trivial) (by intro u; simp [wordType])
    bodyTyped argTyped form fuel

theorem AliasSetup.scalar_beta_proved {body arg : VExpr} (setup : AliasSetup env) (signatures : Signatures env)
    (closed : ClosedConstantTypes env)
    (bodyTyped : CastTyping env 0 (SourceCasts env) (wordType::ctx) body wordType)
    (argTyped : CastTyping env 0 (SourceCasts env) ctx arg wordType)
    (form : ValueForm setup ctx (body.inst arg) wordType) (fuel : Nat) :
    ∃ equation, LeanStructuralConversion.prove env setup.basic setup.exposure 0 (fuel+5) ctx
      (body.inst arg) (.app (.lam wordType body) arg) = some equation ∧ equation.type = wordType :=
  setup.scalar_beta_checked_proved signatures closed bodyTyped (.exact argTyped) form fuel

/-- Abstract and immediately apply the two native `for` arguments. -/
def continuation2Value (firstDomain secondDomain value : VExpr) : VExpr :=
  .app (.app (.lam firstDomain (.lam secondDomain (value.liftN 2 2))) (.bvar 1)) (.bvar 0)

theorem continuation2Value_inst (value : VExpr) :
    ((value.liftN 2 2).inst (.bvar 1) 1).inst (.bvar 0) = value := by
  have first := VExpr.liftN_instN_hi (value.liftN 1 2) (.bvar 0) 1 0 1
  simp only [VExpr.instN_bvar0,VExpr.liftN'_liftN_hi,VExpr.liftN,liftVar,
    Nat.reduceAdd,Nat.not_lt_zero,ite_false] at first
  rw [← first]
  exact VExpr.instN_bvar0 value 0

theorem continuation2Value_ne (firstDomain secondDomain value : VExpr) :
    value ≠ continuation2Value firstDomain secondDomain value := by
  intro same
  have bound := VExpr.sizeOf_liftN (n := 2) value 2
  have sized := congrArg sizeOf same
  change sizeOf value = 1 + (1 + (1 + sizeOf firstDomain +
    (1 + sizeOf secondDomain + sizeOf (value.liftN 2 2))) +
    (1 + sizeOf (1 : Nat))) + (1 + sizeOf (0 : Nat)) at sized
  omega

theorem AliasSetup.value_beta2_proved (setup : AliasSetup env) (signatures : Signatures env)
    (closed : ClosedConstantTypes env)
    (firstClosed : firstDomain.ClosedN 0) (secondClosed : secondDomain.ClosedN 0)
    (secondType : DirectTyping env 0 ctx secondDomain (.sort u))
    (resultClosed : resultType.ClosedN 0) (notSort : ∀ u, resultType ≠ .sort u)
    (typed : CastTyping env 0 (SourceCasts env) (secondDomain::firstDomain::ctx) value resultType)
    (form : ValueForm setup (secondDomain::firstDomain::ctx) value resultType) (fuel : Nat) :
    ∃ equation, LeanStructuralConversion.prove env setup.basic setup.exposure 0 (fuel+5)
      (secondDomain::firstDomain::ctx) value (continuation2Value firstDomain secondDomain value) = some equation ∧
      equation.type = resultType := by
  have lifted : CastTyping env 0 (SourceCasts env)
      (secondDomain::firstDomain::secondDomain::firstDomain::ctx) (value.liftN 2 2) resultType := by
    simpa only [firstClosed.liftN_eq (Nat.zero_le _),secondClosed.liftN_eq (Nat.zero_le _),
      resultClosed.liftN_eq (Nat.zero_le _)] using typed.weakN closed SourceCasts.closed
        (Ctx.LiftN.succ (Ctx.LiftN.succ (Ctx.LiftN.zero [secondDomain,firstDomain])))
  have domainTyped : DirectTyping env 0 (firstDomain::secondDomain::firstDomain::ctx)
      secondDomain (.sort u) := (secondType.withCasts (fun _ _ _ => False)).closed_context
      (by intro _ _ _ h; cases h) secondClosed _ |>.withoutCasts
  have functionTyped := CastTyping.lambda (domainTyped.withCasts (SourceCasts env)) lifted
  have firstArg : CastTyping env 0 (SourceCasts env) (secondDomain::firstDomain::ctx) (.bvar 1) firstDomain := by
    simpa only [firstClosed.liftN_eq (Nat.zero_le _)] using
      (CastTyping.bvar (env := env) (U := 0) (casts := SourceCasts env)
        (Lookup.succ (A := secondDomain) (Lookup.zero (ty := firstDomain) (Γ := ctx))))
  have secondArg : CastTyping env 0 (SourceCasts env) (secondDomain::firstDomain::ctx) (.bvar 0)
      (secondDomain.inst (.bvar 1)) := by
    simpa only [secondClosed.liftN_eq (Nat.zero_le _),secondClosed.instN_eq (Nat.zero_le _)] using
      (CastTyping.bvar (env := env) (U := 0) (casts := SourceCasts env)
        (Lookup.zero (ty := secondDomain) (Γ := firstDomain::ctx)))
  have unbeta := continuation2Value_inst value
  have kind : (resultType.inst (.bvar 1) 1).inst (.bvar 0) = resultType := by
    rw [resultClosed.instN_eq (Nat.zero_le _),resultClosed.instN_eq (Nat.zero_le _)]
  have substituted : ValueForm setup (secondDomain::firstDomain::ctx)
      (((value.liftN 2 2).inst (.bvar 1) 1).inst (.bvar 0))
      ((resultType.inst (.bvar 1) 1).inst (.bvar 0)) := by rw [unbeta,kind]; exact form
  have notAlias := setup.basic_beta2_none functionTyped (by simpa only [kind] using notSort) substituted
  obtain ⟨result,success,same⟩ := step_beta2_cast_complete closed SourceCasts.closed
    functionTyped firstArg secondArg (setup.covers_source_recursive signatures closed fuel) [] setup.exposure
  have target : result.val.1 = value := (congrArg Prod.fst same).trans unbeta
  have resultKind : result.val.2 = resultType := (congrArg Prod.snd same).trans kind
  apply LeanStructuralConversion.prove_reduction_right_complete result success target resultKind
    (fun _ success => form.step_kind _ _ success) (continuation2Value_ne _ _ _)
  rw [continuation2Value_inst] at notAlias
  exact notAlias

/-- Fixed Word declaration shape; independent of the typechecker and parser. -/
def WordDeclaration (native : Lean.Environment) : Prop :=
  ∀ definition : Definition native ``HybridWord.Word,
    definition.declaration.levelParams.length = 0 ∧
    definition.body.val.instL [] = bitvecType ∧
    definition.type.val.instL [] = .sort (.succ .zero)

/-- Connect the abstract declaration setup above to the actual loader, not a
second converter. Source-name freshness is supplied by the generated wrapper. -/
theorem loaded_alias_setup
    (loaded : WordFrontend.load native name = some library)
    (wordShape : WordDeclaration native) (decEqShape : DecEqDeclaration native)
    (freshWord : ``HybridWord.Word ≠ name)
    (freshBitVec : ``BitVec ≠ name)
    (freshOfNat : ``OfNat ≠ name)
    (freshNumerals : ∀ n ∈ [``Nat.zero,``Nat.succ,``Nat.mul], n ≠ name)
    (freshClasses : ∀ op : Binary, op.className ≠ name)
    (freshHeterogeneous : ∀ op : Binary, op.heterogeneous ≠ name)
    (freshNeg : ``Neg ≠ name) (freshOption : ``Option ≠ name) (freshReadClass : ``GetElem? ≠ name) :
    ∃ setup : AliasSetup library.model,
      setup.conversion = library.conversion ∧
      library.exposure = (fun U ctx e => expose setup.rules setup.conversion U ctx e) ∧
      setup.rules.map Rule.name = [name,``HybridWord.Word,``DecidableEq,``optParam] := by
  have originalLoaded := loaded
  unfold WordFrontend.load at loaded
  cases sourceFound : LeanTypeReduction.load native name with
  | none => simp [sourceFound] at loaded
  | some source =>
    simp only [sourceFound,bind,Option.bind] at loaded
    cases dependenciesFound : dependencies native (libraryRoots name source.declaration.value) [] with
    | none => simp [dependenciesFound] at loaded
    | some names =>
      simp only [dependenciesFound] at loaded
      split at loaded
      · contradiction
      · rename_i base installed
        cases identityFound : LeanTypeAliases.load native ``outParam with
        | none => simp [identityFound] at loaded
        | some identity =>
          simp only [identityFound,bind,Option.bind] at loaded
          cases optionalFound : LeanTypeReduction.load native ``optParam with
          | none => simp [optionalFound] at loaded
          | some optional =>
            simp only [optionalFound,bind,Option.bind] at loaded
            cases decEqFound : LeanTypeReduction.load native ``DecidableEq with
            | none => simp [decEqFound] at loaded
            | some decEq =>
              simp only [decEqFound,bind,Option.bind] at loaded
              cases wordFound : LeanTypeReduction.load native ``HybridWord.Word with
              | none => simp [wordFound] at loaded
              | some wd =>
                simp only [wordFound,bind,Option.bind,pure,Option.pure_def,Option.some.injEq] at loaded
                have sourceDeclared := loaded_source_signature originalLoaded source.asDeclaration
                  (.root (by simp [libraryRoots]))
                have wordDeclared := loaded_source_signature originalLoaded wd.asDeclaration
                  (.root (by
                    have present : ``HybridWord.Word ∈ declarations := by decide
                    simp [libraryRoots,present]))
                have decEqDeclared := loaded_source_signature originalLoaded decEq.asDeclaration
                  (.root (by simp [libraryRoots]))
                have optionalDeclared := loaded_source_signature originalLoaded optional.asDeclaration
                  (.root (by simp [libraryRoots]))
                subst library
                let model := source.install (wd.install (decEq.install (optional.install (identity.install base))))
                let setup : AliasSetup model := {
                  native := native, identity := identity
                  identityRegistered := Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
                  leadingRules := [⟨native,name,source,Or.inl rfl⟩]
                  wordRule := ⟨native,``HybridWord.Word,wd,Or.inr (Or.inl rfl)⟩
                  trailingRules := [⟨native,``DecidableEq,decEq,Or.inr (Or.inr (Or.inl rfl))⟩,
                    ⟨native,``optParam,optional,Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩]
                  declaredRules := by
                    intro r member
                    simp only [List.mem_append,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at member
                    rcases member with rfl | rfl | rfl | rfl
                    · exact sourceDeclared
                    · exact wordDeclared
                    · exact decEqDeclared
                    · exact optionalDeclared
                  decEqView := by
                    by_cases sourceName : name = ``DecidableEq
                    · subst name
                      refine ⟨[],⟨native,``DecidableEq,source,Or.inl rfl⟩,_,rfl,rfl,
                        (decEqShape source).1,(decEqShape source).2.1,(decEqShape source).2.2,?_⟩
                      simp
                    · refine ⟨[⟨native,name,source,Or.inl rfl⟩,
                        ⟨native,``HybridWord.Word,wd,Or.inr (Or.inl rfl)⟩],
                        ⟨native,``DecidableEq,decEq,Or.inr (Or.inr (Or.inl rfl))⟩,
                        [⟨native,``optParam,optional,Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩],rfl,rfl,
                        (decEqShape decEq).1,(decEqShape decEq).2.1,(decEqShape decEq).2.2,?_⟩
                      simp [Ne.symm sourceName]
                  wordName := rfl
                  wordMonomorphic := (wordShape wd).1
                  wordBody := (wordShape wd).2.1
                  wordKind := (wordShape wd).2.2
                  wordFirst := by simpa using freshWord
                  irreducibleBitVec := by simp [freshBitVec]
                  irreducibleOfNat := by simp [freshOfNat]
                  irreducibleNumeral := by
                    intro n hn
                    have fresh := freshNumerals n hn
                    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hn
                    rcases hn with rfl | rfl | rfl <;> simp_all
                  irreducibleNeg := by simp [freshNeg]
                  irreducibleOption := by simp [freshOption]
                  irreducibleReadClass := by simp [freshReadClass]
                  irreducibleHeterogeneous := by
                    intro op
                    have fresh := freshHeterogeneous op
                    cases op <;> simp_all [Binary.heterogeneous]
                  irreducibleClass := by
                    intro op
                    have fresh := freshClasses op
                    cases op <;> simp_all [Binary.className] }
                exact ⟨setup,rfl,rfl,rfl⟩

/-- Arithmetic coverage is a consequence of the actual loaded setup. The
setup itself is also reused by binder-certificate completeness. -/
theorem loaded_conversion_covers
    (loaded : WordFrontend.load native name = some library)
    (wordShape : WordDeclaration native) (decEqShape : DecEqDeclaration native)
    (freshWord : ``HybridWord.Word ≠ name)
    (freshBitVec : ``BitVec ≠ name)
    (freshOfNat : ``OfNat ≠ name)
    (freshNumerals : ∀ n ∈ [``Nat.zero,``Nat.succ,``Nat.mul], n ≠ name)
    (freshClasses : ∀ op : Binary, op.className ≠ name)
    (freshHeterogeneous : ∀ op : Binary, op.heterogeneous ≠ name)
    (freshNeg : ``Neg ≠ name) (freshOption : ``Option ≠ name) (freshReadClass : ``GetElem? ≠ name)
    (signatures : Signatures library.model) :
    Conversion.Covers library.conversion 0 Casts := by
  obtain ⟨setup,converter,_,_⟩ := loaded_alias_setup loaded wordShape decEqShape
    freshWord freshBitVec freshOfNat freshNumerals freshClasses freshHeterogeneous freshNeg freshOption freshReadClass
  rw [← converter]
  exact setup.covers signatures

end IRComparison.WordFrontend.Arithmetic
