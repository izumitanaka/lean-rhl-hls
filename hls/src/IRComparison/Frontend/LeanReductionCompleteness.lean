import IRComparison.Frontend.LeanTypeReduction
import IRComparison.Frontend.LeanTypingCompleteness
import IRComparison.Frontend.LeanCastTyping

namespace IRComparison.LeanTypeAliases
open Lean4Lean LeanTypeInference

theorem Alias.expand_complete (entry : Alias native name)
    (registered : env.defeqs entry.equation) (wf : u.WF U)
    (typed : DirectTyping env U ctx arg (.sort u)) (base : Conversion env) :
    ∃ result, entry.expand registered U ctx (.app (.const name [u]) arg) base = some result ∧
      result.val = (arg,u) := by
  obtain ⟨checked,accepted⟩ := typed.check_complete base (noExposure env)
  simp only [Alias.expand,dif_pos rfl,dif_pos wf,accepted,bind,Option.bind]
  exact ⟨_,rfl,rfl⟩

theorem Alias.conversion_left_complete (entry : Alias native name)
    (registered : env.defeqs entry.equation) (wf : u.WF U)
    (typed : DirectTyping env U ctx arg (.sort u)) (base : Conversion env) :
    ∃ result, entry.conversion registered base U ctx (.app (.const name [u]) arg) arg = some result := by
  obtain ⟨⟨⟨term,level⟩,proof⟩,expanded,same⟩ := entry.expand_complete registered wf typed base
  dsimp only at same
  cases same
  simp only [Alias.conversion,expanded,dif_pos rfl,bind,Option.bind]
  exact ⟨_,rfl⟩

private theorem Alias.conversion_right_of_expand (entry : Alias native name)
    (registered : env.defeqs entry.equation) (base : Conversion env)
    (result : {r : VExpr × VLevel // env.IsDefEq U ctx (.app (.const name [u]) arg) r.1 (.sort r.2)})
    (expanded : entry.expand registered U ctx (.app (.const name [u]) arg) base = some result)
    (value : result.val = (arg,u)) :
    ∃ result, entry.conversion registered base U ctx arg (.app (.const name [u]) arg) = some result := by
  rcases result with ⟨⟨term,level⟩,proof⟩
  dsimp only at value
  cases value
  unfold Alias.conversion
  cases first : entry.expand registered U ctx arg base with
  | none =>
    simp only [first,expanded,dif_pos rfl,bind,Option.bind]
    exact ⟨_,rfl⟩
  | some firstResult =>
    simp only [first]
    split
    · exact ⟨_,rfl⟩
    · simp only [expanded,dif_pos rfl,bind,Option.bind]
      exact ⟨_,rfl⟩

theorem Alias.conversion_right_complete (entry : Alias native name)
    (registered : env.defeqs entry.equation) (wf : u.WF U)
    (typed : DirectTyping env U ctx arg (.sort u)) (base : Conversion env) :
    ∃ result, entry.conversion registered base U ctx arg (.app (.const name [u]) arg) = some result := by
  obtain ⟨result,expanded,value⟩ := entry.expand_complete registered wf typed base
  exact entry.conversion_right_of_expand registered base result expanded value

/-- A type-level function may infer an `imax` universe while its annotation
uses an equivalent `max`. The actual universe converter handles that case;
we do not require the two universe expressions to be syntactically identical. -/
theorem Alias.expand_universe_complete (entry : Alias native name)
    (registered : env.defeqs entry.equation)
    (typed : DirectTyping env U ctx arg (.sort actual))
    (actualClosed : actual.WF 0) (expectedClosed : expected.WF 0)
    (sameUniverse : actual.eval [] = expected.eval []) :
    ∃ result, entry.expand registered U ctx (.app (.const name [expected]) arg)
      (LeanUniverseConversion.conversion env) = some result ∧ result.val = (arg,expected) := by
  let base := LeanUniverseConversion.conversion env
  obtain ⟨⟨ty,h⟩,inferred,same⟩ := typed.infer_complete base (noExposure env)
  dsimp only at same
  subst ty
  have checked : ∃ result, checkWith env base U ctx arg (.sort expected) = some result := by
    by_cases same : actual = expected
    · subst expected
      simp only [checkWith,inferred,bind,Option.bind,dif_pos rfl]
      exact ⟨_,rfl⟩
    · obtain ⟨converted,conversion⟩ := LeanUniverseConversion.conversion_complete
        actualClosed expectedClosed sameUniverse env U ctx
      have different : VExpr.sort actual ≠ .sort expected := fun h => same (VExpr.sort.inj h)
      simp only [checkWith,inferred,bind,Option.bind,dif_neg different,base,conversion]
      exact ⟨_,rfl⟩
  obtain ⟨checked,accepted⟩ := checked
  dsimp only [base] at accepted
  have wf := LeanUniverseConversion.wf_of_closed expectedClosed U
  simp only [Alias.expand,dif_pos rfl,dif_pos wf,accepted,bind,Option.bind]
  exact ⟨_,rfl,rfl⟩

theorem Alias.conversion_right_universe_complete (entry : Alias native name)
    (registered : env.defeqs entry.equation)
    (typed : DirectTyping env U ctx arg (.sort actual))
    (actualClosed : actual.WF 0) (expectedClosed : expected.WF 0)
    (sameUniverse : actual.eval [] = expected.eval []) :
    ∃ result, entry.conversion registered (LeanUniverseConversion.conversion env)
      U ctx arg (.app (.const name [expected]) arg) = some result := by
  obtain ⟨result,expanded,value⟩ := entry.expand_universe_complete registered typed
    actualClosed expectedClosed sameUniverse
  exact entry.conversion_right_of_expand registered _ result expanded value


end IRComparison.LeanTypeAliases

namespace IRComparison.LeanTypeReduction
open Lean4Lean LeanTypeInference

/-- Unfolding preserves the declared type when reduction rules come from the
same installed native signatures. This does not assume reduction succeeds. -/
theorem unfoldConstant_kind (rules : List (Rule env))
    (coherent : ∀ r ∈ rules, env.constants r.name =
      some ⟨r.definition.declaration.levelParams.length,r.definition.type.val⟩)
    (declared : env.constants name = some signature)
    (stepped : unfoldConstant rules U ctx name levels = some result) :
    result.val.2 = signature.type.instL levels := by
  induction rules with
  | nil => simp [unfoldConstant] at stepped
  | cons rule rest ih =>
    by_cases same : name = rule.name
    · have declared' : env.constants rule.name = some signature := by rw [← same]; exact declared
      have signatureSame := Option.some.inj ((coherent rule (by simp)).symm.trans declared')
      by_cases hw : ∀ u ∈ levels, u.WF U
      · by_cases hc : levels.length = rule.definition.declaration.levelParams.length
        · simp only [unfoldConstant,dif_pos same,if_pos same,dif_pos hw,if_pos hw,dif_pos hc,if_pos hc,
            pure,Option.pure_def,Option.some.injEq] at stepped
          subst result
          rw [← signatureSame]
        · simp [unfoldConstant,same,hw,hc] at stepped
      · simp [unfoldConstant,same,hw] at stepped
    · simp only [unfoldConstant,dif_neg same,if_neg same] at stepped
      exact ih (fun r member => coherent r (by simp [member])) stepped

/-- A name outside the finite delta-rule list is never unfolded. -/

theorem unfoldConstant_missing (rules : List (Rule env))
    (absent : ∀ r ∈ rules, name ≠ r.name) :
    unfoldConstant rules U ctx name levels = none := by
  induction rules with
  | nil => rfl
  | cons r rs ih =>
    rw [unfoldConstant]
    simp only [dif_neg (absent r (by simp))]
    exact ih (fun r hr => absent r (by simp [hr]))

/-- Lookup of an actual registered definition succeeds, independently of
conversion search; preceding unrelated rules do not affect the result. -/
theorem unfoldConstant_present (leadingRules trailingRules : List (Rule env)) (rule : Rule env)
    (absent : ∀ r ∈ leadingRules, rule.name ≠ r.name)
    (wf : ∀ u ∈ levels, u.WF U)
    (arity : levels.length = rule.definition.declaration.levelParams.length) :
    ∃ result, unfoldConstant (leadingRules ++ rule :: trailingRules) U ctx rule.name levels = some result ∧
      result.val = (rule.definition.body.val.instL levels,rule.definition.type.val.instL levels) := by
  induction leadingRules with
  | nil =>
    simp only [List.nil_append,unfoldConstant,dif_pos rfl,dif_pos wf,dif_pos arity]
    exact ⟨_,rfl,rfl⟩
  | cons r rs ih =>
    simp only [List.cons_append,unfoldConstant,dif_neg (absent r (by simp))]
    exact ih (fun r hr => absent r (by simp [hr]))

/-- Recognize a constant-headed application without evaluating its arguments. -/
def constantHead : VExpr → Option (Lean.Name × List VLevel)
  | .const name levels => some (name,levels)
  | .app f _ => constantHead f
  | _ => none

theorem step_constantHead_missing (source : VExpr) (head : constantHead source = some (name,levels))
    (rules : List (Rule env)) (absent : ∀ r ∈ rules, name ≠ r.name)
    (conv : Conversion env) (exposure : Exposure env) :
    step rules conv U ctx exposure source = none := by
  induction source with
  | const n us =>
    simp only [constantHead,Option.some.injEq,Prod.mk.injEq] at head
    obtain ⟨rfl,rfl⟩ := head
    exact unfoldConstant_missing rules absent
  | app f a ihf iha =>
    have hf := ihf head
    cases f <;> simp_all [constantHead,step,bind,Option.bind]
  | bvar | sort | lam | forallE => simp [constantHead] at head

theorem reduce_missing (missing : step rules conv U ctx exposure source = none) (fuel : Nat) :
    reduce rules conv U ctx exposure fuel source = none := by
  cases fuel <;> simp only [reduce,missing,bind,Option.bind]

/-- After one successful step, bounded continuation preserves its result type
and cannot turn that success into failure. -/
theorem reduce_first_complete
    (first : Result env U ctx source)
    (stepped : step rules conv U ctx exposure source = some first) (fuel : Nat) :
    ∃ result, reduce rules conv U ctx exposure (fuel+1) source = some result ∧
      result.val.2 = first.val.2 := by
  rw [reduce]
  simp only [stepped,bind,Option.bind]
  cases rest : reduce rules conv U ctx exposure fuel first.val.1 with
  | none => simp only [rest]; exact ⟨_,rfl,rfl⟩
  | some next =>
    simp only [rest]
    split
    · exact ⟨_,rfl,rfl⟩
    · cases cast : conv U ctx next.val.2 first.val.2 with
      | none => simp only [cast]; exact ⟨_,rfl,rfl⟩
      | some converted => simp only [cast]; exact ⟨_,rfl,rfl⟩

/-- Any successful beta step reports the type independently determined by
its body. This is a property of reduction, not a success assumption. -/
theorem step_beta_kind {rules : List (Rule env)} {conv : Conversion env} {exposure : Exposure env}
    (bodyTyped : CastTyping env U casts (domain::ctx) body resultType)
    (stepped : step rules conv U ctx exposure (.app (.lam domain body) arg) = some result) :
    result.val.2 = resultType.inst arg := by
  cases argument : checkWith env conv U ctx arg domain exposure with
  | none => simp only [step,argument,bind,Option.bind] at stepped; cases stepped
  | some ha =>
    cases inferred : inferWith env conv U (domain::ctx) body exposure with
    | none => simp only [step,argument,inferred,bind,Option.bind] at stepped; cases stepped
    | some hb =>
      have same := bodyTyped.inferred_kind (known := noKnownTypes env U)
        (by intro _ _ _ h; cases h) _ inferred
      simp only [step,argument,inferred,bind,Option.bind,pure,Option.pure_def,Option.some.injEq] at stepped
      subst result
      exact congrArg (fun ty => ty.inst arg) same

/-- A successful application step preserves the codomain reported by its
function step, even when argument checking or conversion is incomplete. -/
theorem step_application_kind {env : VEnv} {rules : List (Rule env)}
    {conv : Conversion env} {exposure : Exposure env} {U : Nat} {ctx : List VExpr}
    {source domain codomain arg : VExpr} {result : Result env U ctx (.app source arg)}
    (notLambda : ∀ domain body, source ≠ .lam domain body)
    (functionKind : ∀ result, step rules conv U ctx exposure source = some result →
      result.val.2 = .forallE domain codomain)
    (stepped : step rules conv U ctx exposure (.app source arg) = some result) :
    result.val.2 = codomain.inst arg := by
  rw [step.eq_3 _ _ _ _ _ _ _ notLambda] at stepped
  cases first : step rules conv U ctx exposure source with
  | none => simp only [first,bind,Option.bind] at stepped; cases stepped
  | some fn =>
    rcases fn with ⟨⟨term,kind⟩,proof⟩
    have same := functionKind _ first
    dsimp only at same
    subst kind
    simp only [first,bind,Option.bind] at stepped
    cases argument : checkWith env conv U ctx arg domain exposure with
    | none => simp only [argument,bind,Option.bind] at stepped; cases stepped
    | some ha =>
      simp only [argument,bind,Option.bind] at stepped
      cases term with
      | lam binder body =>
        by_cases same : binder = domain
        · simp only [dif_pos same] at stepped
          cases bodyCheck : checkWith env conv U (domain::ctx) body codomain exposure with
          | none => simp only [bodyCheck,bind,Option.bind] at stepped; cases stepped
          | some hb => simp only [bodyCheck,bind,Option.bind] at stepped; cases stepped; rfl
        · simp only [dif_neg same] at stepped; cases stepped; rfl
      | bvar | sort | const | app | forallE => cases stepped; rfl

/-- Two ordinary lambda arguments are reduced in the same weak-head step.
This describes arity, not a bound on nesting or iteration count. -/
theorem step_beta2_kind {env : VEnv} {rules : List (Rule env)}
    {conv : Conversion env} {exposure : Exposure env} {U : Nat} {ctx : List VExpr}
    {firstDomain secondDomain body resultType firstArg secondArg : VExpr}
    {result : Result env U ctx (.app (.app (.lam firstDomain (.lam secondDomain body)) firstArg) secondArg)}
    (bodyTyped : CastTyping env U casts (firstDomain::ctx)
      (.lam secondDomain body) (.forallE secondDomain resultType))
    (stepped : step rules conv U ctx exposure
      (.app (.app (.lam firstDomain (.lam secondDomain body)) firstArg) secondArg) = some result) :
    result.val.2 = (resultType.inst firstArg 1).inst secondArg := by
  exact step_application_kind (domain := secondDomain.inst firstArg)
    (codomain := resultType.inst firstArg 1) (by intro d b h; cases h)
    (fun _ success => step_beta_kind bodyTyped success) stepped

/-- Speculative exposure cannot turn a value-producing reduction into an
equality of types. The converter need not be complete for this exclusion. -/
theorem expose_not_sort {env : VEnv} {rules : List (Rule env)} {conv : Conversion env}
    (kind : ∀ result, step rules conv U ctx (noExposure env) source = some result →
      ∀ u, result.val.2 ≠ .sort u) (fuel : Nat) :
    expose rules conv U ctx source (fuel+1) = none := by
  cases first : step rules conv U ctx (noExposure env) source with
  | none => simp only [expose,reduce_missing first,bind,Option.bind]
  | some result =>
    obtain ⟨⟨⟨value,ty⟩,proof⟩,reduced,equal⟩ := reduce_first_complete result first fuel
    have missingKind : ∀ u, ty ≠ .sort u := fun u h => kind result first u (equal.symm.trans h)
    simp only [expose,reduced,bind,Option.bind]
    split <;> simp_all

theorem expose_beta_not_sort
    (bodyTyped : CastTyping env U casts (domain::ctx) body resultType)
    (notSort : ∀ u, resultType.inst arg ≠ .sort u)
    (rules : List (Rule env)) (conv : Conversion env) (fuel : Nat) :
    expose rules conv U ctx (.app (.lam domain body) arg) (fuel+1) = none :=
  expose_not_sort (fun _ success u => by rw [step_beta_kind bodyTyped success]; exact notSort u) fuel

theorem expose_beta2_not_sort {env : VEnv}
    (bodyTyped : CastTyping env U casts (firstDomain::ctx)
      (.lam secondDomain body) (.forallE secondDomain resultType))
    (notSort : ∀ u, (resultType.inst firstArg 1).inst secondArg ≠ .sort u)
    (rules : List (Rule env)) (conv : Conversion env) (fuel : Nat) :
    expose rules conv U ctx
      (.app (.app (.lam firstDomain (.lam secondDomain body)) firstArg) secondArg) (fuel+1) = none :=
  expose_not_sort (fun _ success u => by rw [step_beta2_kind bodyTyped success]; exact notSort u) fuel

/-- A transparent alias with an irreducible constant-headed body is exposed
at every positive reduction budget, including the existing default budget. -/
theorem reduce_alias_complete (leadingRules trailingRules : List (Rule env)) (rule : Rule env)
    (absent : ∀ r ∈ leadingRules, rule.name ≠ r.name)
    (wf : ∀ u ∈ levels, u.WF U)
    (arity : levels.length = rule.definition.declaration.levelParams.length)
    (head : constantHead (rule.definition.body.val.instL levels) = some (headName,headLevels))
    (irreducible : ∀ r ∈ leadingRules ++ rule :: trailingRules, headName ≠ r.name)
    (conv : Conversion env) (exposure : Exposure env) (fuel : Nat) :
    ∃ result, reduce (leadingRules ++ rule :: trailingRules) conv U ctx exposure (fuel+1)
      (.const rule.name levels) = some result ∧
      result.val = (rule.definition.body.val.instL levels,rule.definition.type.val.instL levels) := by
  obtain ⟨⟨⟨term,ty⟩,correct⟩,unfolded,same⟩ :=
    unfoldConstant_present leadingRules trailingRules rule absent wf arity (ctx := ctx)
  dsimp only at same
  cases same
  have missing := step_constantHead_missing _ head _ irreducible conv exposure (ctx := ctx) (U := U)
  have stopped := reduce_missing missing fuel
  rw [reduce]
  simp only [step,unfolded,bind,Option.bind,stopped]
  exact ⟨_,rfl,rfl⟩

theorem expose_alias_complete (leadingRules trailingRules : List (Rule env)) (rule : Rule env)
    (absent : ∀ r ∈ leadingRules, rule.name ≠ r.name)
    (wf : ∀ u ∈ levels, u.WF U)
    (arity : levels.length = rule.definition.declaration.levelParams.length)
    (head : constantHead (rule.definition.body.val.instL levels) = some (headName,headLevels))
    (irreducible : ∀ r ∈ leadingRules ++ rule :: trailingRules, headName ≠ r.name)
    (kind : rule.definition.type.val.instL levels = .sort u)
    (conv : Conversion env) (fuel : Nat) :
    ∃ result, expose (leadingRules ++ rule :: trailingRules) conv U ctx
      (.const rule.name levels) (fuel+1) = some result ∧
      result.val = (rule.definition.body.val.instL levels,u) := by
  obtain ⟨⟨⟨term,ty⟩,correct⟩,reduced,same⟩ := reduce_alias_complete leadingRules trailingRules rule
    absent wf arity head irreducible conv (noExposure env) fuel (ctx := ctx)
  dsimp only at same
  rw [kind] at same
  cases same
  simp only [expose,reduced,bind,Option.bind]
  exact ⟨_,rfl,rfl⟩

/-- Expanding the alias on the actual side is accepted as well. -/
theorem conversion_alias_left_exact (leadingRules trailingRules : List (Rule env)) (rule : Rule env)
    (absent : ∀ r ∈ leadingRules, rule.name ≠ r.name)
    (wf : ∀ u ∈ levels, u.WF U)
    (arity : levels.length = rule.definition.declaration.levelParams.length)
    (head : constantHead (rule.definition.body.val.instL levels) = some (headName,headLevels))
    (irreducible : ∀ r ∈ leadingRules ++ rule :: trailingRules, headName ≠ r.name)
    (kind : rule.definition.type.val.instL levels = .sort u)
    (base : Conversion env) :
    ∃ result, conversion (leadingRules ++ rule :: trailingRules) base U ctx
      (.const rule.name levels) (rule.definition.body.val.instL levels) = some result ∧ result.val = u := by
  obtain ⟨⟨⟨term,level⟩,correct⟩,expanded,same⟩ := expose_alias_complete leadingRules trailingRules rule
    absent wf arity head irreducible kind base 31 (ctx := ctx)
  dsimp only at same
  cases same
  simp only [conversion,expanded,dif_pos rfl,bind,Option.bind,pure]
  exact ⟨_,rfl,rfl⟩

/-- The actual type-conversion function accepts the expanded body on the left
and its transparent alias on the right. The assumptions describe declarations
and syntax; they do not assume a successful typechecker or reduction search. -/
theorem conversion_alias_right_exact (leadingRules trailingRules : List (Rule env)) (rule : Rule env)
    (absent : ∀ r ∈ leadingRules, rule.name ≠ r.name)
    (wf : ∀ u ∈ levels, u.WF U)
    (arity : levels.length = rule.definition.declaration.levelParams.length)
    (head : constantHead (rule.definition.body.val.instL levels) = some (headName,headLevels))
    (irreducible : ∀ r ∈ leadingRules ++ rule :: trailingRules, headName ≠ r.name)
    (kind : rule.definition.type.val.instL levels = .sort u)
    (base : Conversion env) :
    ∃ result, conversion (leadingRules ++ rule :: trailingRules) base U ctx
      (rule.definition.body.val.instL levels) (.const rule.name levels) = some result ∧ result.val = u := by
  have missing := step_constantHead_missing _ head _ irreducible base (noExposure env) (ctx := ctx) (U := U)
  have stopped := reduce_missing missing 32
  have first : expose (leadingRules ++ rule :: trailingRules) base U ctx
      (rule.definition.body.val.instL levels) = none := by
    simp only [expose,stopped,bind,Option.bind]
  obtain ⟨⟨⟨term,level⟩,correct⟩,second,same⟩ := expose_alias_complete leadingRules trailingRules rule
    absent wf arity head irreducible kind base 31 (ctx := ctx)
  dsimp only at same
  cases same
  simp only [conversion,first,second,dif_pos rfl,bind,Option.bind,pure]
  exact ⟨_,rfl,rfl⟩

theorem conversion_alias_right_complete (leadingRules trailingRules : List (Rule env)) (rule : Rule env)
    (absent : ∀ r ∈ leadingRules, rule.name ≠ r.name)
    (wf : ∀ u ∈ levels, u.WF U)
    (arity : levels.length = rule.definition.declaration.levelParams.length)
    (head : constantHead (rule.definition.body.val.instL levels) = some (headName,headLevels))
    (irreducible : ∀ r ∈ leadingRules ++ rule :: trailingRules, headName ≠ r.name)
    (kind : rule.definition.type.val.instL levels = .sort u)
    (base : Conversion env) :
    ∃ result, conversion (leadingRules ++ rule :: trailingRules) base U ctx
      (rule.definition.body.val.instL levels) (.const rule.name levels) = some result := by
  obtain ⟨result,accepted,_⟩ := conversion_alias_right_exact leadingRules trailingRules rule
    absent wf arity head irreducible kind base (ctx := ctx)
  exact ⟨result,accepted⟩

/-- A typed beta redex is reduced by the actual implementation. Optional
conversion and exposure cannot make an exact, directly typed application fail.
The hypotheses are typing judgments, not successful checker executions. -/
theorem step_beta_checked_complete
    (bodyTyped : CastTyping env U casts (domain :: ctx) body resultType)
    (argTyped : CheckedTyping env U casts ctx arg domain)
    (coverage : Conversion.Covers conv U casts)
    (rules : List (Rule env)) (exposure : Exposure env) :
    ∃ result, step rules conv U ctx exposure (.app (.lam domain body) arg) = some result ∧
      result.val = (body.inst arg, resultType.inst arg) := by
  have empty : KnownTypes.Casts (noKnownTypes env U) casts := by intro _ _ _ h; cases h
  obtain ⟨checked,accepted⟩ := argTyped.check_complete empty coverage exposure
  obtain ⟨⟨ty,h⟩,inferred,same⟩ := bodyTyped.infer_complete empty coverage exposure
  dsimp only at same
  subst ty
  simp only [step,accepted,inferred,bind,Option.bind]
  exact ⟨_,rfl,rfl⟩

theorem step_beta_cast_complete
    (bodyTyped : CastTyping env U casts (domain :: ctx) body resultType)
    (argTyped : CastTyping env U casts ctx arg domain)
    (coverage : Conversion.Covers conv U casts)
    (rules : List (Rule env)) (exposure : Exposure env) :
    ∃ result, step rules conv U ctx exposure (.app (.lam domain body) arg) = some result ∧
      result.val = (body.inst arg, resultType.inst arg) :=
  step_beta_checked_complete bodyTyped (.exact argTyped) coverage rules exposure

theorem step_beta_complete
    (bodyTyped : DirectTyping env U (domain :: ctx) body resultType)
    (argTyped : DirectTyping env U ctx arg domain)
    (rules : List (Rule env)) (conv : Conversion env) (exposure : Exposure env) :
    ∃ result, step rules conv U ctx exposure (.app (.lam domain body) arg) = some result ∧
      result.val = (body.inst arg, resultType.inst arg) :=
  step_beta_cast_complete (bodyTyped.withCasts (fun _ _ _ => False)) (argTyped.withCasts _)
    (fun _ _ _ h => False.elim h) rules exposure

/-- The existing beta/application operation on proof-calculus terms. -/
def applyReduced (fn arg : VExpr) : VExpr := match fn with
  | .lam _ body => body.inst arg
  | other => .app other arg

/-- A checked argument may have a convertible, rather than syntactically
identical, type. The reducer still succeeds. Unlike the exact-argument rule,
this does not claim that substitution preserves the *inferred* type: replacing
a Word variable by a BitVec 32 variable can change that type. -/
theorem step_apply_checked_complete {env : VEnv} {conv : Conversion env}
    {rules : List (Rule env)} {exposure : Exposure env}
    (coverage : Conversion.Covers conv U casts)
    (function : Result env U ctx source)
    (reduced : step rules conv U ctx exposure source = some function)
    (functionType : function.val.2 = .forallE domain codomain)
    (functionTyped : CastTyping env U casts ctx function.val.1 (.forallE domain codomain))
    (argument : CheckedTyping env U casts ctx arg domain) :
    ∃ result, step rules conv U ctx exposure (.app source arg) = some result ∧
      result.val.2 = codomain.inst arg ∧
      result.val.1 = applyReduced function.val.1 arg := by
  obtain ⟨argProof,argChecked⟩ := argument.check_complete
    (known := noKnownTypes env U) (by intro _ _ _ h; cases h) coverage exposure
  rcases function with ⟨⟨fn,ty⟩,equation⟩
  dsimp only at functionType functionTyped
  subst ty
  cases fn with
  | lam binder body =>
    cases functionTyped with
    | lambda domainTyped bodyTyped =>
      obtain ⟨bodyProof,bodyChecked⟩ := bodyTyped.check_complete
        (known := noKnownTypes env U) (by intro _ _ _ h; cases h) coverage exposure
      have success : step rules conv U ctx exposure (.app source arg) =
          some ⟨(body.inst arg,codomain.inst arg),
            (VEnv.IsDefEq.appDF equation argProof.down).trans
              (VEnv.IsDefEq.beta bodyProof.down argProof.down)⟩ := by
        cases source with
        | bvar | sort | lam | forallE => simp [step] at reduced
        | const | app => rw [step] <;> simp [reduced,argChecked,bodyChecked]
      exact ⟨_,success,rfl,rfl⟩
  | bvar | sort | const | app | forallE =>
    have success : step rules conv U ctx exposure (.app source arg) =
        some ⟨(_,codomain.inst arg),VEnv.IsDefEq.appDF equation argProof.down⟩ := by
      cases source with
      | bvar | sort | lam | forallE => simp [step] at reduced
      | const | app => rw [step] <;> simp [reduced,argChecked]
    exact ⟨_,success,rfl,rfl⟩

/-- Exact substitution preserves the inferred type. This source-only lemma
is shared by weak-head completeness and prefix typing; it runs no reducer. -/
theorem applyReduced_typed
    (closed : ClosedConstantTypes env) (stable : ClosedCasts casts)
    (function : CastTyping env U casts ctx fn (.forallE domain codomain))
    (argument : CastTyping env U casts ctx arg domain) :
    CastTyping env U casts ctx (applyReduced fn arg) (codomain.inst arg) := by
  cases fn with
  | lam binder body =>
    cases function with
    | lambda domainTyped bodyTyped => exact bodyTyped.instantiate closed stable argument
  | bvar | sort | const | app | forallE => exact .application function argument

/-- Extending a successfully reduced source application preserves successful
typed reduction. In the lambda case the body check is derived from typing,
and the substituted result is typed by the substitution lemma. -/
theorem step_apply_cast_complete
    (closed : ClosedConstantTypes env) (stable : ClosedCasts casts)
    (coverage : Conversion.Covers conv U casts)
    (function : Result env U ctx source)
    (reduced : step rules conv U ctx exposure source = some function)
    (functionType : function.val.2 = .forallE domain codomain)
    (functionTyped : CastTyping env U casts ctx function.val.1 (.forallE domain codomain))
    (argument : CastTyping env U casts ctx arg domain) :
    ∃ result, step rules conv U ctx exposure (.app source arg) = some result ∧
      result.val.2 = codomain.inst arg ∧
      CastTyping env U casts ctx result.val.1 (codomain.inst arg) ∧
      result.val.1 = applyReduced function.val.1 arg := by
  obtain ⟨result,success,kind,value⟩ := step_apply_checked_complete coverage function
    reduced functionType functionTyped (.exact argument)
  refine ⟨result,success,kind,?_,value⟩
  rw [value]
  exact applyReduced_typed closed stable functionTyped argument

/-- Source application typing for a static telescope. Argument checks are
independent typing derivations, not executions of the type checker. -/
theorem checked_spine_typed
    (arguments : List.Forall₂ (fun domain arg => CheckedTyping env U casts ctx arg domain) domains args)
    (typesClosed : ∀ n, ((domains.drop n).foldr VExpr.forallE resultType).ClosedN 0)
    (typed : CastTyping env U casts ctx source (domains.foldr VExpr.forallE resultType)) :
    CastTyping env U casts ctx (LeanTyped.applications source args) resultType := by
  induction arguments generalizing source with
  | nil => exact typed
  | @cons domain arg domains args check rest ih =>
    have tailTypes : ∀ n, ((domains.drop n).foldr VExpr.forallE resultType).ClosedN 0 := by
      intro n
      simpa only [List.drop_succ_cons] using typesClosed (n+1)
    have tailClosed := tailTypes 0
    simp only [List.drop_zero] at tailClosed
    exact ih tailTypes (by simpa only [tailClosed.instN_eq (Nat.zero_le _)] using
      CastTyping.checkedApplication typed check)

/-- Exact arguments supply all partial-application types compositionally.
The checked-spine rule can reuse this for any exact suffix of a mixed call. -/
theorem exact_spine_prefix_typed
    (arguments : List.Forall₂ (fun domain arg => CastTyping env U casts ctx arg domain) domains args)
    (typesClosed : ∀ n, ((domains.drop n).foldr VExpr.forallE resultType).ClosedN 0)
    (closed : ClosedConstantTypes env) (stable : ClosedCasts casts)
    (typed : CastTyping env U casts ctx initial (domains.foldr VExpr.forallE resultType)) :
    ∀ before after, args = before ++ after →
      CastTyping env U casts ctx (before.foldl applyReduced initial)
        ((domains.drop before.length).foldr VExpr.forallE resultType) := by
  induction arguments generalizing initial with
  | nil =>
    intro before after same
    cases before with
    | nil => exact typed
    | cons a rest => simp at same
  | @cons domain arg domains args argument rest ih =>
    intro before after same
    cases before with
    | nil => exact typed
    | cons a before =>
      simp only [List.cons_append,List.cons.injEq] at same
      rcases same with ⟨rfl,same⟩
      have tailTypes : ∀ n, ((domains.drop n).foldr VExpr.forallE resultType).ClosedN 0 := by
        intro n
        simpa only [List.drop_succ_cons] using typesClosed (n+1)
      have tailClosed := tailTypes 0
      simp only [List.drop_zero] at tailClosed
      have applied := applyReduced_typed closed stable typed argument
      simp only [tailClosed.instN_eq (Nat.zero_le _)] at applied
      simpa only [List.foldl_cons,List.length_cons,List.drop_succ_cons] using
        ih tailTypes applied before after same

/-- Applying a static telescope uses checked argument types, including aliases.
Every intermediate function type is supplied by source typing; no reduction
or checker success is a premise. A single list induction covers arbitrary
arity, independently of the conversion search budget. -/
theorem step_checked_spine_complete
    (arguments : List.Forall₂ (fun domain arg => CheckedTyping env U casts ctx arg domain) domains args)
    (typesClosed : ∀ n, ((domains.drop n).foldr VExpr.forallE resultType).ClosedN 0)
    (prefixTyped : ∀ before after, args = before ++ after → after ≠ [] →
      CastTyping env U casts ctx (before.foldl applyReduced initial)
        ((domains.drop before.length).foldr VExpr.forallE resultType))
    (coverage : Conversion.Covers conv U casts)
    (function : Result env U ctx source)
    (reduced : step rules conv U ctx exposure source = some function)
    (functionType : function.val.2 = domains.foldr VExpr.forallE resultType)
    (functionValue : function.val.1 = initial) :
    ∃ result, step rules conv U ctx exposure (LeanTyped.applications source args) = some result ∧
      result.val.2 = resultType ∧ result.val.1 = args.foldl applyReduced initial := by
  induction arguments generalizing source initial with
  | nil => exact ⟨function,reduced,functionType,functionValue⟩
  | @cons domain arg domains args typed rest ih =>
    have tailTypes : ∀ n, ((domains.drop n).foldr VExpr.forallE resultType).ClosedN 0 := by
      intro n
      simpa only [List.drop_succ_cons] using typesClosed (n+1)
    have tailClosed := tailTypes 0
    simp only [List.drop_zero] at tailClosed
    have current := prefixTyped [] (arg::args) rfl (by simp)
    simp only [List.foldl_nil,List.length_nil,List.drop_zero] at current
    obtain ⟨next,stepped,nextType,nextValue⟩ := step_apply_checked_complete coverage function
      reduced functionType (functionValue.symm ▸ current) typed
    have nextKind : next.val.2 = domains.foldr VExpr.forallE resultType := by
      simpa only [tailClosed.instN_eq (Nat.zero_le _)] using nextType
    have nextTerm : next.val.1 = applyReduced initial arg := by rw [nextValue,functionValue]
    have nextPrefixes : ∀ before after, args = before ++ after → after ≠ [] →
        CastTyping env U casts ctx (before.foldl applyReduced (applyReduced initial arg))
          ((domains.drop before.length).foldr VExpr.forallE resultType) := by
      intro before after same nonempty
      have h := prefixTyped (arg::before) after (by simp [same]) nonempty
      simpa only [List.foldl_cons,List.length_cons,List.drop_succ_cons] using h
    obtain ⟨result,success,kind,value⟩ := ih tailTypes nextPrefixes next stepped nextKind nextTerm
    exact ⟨result,success,kind,by simpa only [List.foldl_cons] using value⟩

/-- The actual reducer accepts a two-argument lambda from independent typing
and conversion coverage; no successful subcheck is assumed. -/
theorem step_beta2_cast_complete
    (closed : ClosedConstantTypes env) (stable : ClosedCasts casts)
    (bodyTyped : CastTyping env U casts (firstDomain::ctx)
      (.lam secondDomain body) (.forallE secondDomain resultType))
    (firstTyped : CastTyping env U casts ctx firstArg firstDomain)
    (secondTyped : CastTyping env U casts ctx secondArg (secondDomain.inst firstArg))
    (coverage : Conversion.Covers conv U casts)
    (rules : List (Rule env)) (exposure : Exposure env) :
    ∃ result, step rules conv U ctx exposure
      (.app (.app (.lam firstDomain (.lam secondDomain body)) firstArg) secondArg) = some result ∧
      result.val = ((body.inst firstArg 1).inst secondArg, (resultType.inst firstArg 1).inst secondArg) := by
  obtain ⟨first,stepped,same⟩ := step_beta_cast_complete bodyTyped firstTyped coverage rules exposure
  have firstKind : first.val.2 = .forallE (secondDomain.inst firstArg) (resultType.inst firstArg 1) :=
    congrArg Prod.snd same
  have firstBody : CastTyping env U casts ctx first.val.1
      (.forallE (secondDomain.inst firstArg) (resultType.inst firstArg 1)) := by
    rw [congrArg Prod.fst same]
    exact bodyTyped.instantiate closed stable firstTyped
  obtain ⟨result,success,kind,_,value⟩ := step_apply_cast_complete closed stable coverage
    first stepped firstKind firstBody secondTyped
  refine ⟨result,success,Prod.ext ?_ kind⟩
  simpa only [congrArg Prod.fst same,VExpr.inst,applyReduced] using value

theorem step_apply_complete
    (closed : ClosedConstantTypes env)
    (function : Result env U ctx source)
    (reduced : step rules conv U ctx exposure source = some function)
    (functionType : function.val.2 = .forallE domain codomain)
    (functionTyped : DirectTyping env U ctx function.val.1 (.forallE domain codomain))
    (argument : DirectTyping env U ctx arg domain) :
    ∃ result, step rules conv U ctx exposure (.app source arg) = some result ∧
      result.val.2 = codomain.inst arg ∧
      DirectTyping env U ctx result.val.1 (codomain.inst arg) ∧
      result.val.1 = applyReduced function.val.1 arg := by
  obtain ⟨result,success,kind,typed,term⟩ := step_apply_cast_complete closed
    (casts := fun _ _ _ => False) (fun _ _ _ h => False.elim h)
    (fun _ _ _ h => False.elim h) function reduced functionType
    (functionTyped.withCasts _) (argument.withCasts _)
  exact ⟨result,success,kind,typed.withoutCasts,term⟩

/-- Typing an argument list is independent of reduction or checker success.
The codomain is instantiated after each argument, as in Lean application. -/
inductive ArgumentsCasts (env : VEnv) (U : Nat) (casts : TypeCasts) (ctx : List VExpr) :
    VExpr → List VExpr → VExpr → Prop where
  | nil : ArgumentsCasts env U casts ctx ty [] ty
  | cons : CastTyping env U casts ctx argument domain →
      ArgumentsCasts env U casts ctx (codomain.inst argument) rest result →
      ArgumentsCasts env U casts ctx (.forallE domain codomain) (argument::rest) result

/-- The exact telescope's source typing is shared by body and step
certificate transport, rather than repeated at each call site. -/
theorem ArgumentsCasts.application_typed
    (arguments : ArgumentsCasts env U casts ctx ty args resultType)
    (typed : CastTyping env U casts ctx fn ty) :
    CastTyping env U casts ctx (LeanTyped.applications fn args) resultType := by
  induction arguments generalizing fn with
  | nil => exact typed
  | cons argument rest ih => exact ih (.application typed argument)

theorem ArgumentsCasts.step_complete
    (arguments : ArgumentsCasts env U casts ctx ty args resultType)
    (closed : ClosedConstantTypes env) (stable : ClosedCasts casts)
    (coverage : Conversion.Covers conv U casts)
    (function : Result env U ctx source)
    (reduced : step rules conv U ctx exposure source = some function)
    (functionType : function.val.2 = ty)
    (functionTyped : CastTyping env U casts ctx function.val.1 ty) :
    ∃ result, step rules conv U ctx exposure (LeanTyped.applications source args) = some result ∧
      result.val.2 = resultType ∧ CastTyping env U casts ctx result.val.1 resultType ∧
      result.val.1 = args.foldl applyReduced function.val.1 := by
  induction arguments generalizing source with
  | nil => exact ⟨function,reduced,functionType,functionTyped,rfl⟩
  | cons argument rest ih =>
    obtain ⟨next,stepped,nextType,nextTyped,nextTerm⟩ :=
      step_apply_cast_complete closed stable coverage function reduced functionType functionTyped argument
    obtain ⟨result,success,resultType,resultTyped,resultTerm⟩ := ih next stepped nextType nextTyped
    exact ⟨result,success,resultType,resultTyped,by simpa only [List.foldl_cons,nextTerm] using resultTerm⟩

/-- The named-definition reduction used by the final source connection
succeeds for a monomorphic, directly typed body and typed arguments. In
particular it does not assume that the internal body checks succeed. -/
theorem named_application_cast_complete
    (rule : Rule env) (monomorphic : rule.definition.declaration.levelParams = [])
    (bodyTyped : CastTyping env U casts ctx rule.definition.body.val rule.definition.type.val)
    (arguments : ArgumentsCasts env U casts ctx rule.definition.type.val args resultType)
    (closed : ClosedConstantTypes env) (stable : ClosedCasts casts)
    (coverage : Conversion.Covers conv U casts) (exposure : Exposure env) :
    ∃ result, step [rule] conv U ctx exposure
        (LeanTyped.applications (.const rule.name []) args) = some result ∧
      result.val.2 = resultType ∧ CastTyping env U casts ctx result.val.1 resultType ∧
      result.val.1 = args.foldl applyReduced rule.definition.body.val := by
  have typeRep : LeanLibrary.Represents [] rule.definition.declaration.type rule.definition.type.val :=
    Eq.mp (congrArg (fun names => LeanLibrary.Represents names rule.definition.declaration.type
      rule.definition.type.val) monomorphic) rule.definition.type.property
  have bodyRep : LeanLibrary.Represents [] rule.definition.declaration.value rule.definition.body.val :=
    Eq.mp (congrArg (fun names => LeanLibrary.Represents names rule.definition.declaration.value
      rule.definition.body.val) monomorphic) rule.definition.body.property
  obtain ⟨function,unfolded,values⟩ := unfoldConstant_present [] [] rule (by simp)
    (levels := []) (U := U) (ctx := ctx) (by simp) (by simp [monomorphic])
  simp only [bodyRep.monomorphic.instL_empty,typeRep.monomorphic.instL_empty] at values
  obtain ⟨result,success,resultType,resultTyped,resultTerm⟩ :=
    arguments.step_complete closed stable coverage function unfolded (congrArg Prod.snd values)
    (by simpa only [values] using bodyTyped)
  exact ⟨result,success,resultType,resultTyped,by simpa only [values] using resultTerm⟩

inductive ArgumentsTyped (env : VEnv) (U : Nat) (ctx : List VExpr) :
    VExpr → List VExpr → VExpr → Prop where
  | nil : ArgumentsTyped env U ctx ty [] ty
  | cons : DirectTyping env U ctx argument domain →
      ArgumentsTyped env U ctx (codomain.inst argument) rest result →
      ArgumentsTyped env U ctx (.forallE domain codomain) (argument::rest) result

theorem ArgumentsTyped.withCasts (arguments : ArgumentsTyped env U ctx ty args result)
    (casts : TypeCasts) : ArgumentsCasts env U casts ctx ty args result := by
  induction arguments with
  | nil => exact .nil
  | cons argument _ ih => exact .cons (argument.withCasts casts) ih

theorem ArgumentsTyped.step_complete
    (arguments : ArgumentsTyped env U ctx ty args resultType)
    (closed : ClosedConstantTypes env)
    (function : Result env U ctx source)
    (reduced : step rules conv U ctx exposure source = some function)
    (functionType : function.val.2 = ty)
    (functionTyped : DirectTyping env U ctx function.val.1 ty) :
    ∃ result, step rules conv U ctx exposure (LeanTyped.applications source args) = some result ∧
      result.val.2 = resultType ∧ DirectTyping env U ctx result.val.1 resultType ∧
      result.val.1 = args.foldl applyReduced function.val.1 := by
  obtain ⟨result,success,kind,typed,term⟩ :=
    (arguments.withCasts (fun _ _ _ => False)).step_complete closed
      (fun _ _ _ h => False.elim h) (fun _ _ _ h => False.elim h)
      function reduced functionType (functionTyped.withCasts _)
  exact ⟨result,success,kind,typed.withoutCasts,term⟩

/-- The named-definition reduction used by the final source connection
succeeds for a monomorphic, directly typed body and typed arguments. In
particular it does not assume that the internal body checks succeed. -/
theorem named_application_complete
    (rule : Rule env) (monomorphic : rule.definition.declaration.levelParams = [])
    (bodyTyped : DirectTyping env U ctx rule.definition.body.val rule.definition.type.val)
    (arguments : ArgumentsTyped env U ctx rule.definition.type.val args resultType)
    (closed : ClosedConstantTypes env) (conv : Conversion env) (exposure : Exposure env) :
    ∃ result, step [rule] conv U ctx exposure
        (LeanTyped.applications (.const rule.name []) args) = some result ∧
      result.val.2 = resultType ∧ DirectTyping env U ctx result.val.1 resultType ∧
      result.val.1 = args.foldl applyReduced rule.definition.body.val := by
  obtain ⟨result,success,kind,typed,term⟩ := named_application_cast_complete
    rule monomorphic (bodyTyped.withCasts (fun _ _ _ => False)) (arguments.withCasts _)
    closed (fun _ _ _ h => False.elim h) (fun _ _ _ h => False.elim h) exposure
  exact ⟨result,success,kind,typed.withoutCasts,term⟩

end IRComparison.LeanTypeReduction

namespace IRComparison.LeanTypeAliases
open Lean4Lean LeanTypeInference

/-- The alias converter leaves applications of every other constant alone. -/
theorem Alias.expand_other_head {source : VExpr} (entry : Alias native name)
    (registered : env.defeqs entry.equation)
    (head : LeanTypeReduction.constantHead source = some (other,levels))
    (different : other ≠ name) (base : Conversion env) :
    entry.expand registered U ctx source base = none := by
  unfold Alias.expand
  split
  · rename_i found u arg same
    simp only [LeanTypeReduction.constantHead,Option.some.injEq,Prod.mk.injEq] at head
    simp only [head.1,dif_neg different]
  · rfl

end IRComparison.LeanTypeAliases
