import IRComparison.Frontend.LeanStructuralConversion
import IRComparison.Frontend.LeanRetainedConversion
import IRComparison.Frontend.LeanReductionCompleteness

/-! Transport retained argument lets to the original application. Only the
administrative prefix inserted for actual arguments is traversed; the bound
is the actual argument count, not a fixed normalization/search allowance. -/
namespace IRComparison.WordFrontend.RetainedConversion
open Lean4Lean LeanTyped LeanTypeInference LeanTypeReduction

/-- Proof-side projection of exactly the inserted let prefix. This is not
an input parser or unrestricted normalizer: the telescope supplies the exact
number of scalar slots, and an absent let makes the projection fail. -/
def contractLets : Nat → Lean.Expr → Option Lean.Expr
  | 0, source => some source
  | count+1, .letE _ _ value body _ =>
      contractLets count (LeanBindings.instantiate value body)
  | _+1, _ => none

/-- Captured substitutions commute with an already established let prefix.
This lets the argument induction keep one body derivation rather than repeat
it at every combination of saved and substituted scalar arguments. -/
theorem contractLets_substitute
    (success : contractLets count source = some target) (σ : Nat → Lean.Expr) :
    contractLets count (LeanBindings.substitute σ source) =
      some (LeanBindings.substitute σ target) := by
  induction count generalizing source target σ with
  | zero => simpa only [contractLets,Option.some.injEq] using
      congrArg (LeanBindings.substitute σ) (Option.some.inj success)
  | succ count ih =>
    cases source <;> try cases success
    rename_i name ty value body flag
    simpa only [LeanBindings.substitute,contractLets,← LeanBindings.substitute_instantiate]
      using ih success σ

/-- The same prefix projection on the proof calculus used by conversion. -/
def contractCoreLets : Nat → VExpr → Option VExpr
  | 0, source => some source
  | count+1, .app (.lam _ body) value => contractCoreLets count (body.inst value)
  | _+1, _ => none

theorem contractLets_represents (sourceRep : Represents source core)
    (success : contractLets count source = some target) :
    ∃ result, contractCoreLets count core = some result ∧ Represents target result := by
  induction count generalizing source core target with
  | zero =>
    cases success
    exact ⟨core,rfl,sourceRep⟩
  | succ count ih =>
    cases source <;> try cases success
    cases sourceRep with
    | letE typeRep valueRep bodyRep =>
      exact ih (bodyRep.instantiate valueRep) success

/-- Typed derivation for an administrative let prefix, derived from the
argument telescope and its single endpoint body. This is not an independent
input syntax: it contains no program operations and no successful checker
premise. Unlike an application spine, each binder extends the local context. -/
inductive Prefix (env : VEnv) (U : Nat) (casts : TypeCasts) (ty : VExpr) :
    List VExpr → VExpr → VExpr → Nat → Prop where
  | done (typed : CastTyping env U casts ctx value ty) : Prefix env U casts ty ctx value value 0
  | bind (domainClosed : domain.ClosedN 0)
      (domainTyped : CastTyping env U casts ctx domain (.sort u))
      (argumentTyped : CastTyping env U casts ctx argument domain)
      (body : Prefix env U casts ty (domain::ctx) source target count) :
      Prefix env U casts ty ctx (.app (.lam domain source) argument) (target.inst argument) (count+1)

/-- The syntax of the inserted binders bounds their count. It is independent
of the runtime converter and requires no parser or search success. -/
theorem Prefix.length_le (chain : Prefix env U casts ty ctx source target count) :
    count ≤ prefixLength source := by
  induction chain with
  | done _ => exact Nat.zero_le _
  | bind _ _ _ _ ih => simpa only [prefixLength] using Nat.add_le_add_right ih 1

theorem Prefix.typed (chain : Prefix env U casts ty ctx source target count)
    (resultClosed : ty.ClosedN 0) : CastTyping env U casts ctx source ty := by
  induction chain with
  | done typed => exact typed
  | bind _ domainTyped argumentTyped _ ih =>
    simpa only [resultClosed.instN_eq (Nat.zero_le _)] using
      CastTyping.application (.lambda domainTyped ih) argumentTyped

/-- One common substitution proof handles every already retained argument,
including under later retained slots. No body-specific derivation is copied. -/
theorem Prefix.instN (chain : Prefix env U casts ty before source target count)
    (closed : ClosedConstantTypes env) (stable : ClosedCasts casts) (resultClosed : ty.ClosedN 0)
    (argument : CastTyping env U casts base value domain)
    (substitution : Ctx.InstN base value domain k before after) :
    Prefix env U casts ty after (source.inst value k) (target.inst value k) count := by
  induction chain generalizing after k with
  | done typed =>
    exact .done (by
      simpa only [resultClosed.instN_eq (Nat.zero_le _)] using
        typed.instN closed stable argument substitution)
  | @bind before binder u actual source target count binderClosed binderTyped actualTyped body ih =>
    have bt := binderTyped.instN closed stable argument substitution
    have argTyped := actualTyped.instN closed stable argument substitution
    have tail := ih substitution.succ
    simp only [binderClosed.instN_eq (Nat.zero_le _),VExpr.inst] at bt argTyped tail
    have result := Prefix.bind binderClosed bt argTyped tail
    simpa only [VExpr.inst,binderClosed.instN_eq (Nat.zero_le _),VExpr.inst0_inst_hi] using result

/-- Compose the two reduction induction hypotheses at the certificate's
equality prefix. Prefix typing is independent of the compiler; inference
success is derived here, rather than required from each call-site proof. -/
theorem conversion_complete {level : VLevel}
    {reduced : LeanTypeReduction.Result env U ctx right}
    (rightStep : step [] conv U ctx exposure right = some reduced)
    {equality : PLift (env.IsDefEq U ctx left reduced.val.1 reduced.val.2)}
    (leftSteps : reducePrefix conv exposure U ctx reduced.val.1 reduced.val.2
      (reduced.property.symm.trans reduced.property) count left = some equality)
    (headTyped : CastTyping env U casts ctx head (.forallE reduced.val.2 codomain))
    (resultSort : codomain.inst left = .sort level)
    (coverage : Conversion.Covers conv U casts) :
    ∃ result, conversion conv exposure count U ctx (.app head left) (.app head right) = some result := by
  obtain ⟨⟨inferred,proof⟩,inferredEq,same⟩ := headTyped.infer_complete
    (known := noKnownTypes env U) (by intro e actual result he; cases he) coverage exposure
  dsimp only at same
  subst inferred
  simp only [conversion,dif_pos rfl,rightStep,leftSteps,inferredEq,
    bind,Option.bind,resultSort,pure,Option.pure_def,dite_true]
  split
  · exact ⟨_,rfl⟩
  · rename_i other evidence impossible
    exact False.elim (impossible level (resultSort ▸ evidence) resultSort (proof_irrel_heq _ _))

/-- Reflexive endpoint needs no allowance and no typechecker call. -/
theorem prefix_endpoint (conv : Conversion env) (exposure : Exposure env)
    (typed : env.HasType U ctx target ty) (count : Nat) :
    reducePrefix conv exposure U ctx target ty typed count target = some ⟨typed⟩ := by
  rw [reducePrefix.eq_def]
  simp

/-- One inserted scalar let consumes exactly one prefix step. The recursive
premise is the argument-telescope induction hypothesis, not an assumption
that the whole source parser or converter succeeds. -/
theorem reducePrefix_checkedBeta {body : VExpr}
    (bodyTyped : CastTyping env U casts (domain::ctx) body bodyType)
    (argumentTyped : CheckedTyping env U casts ctx argument domain)
    (coverage : Conversion.Covers conv U casts) (exposure : Exposure env)
    (targetTyped : env.HasType U ctx target (bodyType.inst argument))
    {rest : PLift (env.IsDefEq U ctx (body.inst argument) target (bodyType.inst argument))}
    (remaining : reducePrefix conv exposure U ctx target (bodyType.inst argument)
      targetTyped count (body.inst argument) = some rest) :
    ∃ result, reducePrefix conv exposure U ctx target (bodyType.inst argument)
      targetTyped (count+1) (.app (.lam domain body) argument) = some result := by
  by_cases same : VExpr.app (.lam domain body) argument = target
  · subst target
    exact ⟨_,prefix_endpoint conv exposure targetTyped _⟩
  · obtain ⟨stepResult,stepped,stepValue⟩ := step_beta_checked_complete bodyTyped argumentTyped coverage [] exposure
    rw [reducePrefix.eq_def]
    simp only [same,not_false_eq_true,dif_neg,stepped,bind,Option.bind]
    obtain ⟨⟨value,ty⟩,proof⟩ := stepResult
    dsimp only at stepValue
    cases stepValue
    simp only [dif_pos rfl,remaining,pure,Option.pure_def,bind,Option.bind]
    exact ⟨_,rfl⟩

/-- Exact-typed arguments are a specialization of the same binder proof.
The checked variant also covers Word/BitVec 32 conversion at the binder. -/
theorem reducePrefix_beta {body : VExpr}
    (bodyTyped : CastTyping env U casts (domain::ctx) body bodyType)
    (argumentTyped : CastTyping env U casts ctx argument domain)
    (coverage : Conversion.Covers conv U casts) (exposure : Exposure env)
    (targetTyped : env.HasType U ctx target (bodyType.inst argument))
    {rest : PLift (env.IsDefEq U ctx (body.inst argument) target (bodyType.inst argument))}
    (remaining : reducePrefix conv exposure U ctx target (bodyType.inst argument)
      targetTyped count (body.inst argument) = some rest) :
    ∃ result, reducePrefix conv exposure U ctx target (bodyType.inst argument)
      targetTyped (count+1) (.app (.lam domain body) argument) = some result :=
  reducePrefix_checkedBeta bodyTyped (.exact argumentTyped) coverage exposure targetTyped remaining

/-- The typed let derivation supplies every intermediate check. Its exact
scalar-slot count suffices for the running converter; no successful check
or manually typed intermediate program is required by this theorem. -/
theorem Prefix.complete
    (chain : Prefix env U casts ty ctx source target count)
    (closed : ClosedConstantTypes env) (stable : ClosedCasts casts) (resultClosed : ty.ClosedN 0)
    (coverage : Conversion.Covers conv U casts) (exposure : Exposure env)
    (targetTyped : env.HasType U ctx target ty) :
    ∃ result, reducePrefix conv exposure U ctx target ty targetTyped count source = some result := by
  induction count generalizing ctx source target with
  | zero =>
    cases chain with
    | done typed => exact ⟨_,prefix_endpoint conv exposure targetTyped 0⟩
  | succ count ih =>
    cases chain with
    | @bind _ domain u argument body endpoint _ domainClosed domainTyped argumentTyped tail =>
      have substituted := tail.instN closed stable resultClosed argumentTyped Ctx.InstN.zero
      obtain ⟨rest,remaining⟩ := ih substituted targetTyped
      have beta : ∀ (ht : env.HasType U ctx (endpoint.inst argument) (ty.inst argument))
          (r : PLift (env.IsDefEq U ctx (body.inst argument) (endpoint.inst argument) (ty.inst argument))),
          reducePrefix conv exposure U ctx (endpoint.inst argument) (ty.inst argument) ht
            count (body.inst argument) = some r →
          ∃ result, reducePrefix conv exposure U ctx (endpoint.inst argument) (ty.inst argument) ht
            (count+1) (.app (.lam domain body) argument) = some result := by
        intro ht r hr
        exact reducePrefix_beta (tail.typed resultClosed) argumentTyped coverage exposure ht hr
      have typeEq : ty.inst argument = ty := resultClosed.instN_eq (Nat.zero_le _)
      rw [typeEq] at beta
      exact beta targetTyped rest remaining

/-- Additional actuals that need no scalar binding do not invalidate a
prefix proof. The caller can use the whole argument count as an upper bound. -/
theorem reducePrefix_mono {env : VEnv} {conv : Conversion env} {exposure : Exposure env}
    {U : Nat} {ctx : List VExpr} {target ty source : VExpr} {count limit : Nat}
    {result : PLift (env.IsDefEq U ctx source target ty)}
    (typed : env.HasType U ctx target ty)
    (success : reducePrefix conv exposure U ctx target ty typed count source = some result)
    (enough : count ≤ limit) :
    ∃ next, reducePrefix conv exposure U ctx target ty typed limit source = some next := by
  induction count generalizing source limit with
  | zero =>
    rw [reducePrefix.eq_def] at success
    dsimp only at success
    split at success
    · rename_i same; subst source
      exact ⟨_,prefix_endpoint conv exposure typed _⟩
    · simp at success
  | succ count ih =>
    rw [reducePrefix.eq_def] at success
    dsimp only at success
    split at success
    · rename_i same; subst source
      exact ⟨_,prefix_endpoint conv exposure typed _⟩
    · rename_i different
      cases limit with
      | zero => omega
      | succ limit =>
        cases firstEq : step [] conv U ctx exposure source with
        | none => simp [firstEq] at success
        | some first =>
          simp only [firstEq,bind,Option.bind] at success
          split at success
          · rename_i sameType
            cases tailEq : reducePrefix conv exposure U ctx target ty typed count first.val.1 with
            | none => simp [tailEq] at success
            | some tail =>
              obtain ⟨next,nextEq⟩ := ih (limit := limit) tailEq (by omega)
              rw [reducePrefix.eq_def]
              simp only [different,dif_neg,firstEq,bind,Option.bind,sameType,dif_pos,nextEq,pure,Option.pure_def,if_false,if_true,dite_false,dite_true]
              exact ⟨⟨(sameType ▸ first.property).trans next.down⟩,trivial⟩
          · simp at success

/-- The converter's whole actual-argument count covers its scalar prefix.
All intermediate typing and reduction checks follow from the one prefix
induction; they are not independent obligations at each helper call. -/
theorem conversion_of_prefix {level : VLevel}
    {reduced : LeanTypeReduction.Result env U ctx right}
    (rightStep : step [] conv U ctx exposure right = some reduced)
    (chain : Prefix env U casts reduced.val.2 ctx left reduced.val.1 count)
    (closed : ClosedConstantTypes env) (stable : ClosedCasts casts)
    (resultClosed : reduced.val.2.ClosedN 0)
    (headTyped : CastTyping env U casts ctx head (.forallE reduced.val.2 codomain))
    (resultSort : codomain.inst left = .sort level)
    (coverage : Conversion.Covers conv U casts) (enough : count ≤ limit) :
    ∃ result, conversion conv exposure limit U ctx (.app head left) (.app head right) = some result := by
  obtain ⟨equality,success⟩ := chain.complete closed stable resultClosed coverage exposure
    (reduced.property.symm.trans reduced.property)
  obtain ⟨next,expanded⟩ := reducePrefix_mono _ success enough
  exact conversion_complete rightStep expanded headTyped resultSort coverage

/-- Discharge the original application's reduction from independent checked
argument types. This covers Word/BitVec aliases and arbitrary arity, and
connects the retained-prefix proof to the actual conversion function. -/
theorem conversion_checked_call {level : VLevel}
    (bodyTyped : CastTyping env U casts (domain::ctx) body (domains.foldr VExpr.forallE resultType))
    (firstTyped : CheckedTyping env U casts ctx first domain)
    (arguments : List.Forall₂ (fun domain arg => CheckedTyping env U casts ctx arg domain) domains args)
    (typesClosed : ∀ n, ((domains.drop n).foldr VExpr.forallE resultType).ClosedN 0)
    (prefixTyped : ∀ before after, args = before ++ after → after ≠ [] →
      CastTyping env U casts ctx (before.foldl applyReduced (body.inst first))
        ((domains.drop before.length).foldr VExpr.forallE resultType))
    (chain : Prefix env U casts resultType ctx left
      (args.foldl applyReduced (body.inst first)) count)
    (closed : ClosedConstantTypes env) (stable : ClosedCasts casts)
    (resultClosed : resultType.ClosedN 0)
    (headTyped : CastTyping env U casts ctx head (.forallE resultType codomain))
    (resultSort : codomain.inst left = .sort level)
    (coverage : Conversion.Covers conv U casts) (exposure : Exposure env) (enough : count ≤ limit) :
    ∃ result, conversion conv exposure limit U ctx (.app head left)
      (.app head (applications (.app (.lam domain body) first) args)) = some result := by
  obtain ⟨initial,initialStep,initialValue⟩ := step_beta_checked_complete bodyTyped firstTyped coverage [] exposure
  have functionValue := congrArg Prod.fst initialValue
  have functionType : initial.val.2 = domains.foldr VExpr.forallE resultType := by
    have closedType := typesClosed 0
    simp only [List.drop_zero] at closedType
    simpa only [closedType.instN_eq (Nat.zero_le _)] using congrArg Prod.snd initialValue
  obtain ⟨reduced,reducedStep,reducedType,reducedValue⟩ := step_checked_spine_complete
    arguments typesClosed prefixTyped coverage initial initialStep functionType functionValue
  apply conversion_of_prefix reducedStep
    (by simpa only [reducedType,reducedValue] using chain) closed stable
    (by simpa only [reducedType] using resultClosed)
    (by simpa only [reducedType] using headTyped) resultSort coverage enough

end IRComparison.WordFrontend.RetainedConversion
