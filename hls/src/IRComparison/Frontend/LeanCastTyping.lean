import IRComparison.Frontend.LeanTypingCompleteness

/-! Completeness for fact applications that use type conversion, for example
`Word` versus `BitVec 32` below an arithmetic typeclass. The conversion relation
is specified independently of inference. Its coverage by the actual converter
is a separate obligation, never a new definition of accepted HLS syntax. -/
namespace IRComparison.LeanTypeInference
open Lean4Lean

abbrev TypeCasts := List VExpr → VExpr → VExpr → Prop

inductive CastTyping (env : VEnv) (U : Nat) (casts : TypeCasts) :
    List VExpr → VExpr → VExpr → Prop where
  | bvar : Lookup ctx n ty → CastTyping env U casts ctx (.bvar n) ty
  | sort : u.WF U → CastTyping env U casts ctx (.sort u) (.sort (.succ u))
  | constant : env.constants name = some info →
      (∀ u ∈ levels, u.WF U) → levels.length = info.uvars →
      CastTyping env U casts ctx (.const name levels) (info.type.instL levels)
  | application : CastTyping env U casts ctx f (.forallE domain codomain) →
      CastTyping env U casts ctx arg domain →
      CastTyping env U casts ctx (.app f arg) (codomain.inst arg)
  | convertedApplication : CastTyping env U casts ctx f (.forallE domain codomain) →
      CastTyping env U casts ctx arg actual → casts ctx actual domain →
      CastTyping env U casts ctx (.app f arg) (codomain.inst arg)
  | functionApplication : CastTyping env U casts ctx f actual →
      (view : functionTypeView actual = some (.forallE domain codomain)) →
      casts ctx actual (.forallE domain codomain) →
      CastTyping env U casts ctx arg domain →
      CastTyping env U casts ctx (.app f arg) (codomain.inst arg)
  | lambda : CastTyping env U casts ctx domain (.sort u) →
      CastTyping env U casts (domain::ctx) body ty →
      CastTyping env U casts ctx (.lam domain body) (.forallE domain ty)
  | forallType : CastTyping env U casts ctx domain (.sort u) →
      CastTyping env U casts (domain::ctx) body (.sort v) →
      CastTyping env U casts ctx (.forallE domain body) (.sort (.imax u v))

theorem DirectTyping.withCasts (typed : DirectTyping env U ctx e ty) (casts : TypeCasts) :
    CastTyping env U casts ctx e ty := by
  induction typed with
  | bvar h => exact .bvar h
  | sort h => exact .sort h
  | constant h levels arity => exact .constant h levels arity
  | application _ _ f a => exact .application f a
  | lambda _ _ d b => exact .lambda d b
  | forallType _ _ d b => exact .forallType d b

/-- Enlarge the independently specified conversion relation without changing
any term or its inferred type. Source-type casts and certificate-only beta
conversions can thus be kept separate. -/
theorem CastTyping.mono (typed : CastTyping env U casts ctx e ty)
    (embeds : ∀ scope a b, casts scope a b → other scope a b) :
    CastTyping env U other ctx e ty := by
  induction typed with
  | bvar h => exact .bvar h
  | sort h => exact .sort h
  | constant h levels arity => exact .constant h levels arity
  | application _ _ f a => exact .application f a
  | convertedApplication _ _ cast f a => exact .convertedApplication f a (embeds _ _ _ cast)
  | functionApplication _ view cast _ f a => exact .functionApplication f view (embeds _ _ _ cast) a
  | lambda _ _ d b => exact .lambda d b
  | forallType _ _ d b => exact .forallType d b

/-- With no allowed casts this is exactly the original direct judgment. -/
theorem CastTyping.withoutCasts (typed : CastTyping env U (fun _ _ _ => False) ctx e ty) :
    DirectTyping env U ctx e ty := by
  induction typed with
  | bvar h => exact .bvar h
  | sort h => exact .sort h
  | constant h levels arity => exact .constant h levels arity
  | application _ _ f a => exact .application f a
  | convertedApplication _ _ impossible => exact False.elim impossible
  | functionApplication _ _ impossible _ => exact False.elim impossible
  | lambda _ _ d b => exact .lambda d b
  | forallType _ _ d b => exact .forallType d b

/-- These arithmetic casts relate closed types and are independent of local
bindings. This lets source proofs cross lets and loop binders unchanged. -/
def ClosedCasts (casts : TypeCasts) : Prop :=
  ∀ ctx actual expected, casts ctx actual expected →
    actual.ClosedN 0 ∧ expected.ClosedN 0 ∧ ∀ scope, casts scope actual expected

private theorem lookup_replace_suffix (kept : List VExpr)
    (found : Lookup (kept ++ before) n ty) (inside : n < kept.length) (after : List VExpr) :
    Lookup (kept ++ after) n ty := by
  induction kept generalizing n ty with
  | nil => simp at inside
  | cons binder rest ih =>
    cases found with
    | zero => exact .zero
    | succ found => exact .succ (ih found (by simpa using inside))

/-- A term referring only to the retained binders has exactly the same typing
under any outer scope. This also permits a closed generated IR quotation to
move out of a source continuation without rechecking it. -/
theorem CastTyping.replace_context_suffix (typed : CastTyping env U casts ctx e ty)
    (stable : ClosedCasts casts) (kept before after : List VExpr)
    (contextEq : ctx = kept ++ before) (scope : e.ClosedN kept.length) :
    CastTyping env U casts (kept ++ after) e ty := by
  induction typed generalizing kept with
  | bvar found => exact .bvar (lookup_replace_suffix kept (contextEq ▸ found) scope after)
  | sort wf => exact .sort wf
  | constant found levels arity => exact .constant found levels arity
  | application _ _ ihf iha => exact .application (ihf kept contextEq scope.1) (iha kept contextEq scope.2)
  | convertedApplication _ _ cast ihf iha =>
    exact .convertedApplication (ihf kept contextEq scope.1) (iha kept contextEq scope.2)
      ((stable _ _ _ cast).2.2 _)
  | functionApplication _ view cast _ ihf iha =>
    exact .functionApplication (ihf kept contextEq scope.1) view ((stable _ _ _ cast).2.2 _) (iha kept contextEq scope.2)
  | lambda _ _ ihd ihb =>
    exact .lambda (ihd kept contextEq scope.1)
      (ihb (_::kept) (by simp only [contextEq,List.cons_append]) scope.2)
  | forallType _ _ ihd ihb =>
    exact .forallType (ihd kept contextEq scope.1)
      (ihb (_::kept) (by simp only [contextEq,List.cons_append]) scope.2)

theorem CastTyping.closed_context (typed : CastTyping env U casts ctx e ty)
    (stable : ClosedCasts casts) (scope : e.ClosedN 0) (next : List VExpr) :
    CastTyping env U casts next e ty :=
  typed.replace_context_suffix stable [] ctx next rfl scope

theorem CastTyping.weakN (typed : CastTyping env U casts ctx e ty)
    (closed : ClosedConstantTypes env) (stable : ClosedCasts casts) (extension : Ctx.LiftN n k ctx next) :
    CastTyping env U casts next (e.liftN n k) (ty.liftN n k) := by
  induction typed generalizing k next with
  | bvar found => exact .bvar (found.weakN extension)
  | sort wf => exact .sort wf
  | constant found levels arity =>
    rw [(closed _ _ found).instL.liftN_eq (Nat.zero_le _)]
    exact .constant found levels arity
  | application _ _ ihf iha =>
    exact VExpr.liftN_inst_hi .. ▸ .application (ihf extension) (iha extension)
  | convertedApplication _ _ cast ihf iha =>
    refine VExpr.liftN_inst_hi .. ▸ .convertedApplication (ihf extension) (iha extension) ?_
    simpa only [(stable _ _ _ cast).1.liftN_eq (Nat.zero_le k),
      (stable _ _ _ cast).2.1.liftN_eq (Nat.zero_le k)] using (stable _ _ _ cast).2.2 next
  | functionApplication _ view cast _ ihf iha =>
    have a := (stable _ _ _ cast).1.liftN_eq (n := n) (Nat.zero_le k)
    have b := (stable _ _ _ cast).2.1.liftN_eq (n := n) (Nat.zero_le k)
    simp only [VExpr.liftN] at b
    refine VExpr.liftN_inst_hi .. ▸ .functionApplication (ihf extension) ?_ ?_ (iha extension)
    · simpa only [a, b] using view
    · simpa only [a, b] using (stable _ _ _ cast).2.2 next
  | lambda _ _ ihd ihb => exact .lambda (ihd extension) (ihb extension.succ)
  | forallType _ _ ihd ihb => exact .forallType (ihd extension) (ihb extension.succ)

theorem CastTyping.lift (typed : CastTyping env U casts ctx e ty)
    (closed : ClosedConstantTypes env) (stable : ClosedCasts casts) (binder : VExpr) :
    CastTyping env U casts (binder::ctx) e.lift ty.lift :=
  typed.weakN closed stable .one

/-- Substituting an already typed value preserves direct typing, including
under nested binders. No fixed bound on binding depth is involved. -/
theorem CastTyping.instN (typed : CastTyping env U casts before e ty)
    (closed : ClosedConstantTypes env) (stable : ClosedCasts casts) (argument : CastTyping env U casts base value domain)
    (substitution : Ctx.InstN base value domain k before after) :
    CastTyping env U casts after (e.inst value k) (ty.inst value k) := by
  induction typed generalizing after k with
  | @bvar _ i ty found =>
    dsimp [VExpr.inst]
    induction substitution generalizing i ty with
    | zero =>
      cases found with simp [VExpr.inst_lift]
      | zero => exact argument
      | succ found => exact .bvar found
    | succ _ ih =>
      cases found with
          (simp; rw [Nat.add_comm,← VExpr.liftN_instN_lo (hj := Nat.zero_le _)])
      | zero => exact .bvar .zero
      | succ found => exact (ih found).lift closed stable _
  | sort wf => exact .sort wf
  | constant found levels arity =>
    rw [(closed _ _ found).instL.instN_eq (Nat.zero_le _)]
    exact .constant found levels arity
  | application _ _ ihf iha =>
    exact VExpr.inst_inst_hi .. ▸ .application (ihf substitution) (iha substitution)
  | convertedApplication _ _ cast ihf iha =>
    refine VExpr.inst_inst_hi .. ▸ .convertedApplication (ihf substitution) (iha substitution) ?_
    simpa only [(stable _ _ _ cast).1.instN_eq (Nat.zero_le k),
      (stable _ _ _ cast).2.1.instN_eq (Nat.zero_le k)] using (stable _ _ _ cast).2.2 after
  | functionApplication _ view cast _ ihf iha =>
    have a := (stable _ _ _ cast).1.instN_eq (e2 := value) (Nat.zero_le k)
    have b := (stable _ _ _ cast).2.1.instN_eq (e2 := value) (Nat.zero_le k)
    simp only [VExpr.inst] at b
    refine VExpr.inst_inst_hi .. ▸ .functionApplication (ihf substitution) ?_ ?_ (iha substitution)
    · simpa only [a, b] using view
    · simpa only [a, b] using (stable _ _ _ cast).2.2 after
  | lambda _ _ ihd ihb => exact .lambda (ihd substitution) (ihb substitution.succ)
  | forallType _ _ ihd ihb => exact .forallType (ihd substitution) (ihb substitution.succ)

theorem CastTyping.instantiate (typed : CastTyping env U casts (domain::ctx) body ty)
    (closed : ClosedConstantTypes env) (stable : ClosedCasts casts) (argument : CastTyping env U casts ctx value domain) :
    CastTyping env U casts ctx (body.inst value) (ty.inst value) :=
  typed.instN closed stable argument .zero

theorem CastTyping.closed_term (typed : CastTyping env U casts ctx e ty) :
    e.ClosedN ctx.length := by
  induction typed with
  | bvar found => exact found.lt
  | sort | constant => trivial
  | application _ _ ihf iha | convertedApplication _ _ _ ihf iha | functionApplication _ _ _ _ ihf iha => exact ⟨ihf,iha⟩
  | lambda _ _ ihd ihb | forallType _ _ ihd ihb => exact ⟨ihd,ihb⟩

/-- A closed, directly typed declaration can be used under any input scope. -/
theorem CastTyping.in_context (typed : CastTyping env U casts [] e ty)
    (closed : ClosedConstantTypes env) (stable : ClosedCasts casts) (typeClosed : ty.ClosedN 0) (ctx : List VExpr) :
    CastTyping env U casts ctx e ty := by
  induction ctx with
  | nil => exact typed
  | cons binder rest ih =>
    simpa only [typed.closed_term.lift_eq,typeClosed.lift_eq] using ih.lift closed stable binder

/-- Casts affect argument checking, not the inferred result type. -/
theorem CastTyping.unique (first : CastTyping env U casts ctx e a)
    (second : CastTyping env U casts ctx e b) : a = b := by
  induction first generalizing b with
  | bvar found => cases second with | bvar other => exact found.uniq other
  | sort => cases second; rfl
  | constant found levels arity =>
    cases second with
    | constant other _ _ =>
      have same := Option.some.inj (found.symm.trans other)
      cases same
      rfl
  | application _ _ ihf _ | convertedApplication _ _ _ ihf _ =>
    cases second with
    | application f a | convertedApplication f a _ =>
      have same := ihf f
      cases same
      rfl
    | functionApplication f view _ _ =>
      have same := ihf f
      rw [← same] at view
      cases view
  | functionApplication _ view _ _ ihf _ =>
    cases second with
    | application f a | convertedApplication f a _ =>
      have same := ihf f
      rw [same] at view
      cases view
    | functionApplication f other _ _ =>
      have same := ihf f
      rw [← same] at other
      have shapes := Option.some.inj (view.symm.trans other)
      cases shapes
      rfl
  | lambda _ _ _ ihb =>
    cases second with
    | lambda _ b => exact congrArg _ (ihb b)
  | forallType _ _ ihd ihb =>
    cases second with
    | forallType d b =>
      have hd := ihd d
      have hb := ihb b
      cases hd
      cases hb
      rfl

def KnownTypes.Casts (known : KnownTypes env U) (casts : TypeCasts) : Prop :=
  ∀ ctx e result, known ctx e = some result → CastTyping env U casts ctx e result.val

theorem KnownTypes.Direct.withCasts (direct : KnownTypes.Direct known) (casts : TypeCasts) :
    KnownTypes.Casts known casts :=
  fun ctx e result hit => (direct ctx e result hit).withCasts casts

theorem KnownTypes.Casts.orElse
    (first : KnownTypes.Casts a casts) (second : KnownTypes.Casts b casts) :
    KnownTypes.Casts (a.orElse b) casts := by
  intro ctx e result found
  cases ha : a ctx e with
  | none => exact second ctx e result (by simpa [KnownTypes.orElse,ha] using found)
  | some hit =>
    have eqn : hit = result := by simpa [KnownTypes.orElse,ha] using found
    subst result
    exact first ctx e hit ha

/-- A local coverage obligation on the type-conversion service. A source
grammar must derive its casts and discharge this obligation for the installed
converter; inference success itself is not a constructor of CastTyping. -/
def Conversion.Covers (conv : Conversion env) (U : Nat) (casts : TypeCasts) : Prop :=
  ∀ ctx actual expected, casts ctx actual expected →
    ∃ result, conv U ctx actual expected = some result

private theorem cache_or_miss (typed : CastTyping env U casts ctx e ty)
    (coherent : KnownTypes.Casts known casts)
    (conv : Conversion env) (exposure : Exposure env)
    (miss : known ctx e = none → ∃ result,
      inferWith env conv U ctx e exposure known = some result ∧ result.val = ty) :
    ∃ result, inferWith env conv U ctx e exposure known = some result ∧ result.val = ty := by
  cases cached : known ctx e with
  | none => exact miss cached
  | some result =>
    exact ⟨result,by rw [inferWith.eq_def,cached],(coherent ctx e result cached).unique typed⟩

theorem CastTyping.infer_complete (typed : CastTyping env U casts ctx e ty)
    (coherent : KnownTypes.Casts known casts) (coverage : conv.Covers U casts)
    (exposure : Exposure env) :
    ∃ result, inferWith env conv U ctx e exposure known = some result ∧ result.val = ty := by
  induction typed with
  | bvar found =>
    apply cache_or_miss (.bvar found) coherent conv exposure
    intro missing
    obtain ⟨result,success,same⟩ := lookup_complete found
    simp only [inferWith,missing,success,bind,Option.bind]
    exact ⟨_,rfl,same⟩
  | sort wf =>
    apply cache_or_miss (.sort wf) coherent conv exposure
    intro missing
    simp only [inferWith,missing,dif_pos wf]
    exact ⟨_,rfl,rfl⟩
  | constant registered levels arity =>
    apply cache_or_miss (.constant registered levels arity) coherent conv exposure
    intro missing
    simp only [inferWith,missing]
    split
    · rename_i absent
      rw [registered] at absent
      contradiction
    · rename_i info found
      have eqn := Option.some.inj (found.symm.trans registered)
      subst info
      simp only [dif_pos levels,dif_pos arity]
      exact ⟨_,rfl,rfl⟩
  | application first second ihf iha =>
    apply cache_or_miss (.application first second) coherent conv exposure
    intro missing
    obtain ⟨⟨ft,hf⟩,hfirst,eqf⟩ := ihf
    obtain ⟨⟨argTy,ha⟩,hsecond,eqa⟩ := iha
    dsimp only at eqf eqa
    subst ft; subst argTy
    simp only [inferWith,missing,hfirst,hsecond,bind,Option.bind,dif_pos rfl]
    exact ⟨_,rfl,rfl⟩
  | @convertedApplication ctx f domain codomain arg actual first second cast ihf iha =>
    apply cache_or_miss (.convertedApplication first second cast) coherent conv exposure
    intro missing
    obtain ⟨⟨ft,hf⟩,hfirst,eqf⟩ := ihf
    obtain ⟨⟨argTy,ha⟩,hsecond,eqa⟩ := iha
    dsimp only at eqf eqa
    subst ft; subst argTy
    by_cases same : actual = domain
    · simp only [inferWith,missing,hfirst,hsecond,bind,Option.bind,dif_pos same]
      exact ⟨_,rfl,rfl⟩
    · obtain ⟨converted,success⟩ := coverage ctx actual domain cast
      simp only [inferWith,missing,hfirst,hsecond,bind,Option.bind,dif_neg same,success]
      exact ⟨_,rfl,rfl⟩
  | @functionApplication ctx f actual domain codomain arg first view cast second ihf iha =>
    apply cache_or_miss (.functionApplication first view cast second) coherent conv exposure
    intro missing
    obtain ⟨⟨ft,hf⟩,hfirst,eqf⟩ := ihf
    obtain ⟨⟨argTy,ha⟩,hsecond,eqa⟩ := iha
    dsimp only at eqf eqa
    subst ft; subst argTy
    obtain ⟨converted,accepted⟩ := coverage ctx actual (.forallE domain codomain) cast
    have nonforall := functionTypeView_not_forall view
    cases actual <;> try { exact False.elim (nonforall _ _ rfl) }
    all_goals
      simp only [inferWith,missing,hfirst,view,accepted,hsecond,bind,Option.bind,dif_pos rfl]
      exact ⟨_,rfl,rfl⟩
  | lambda domain body ihd ihb =>
    apply cache_or_miss (.lambda domain body) coherent conv exposure
    intro missing
    obtain ⟨⟨dt,hd⟩,first,eqd⟩ := ihd
    obtain ⟨⟨bt,hb⟩,second,eqb⟩ := ihb
    dsimp only at eqd eqb
    subst dt; subst bt
    simp only [inferWith,missing,first,second,bind,Option.bind]
    exact ⟨_,rfl,rfl⟩
  | forallType domain body ihd ihb =>
    apply cache_or_miss (.forallType domain body) coherent conv exposure
    intro missing
    obtain ⟨⟨dt,hd⟩,first,eqd⟩ := ihd
    obtain ⟨⟨bt,hb⟩,second,eqb⟩ := ihb
    dsimp only at eqd eqb
    subst dt; subst bt
    simp only [inferWith,missing,first,second,bind,Option.bind]
    exact ⟨_,rfl,rfl⟩

theorem CastTyping.check_complete (typed : CastTyping env U casts ctx e ty)
    (coherent : KnownTypes.Casts known casts) (coverage : conv.Covers U casts)
    (exposure : Exposure env) :
    ∃ result, checkWith env conv U ctx e ty exposure known = some result := by
  obtain ⟨⟨actual,h⟩,success,same⟩ := typed.infer_complete coherent coverage exposure
  dsimp only at same
  subst actual
  simp only [checkWith,success,bind,Option.bind,dif_pos rfl]
  exact ⟨_,rfl⟩

private theorem cache_or_kind (typed : CastTyping env U casts ctx e ty)
    (coherent : KnownTypes.Casts known casts)
    (miss : known ctx e = none → ∀ result,
      inferWith env conv U ctx e exposure known = some result → result.val = ty)
    (result : {ty // env.HasType U ctx e ty})
    (success : inferWith env conv U ctx e exposure known = some result) : result.val = ty := by
  cases cached : known ctx e with
  | none => exact miss cached result success
  | some hit =>
    have same : hit = result := by
      rw [inferWith.eq_def,cached] at success
      exact Option.some.inj success
    subst result
    exact (coherent ctx e hit cached).unique typed

private theorem application_inferred_kind {env : VEnv} {U : Nat} {known : KnownTypes env U}
    {conv : Conversion env} {exposure : Exposure env} {ctx : List VExpr} {f a domain codomain : VExpr}
    (missing : known ctx (.app f a) = none)
    (functionKind : ∀ result, inferWith env conv U ctx f exposure known = some result →
      result.val = .forallE domain codomain)
    (result : {ty // env.HasType U ctx (.app f a) ty})
    (success : inferWith env conv U ctx (.app f a) exposure known = some result) :
    result.val = codomain.inst a := by
  cases first : inferWith env conv U ctx f exposure known with
  | none => simp [inferWith,missing,first] at success
  | some fn =>
    rcases fn with ⟨ft,hf⟩
    have same := functionKind _ first
    dsimp only at same
    subst ft
    cases second : inferWith env conv U ctx a exposure known with
    | none => simp [inferWith,missing,first,second] at success
    | some arg =>
      rcases arg with ⟨argTy,ha⟩
      simp only [inferWith,missing,first,second,bind,Option.bind] at success
      split at success
      · cases success; rfl
      · cases converted : conv U ctx argTy domain with
        | none => simp [converted] at success
        | some cast => simp only [converted,Option.bind_some] at success; cases success; rfl

private theorem applied_view_kind {env : VEnv} {U : Nat} {known : KnownTypes env U}
    {conv : Conversion env} {exposure : Exposure env} {ctx : List VExpr} {f a domain codomain : VExpr}
    (hf : env.HasType U ctx f (.forallE domain codomain))
    (result : {ty // env.HasType U ctx (.app f a) ty})
    (success : (do
      let arg ← inferWith env conv U ctx a exposure known
      if same : arg.val = domain then
        pure (⟨codomain.inst a, .app hf (same ▸ arg.property)⟩ : {ty // env.HasType U ctx (.app f a) ty})
      else do
        let cast ← conv U ctx arg.val domain
        pure ⟨codomain.inst a, .app hf (.defeq cast.property arg.property)⟩) = some result) :
    result.val = codomain.inst a := by
  cases argument : inferWith env conv U ctx a exposure known with
  | none => simp [argument] at success
  | some arg =>
    simp only [argument,bind,Option.bind] at success
    split at success
    · cases success; rfl
    · cases cast : conv U ctx arg.val domain with
      | none => simp [cast] at success
      | some c => simp only [cast,bind,Option.bind,pure,Option.pure_def] at success; cases success; rfl

private theorem function_application_inferred_kind {env : VEnv} {U : Nat} {known : KnownTypes env U}
    {conv : Conversion env} {exposure : Exposure env} {ctx : List VExpr} {f a actual domain codomain : VExpr}
    (missing : known ctx (.app f a) = none)
    (functionKind : ∀ result, inferWith env conv U ctx f exposure known = some result → result.val = actual)
    (view : functionTypeView actual = some (.forallE domain codomain))
    (result : {ty // env.HasType U ctx (.app f a) ty})
    (success : inferWith env conv U ctx (.app f a) exposure known = some result) :
    result.val = codomain.inst a := by
  cases first : inferWith env conv U ctx f exposure known with
  | none => simp [inferWith,missing,first] at success
  | some fn =>
    rcases fn with ⟨ft,hf⟩
    have same := functionKind _ first
    dsimp only at same
    subst ft
    cases converted : conv U ctx actual (.forallE domain codomain) with
    | none =>
      cases expanded : exposure U ctx actual with
      | none =>
        have nonforall := functionTypeView_not_forall view
        cases actual <;> try { exact False.elim (nonforall _ _ rfl) }
        all_goals simp [inferWith,missing,first,view,converted,expanded] at success
      | some unfolded =>
        rcases unfolded with ⟨⟨target,level⟩,proof⟩
        by_cases same : target = .forallE domain codomain
        · subst target
          apply applied_view_kind (.defeq proof hf) result
          have nonforall := functionTypeView_not_forall view
          cases actual <;> try { exact False.elim (nonforall _ _ rfl) }
          all_goals simpa only [inferWith,missing,first,view,converted,expanded,bind,Option.bind,dif_pos rfl] using success
        · have nonforall := functionTypeView_not_forall view
          cases actual <;> try { exact False.elim (nonforall _ _ rfl) }
          all_goals simp [inferWith,missing,first,view,converted,expanded,same] at success
    | some cast =>
      apply applied_view_kind (.defeq cast.property hf) result
      have nonforall := functionTypeView_not_forall view
      cases actual <;> try { exact False.elim (nonforall _ _ rfl) }
      all_goals simpa only [inferWith,missing,first,view,converted,bind,Option.bind] using success

/-- A successful inference on an independently typed term has the specified
syntactic type even if the converter is not complete. This is useful when
showing that failed speculative type reductions cannot change value types. -/
theorem CastTyping.inferred_kind (typed : CastTyping env U casts ctx e ty)
    (coherent : KnownTypes.Casts known casts)
    (result : {ty // env.HasType U ctx e ty})
    (success : inferWith env conv U ctx e exposure known = some result) : result.val = ty := by
  induction typed with
  | bvar found =>
    apply cache_or_kind (.bvar found) coherent ?_ result success
    intro missing result success
    obtain ⟨value,accepted,same⟩ := lookup_complete found
    simp only [inferWith,missing,accepted,bind,Option.bind] at success
    cases success
    exact same
  | sort wf =>
    apply cache_or_kind (.sort wf) coherent ?_ result success
    intro missing result success
    simp only [inferWith,missing,dif_pos wf] at success
    cases success; rfl
  | constant registered levels arity =>
    apply cache_or_kind (.constant registered levels arity) coherent ?_ result success
    intro missing result success
    simp only [inferWith,missing] at success
    split at success
    · rename_i absent
      rw [registered] at absent
      contradiction
    · rename_i info found
      have same := Option.some.inj (found.symm.trans registered)
      subst info
      simp only [dif_pos levels,dif_pos arity] at success
      cases success; rfl
  | application first second ihf _ =>
    exact cache_or_kind (.application first second) coherent
      (fun missing => application_inferred_kind missing ihf) result success
  | convertedApplication first second cast ihf _ =>
    exact cache_or_kind (.convertedApplication first second cast) coherent
      (fun missing => application_inferred_kind missing ihf) result success
  | functionApplication first view cast second ihf _ =>
    exact cache_or_kind (.functionApplication first view cast second) coherent
      (fun missing => function_application_inferred_kind missing ihf view) result success
  | @lambda ctx domain u body ty domainTyped bodyTyped ihd ihb =>
    apply cache_or_kind (.lambda domainTyped bodyTyped) coherent ?_ result success
    intro missing result success
    cases first : inferWith env conv U ctx domain exposure known with
    | none => simp [inferWith,missing,first] at success
    | some d =>
      rcases d with ⟨dt,hd⟩
      have same := ihd _ first
      dsimp only at same
      subst dt
      cases second : inferWith env conv U (domain::ctx) body exposure known with
      | none => simp [inferWith,missing,first,second] at success
      | some b =>
        rcases b with ⟨bt,hb⟩
        have same := ihb _ second
        dsimp only at same
        subst bt
        simp only [inferWith,missing,first,second,bind,Option.bind] at success
        cases success; rfl
  | @forallType ctx domain u body v domainTyped bodyTyped ihd ihb =>
    apply cache_or_kind (.forallType domainTyped bodyTyped) coherent ?_ result success
    intro missing result success
    cases first : inferWith env conv U ctx domain exposure known with
    | none => simp [inferWith,missing,first] at success
    | some d =>
      rcases d with ⟨dt,hd⟩
      have same := ihd _ first
      dsimp only at same
      subst dt
      cases second : inferWith env conv U (domain::ctx) body exposure known with
      | none => simp [inferWith,missing,first,second] at success
      | some b =>
        rcases b with ⟨bt,hb⟩
        have same := ihb _ second
        dsimp only at same
        subst bt
        simp only [inferWith,missing,first,second,bind,Option.bind] at success
        cases success; rfl

/-- Checking an expression against its expected type is distinct from inferring
that exact type. In particular a BitVec expression can check at an abbreviation
without pretending that native inference returned the abbreviation. -/
inductive CheckedTyping (env : VEnv) (U : Nat) (casts : TypeCasts)
    (ctx : List VExpr) (e : VExpr) : VExpr → Prop where
  | exact : CastTyping env U casts ctx e expected → CheckedTyping env U casts ctx e expected
  | converted : CastTyping env U casts ctx e actual → casts ctx actual expected →
      CheckedTyping env U casts ctx e expected

instance : Coe (CastTyping env U casts ctx e ty) (CheckedTyping env U casts ctx e ty) :=
  ⟨CheckedTyping.exact⟩

theorem CheckedTyping.mono (typed : CheckedTyping env U casts ctx e ty)
    (embeds : ∀ scope a b, casts scope a b → other scope a b) :
    CheckedTyping env U other ctx e ty := by
  cases typed with
  | exact h => exact .exact (h.mono embeds)
  | converted h cast => exact .converted (h.mono embeds) (embeds _ _ _ cast)

theorem CastTyping.checkedApplication
    (fn : CastTyping env U casts ctx f (.forallE domain codomain))
    (arg : CheckedTyping env U casts ctx e domain) :
    CastTyping env U casts ctx (.app f e) (codomain.inst e) := by
  cases arg with
  | exact h => exact .application fn h
  | converted h cast => exact .convertedApplication fn h cast

/-- The actual checker succeeds from source typing and the separately proved
conversion coverage. Checker success is never a constructor of this judgment. -/
theorem CheckedTyping.check_complete (typed : CheckedTyping env U casts ctx e ty)
    (coherent : KnownTypes.Casts known casts) (coverage : conv.Covers U casts)
    (exposure : Exposure env) :
    ∃ result, checkWith env conv U ctx e ty exposure known = some result := by
  cases typed with
  | exact h => exact h.check_complete coherent coverage exposure
  | @converted actual expected inferred cast =>
    obtain ⟨⟨actualType,h⟩,parsed,same⟩ := inferred.infer_complete coherent coverage exposure
    dsimp only at same
    subst actualType
    by_cases same : actual = ty
    · simp only [checkWith,parsed,bind,Option.bind,dif_pos same,pure,Option.pure_def]
      exact ⟨⟨same ▸ h⟩, trivial⟩
    · obtain ⟨equation,accepted⟩ := coverage ctx actual ty cast
      simp only [checkWith,parsed,bind,Option.bind,dif_neg same,accepted,pure,Option.pure_def]
      exact ⟨⟨.defeq equation.property h⟩, trivial⟩

/-- Scope extension preserves both the inferred type and its permitted cast. -/
theorem CheckedTyping.weakN (typed : CheckedTyping env U casts ctx e ty)
    (closed : ClosedConstantTypes env) (stable : ClosedCasts casts)
    (extension : Ctx.LiftN n k ctx next) :
    CheckedTyping env U casts next (e.liftN n k) (ty.liftN n k) := by
  cases typed with
  | exact h => exact .exact (h.weakN closed stable extension)
  | converted h cast =>
    refine .converted (h.weakN closed stable extension) ?_
    simpa only [(stable _ _ _ cast).1.liftN_eq (Nat.zero_le k),
      (stable _ _ _ cast).2.1.liftN_eq (Nat.zero_le k)] using (stable _ _ _ cast).2.2 next

theorem CheckedTyping.lift (typed : CheckedTyping env U casts ctx e ty)
    (closed : ClosedConstantTypes env) (stable : ClosedCasts casts) (binder : VExpr) :
    CheckedTyping env U casts (binder::ctx) e.lift ty.lift :=
  typed.weakN closed stable .one

theorem CheckedTyping.closed_term (typed : CheckedTyping env U casts ctx e ty) :
    e.ClosedN ctx.length := by
  cases typed with
  | exact h => exact h.closed_term
  | converted h _ => exact h.closed_term

end IRComparison.LeanTypeInference
