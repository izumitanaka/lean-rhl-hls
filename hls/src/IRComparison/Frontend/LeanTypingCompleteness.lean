import IRComparison.Frontend.LeanTypeInference

namespace IRComparison.LeanTyped
open Lean4Lean

/-- A structural condition on native universe syntax, independent of the
translation function. Monomorphic source definitions instantiate all levels. -/
def ClosedLevel : Lean.Level → Prop
  | .zero => True
  | .succ u => ClosedLevel u
  | .max u v | .imax u v => ClosedLevel u ∧ ClosedLevel v
  | .param _ | .mvar _ => False

theorem level_complete (closed : ClosedLevel u) : ∃ v, level u = some v := by
  induction u with
  | zero => exact ⟨.zero,rfl⟩
  | succ u ih =>
    obtain ⟨v,hv⟩ := ih closed
    exact ⟨.succ v,by simp [level,hv]⟩
  | max u v ihu ihv =>
    obtain ⟨a,ha⟩ := ihu closed.1
    obtain ⟨b,hb⟩ := ihv closed.2
    exact ⟨.max a b,by simp [level,ha,hb]⟩
  | imax u v ihu ihv =>
    obtain ⟨a,ha⟩ := ihu closed.1
    obtain ⟨b,hb⟩ := ihv closed.2
    exact ⟨.imax a b,by simp [level,ha,hb]⟩
  | param | mvar => contradiction

theorem levels_complete {us : List Lean.Level} (closed : ∀ u ∈ us, ClosedLevel u) :
    ∃ vs, us.mapM level = some vs := by
  induction us with
  | nil => exact ⟨[],rfl⟩
  | cons u us ih =>
    obtain ⟨v,hv⟩ := level_complete (closed u (by simp))
    obtain ⟨vs,hvs⟩ := ih (fun u hu => closed u (by simp [hu]))
    exact ⟨v::vs,by simp [List.mapM_cons,hv,hvs]⟩

/-- Native syntax that has a view in the existing proof calculus. This is
not the HLS grammar: arbitrary applications and binders satisfy it. No parser,
typechecker, or successful compilation occurs in this definition. -/
def RepresentableSyntax : Lean.Expr → Prop
  | .bvar _ | .lit (.natVal _) => True
  | .sort u => ClosedLevel u
  | .const _ us => ∀ u ∈ us, ClosedLevel u
  | .app f a => RepresentableSyntax f ∧ RepresentableSyntax a
  | .lam _ ty b _ | .forallE _ ty b _ => RepresentableSyntax ty ∧ RepresentableSyntax b
  | .letE _ ty v b _ => RepresentableSyntax ty ∧ RepresentableSyntax v ∧ RepresentableSyntax b
  | .mdata _ b => RepresentableSyntax b
  | .fvar _ | .mvar _ | .proj _ _ _ | .lit (.strVal _) => False

theorem RepresentableSyntax.represents (shape : RepresentableSyntax source) :
    ∃ core, Represents source core := by
  induction source with
  | bvar n => exact ⟨.bvar n,.bvar⟩
  | sort u =>
    obtain ⟨v,hv⟩ := level_complete shape
    exact ⟨.sort v,.sort hv⟩
  | const name us =>
    obtain ⟨vs,hvs⟩ := levels_complete shape
    exact ⟨.const name vs,.constant hvs⟩
  | app f a ihf iha =>
    obtain ⟨fc,hf⟩ := ihf shape.1
    obtain ⟨ac,ha⟩ := iha shape.2
    exact ⟨.app fc ac,.app hf ha⟩
  | lam name ty body info iht ihb =>
    obtain ⟨tc,ht⟩ := iht shape.1
    obtain ⟨bc,hb⟩ := ihb shape.2
    exact ⟨.lam tc bc,.lam ht hb⟩
  | forallE name ty body info iht ihb =>
    obtain ⟨tc,ht⟩ := iht shape.1
    obtain ⟨bc,hb⟩ := ihb shape.2
    exact ⟨.forallE tc bc,.forallE ht hb⟩
  | letE name ty value body flag iht ihv ihb =>
    obtain ⟨tc,ht⟩ := iht shape.1
    obtain ⟨vc,hv⟩ := ihv shape.2.1
    obtain ⟨bc,hb⟩ := ihb shape.2.2
    exact ⟨.app (.lam tc bc) vc,.letE ht hv hb⟩
  | mdata data body ih =>
    obtain ⟨bc,hb⟩ := ih shape
    exact ⟨bc,.metadata hb⟩
  | lit value =>
    cases value with
    | natVal n => exact ⟨numeral n,.natural⟩
    | strVal => contradiction
  | fvar | mvar | proj => contradiction

/-- The source-to-proof-calculus translation is complete for its independent
representation judgment, including binders, metadata and compact numerals. -/
theorem Represents.translate_complete (rep : Represents source core) :
    ∃ result, translate source = some result ∧ result.val = core := by
  induction rep with
  | bvar => exact ⟨_,rfl,rfl⟩
  | sort level =>
    refine ⟨⟨_,.sort level⟩,?_,rfl⟩
    simp only [translate]
    split
    · rename_i v found
      have same := Option.some.inj (found.symm.trans level)
      subst v
      rfl
    · rename_i missing
      rw [level] at missing
      contradiction
  | constant levels =>
    refine ⟨⟨_,.constant levels⟩,?_,rfl⟩
    simp only [translate]
    split
    · rename_i vs found
      have same := Option.some.inj (found.symm.trans levels)
      subst vs
      rfl
    · rename_i missing
      rw [levels] at missing
      contradiction
  | app f a ihf iha =>
    obtain ⟨⟨f',hf⟩,first,ef⟩ := ihf
    obtain ⟨⟨a',ha⟩,second,ea⟩ := iha
    dsimp only at ef ea
    subst f'; subst a'
    simp only [translate,first,second,bind,Option.bind]
    exact ⟨_,rfl,rfl⟩
  | lam ty body iht ihb | forallE ty body iht ihb =>
    obtain ⟨⟨t',ht⟩,first,et⟩ := iht
    obtain ⟨⟨b',hb⟩,second,eb⟩ := ihb
    dsimp only at et eb
    subst t'; subst b'
    simp only [translate,first,second,bind,Option.bind]
    exact ⟨_,rfl,rfl⟩
  | letE ty value body iht ihv ihb =>
    obtain ⟨⟨t',ht⟩,first,et⟩ := iht
    obtain ⟨⟨v',hv⟩,second,ev⟩ := ihv
    obtain ⟨⟨b',hb⟩,third,eb⟩ := ihb
    dsimp only at et ev eb
    subst t'; subst v'; subst b'
    simp only [translate,first,second,third,bind,Option.bind]
    exact ⟨_,rfl,rfl⟩
  | metadata body ih =>
    obtain ⟨⟨b',hb⟩,success,eq⟩ := ih
    dsimp only at eq
    subst b'
    simp only [translate,success,bind,Option.bind]
    exact ⟨_,rfl,rfl⟩
  | natural => exact ⟨_,rfl,rfl⟩

theorem RepresentableSyntax.translate_complete (shape : RepresentableSyntax source) :
    ∃ result, translate source = some result := by
  obtain ⟨core,represented⟩ := shape.represents
  obtain ⟨result,found,_⟩ := represented.translate_complete
  exact ⟨result,found⟩

theorem RepresentableSyntax.rename (shape : RepresentableSyntax source) (rho : Nat → Nat) :
    RepresentableSyntax (LeanBindings.rename rho source) := by
  induction source generalizing rho <;>
    simp_all [LeanBindings.rename,RepresentableSyntax]

private theorem representable_underSubst (substitution : Nat → Lean.Expr)
    (represented : ∀ n, RepresentableSyntax (substitution n)) :
    ∀ n, RepresentableSyntax (LeanBindings.underSubst substitution n) := by
  intro n
  cases n with
  | zero => trivial
  | succ n => exact (represented n).rename Nat.succ

theorem RepresentableSyntax.substitute (shape : RepresentableSyntax source)
    (substitution : Nat → Lean.Expr) (represented : ∀ n, RepresentableSyntax (substitution n)) :
    RepresentableSyntax (LeanBindings.substitute substitution source) := by
  induction source generalizing substitution <;>
    simp_all [LeanBindings.substitute,RepresentableSyntax,representable_underSubst]

end IRComparison.LeanTyped

namespace IRComparison.LeanTypeInference
open Lean4Lean

/-- The syntax-directed fragment of the existing Lean typing rules. This
judgment is independent of inference execution. It is proof infrastructure for
library fact applications, not a restriction on the HLS source language. -/
inductive DirectTyping (env : VEnv) (U : Nat) : List VExpr → VExpr → VExpr → Prop where
  | bvar : Lookup ctx n ty → DirectTyping env U ctx (.bvar n) ty
  | sort : u.WF U → DirectTyping env U ctx (.sort u) (.sort (.succ u))
  | constant : env.constants name = some info →
      (∀ u ∈ levels, u.WF U) → levels.length = info.uvars →
      DirectTyping env U ctx (.const name levels) (info.type.instL levels)
  | application : DirectTyping env U ctx f (.forallE domain codomain) →
      DirectTyping env U ctx arg domain → DirectTyping env U ctx (.app f arg) (codomain.inst arg)
  | lambda : DirectTyping env U ctx domain (.sort u) →
      DirectTyping env U (domain :: ctx) body ty →
      DirectTyping env U ctx (.lam domain body) (.forallE domain ty)
  | forallType : DirectTyping env U ctx domain (.sort u) →
      DirectTyping env U (domain :: ctx) body (.sort v) →
      DirectTyping env U ctx (.forallE domain body) (.sort (.imax u v))

theorem DirectTyping.sound (typed : DirectTyping env U ctx e ty) : env.HasType U ctx e ty := by
  induction typed with
  | bvar h => exact .bvar h
  | sort h => exact .sort h
  | constant h levels count => exact .const h levels count
  | application _ _ f a => exact .app f a
  | lambda _ _ d b => exact .lam d b
  | forallType _ _ d b => exact .forallE d b

/-- Only closure of declaration types is needed for direct weakening. This
does not assume an ordering/proof of the entire imported Lean environment. -/
def ClosedConstantTypes (env : VEnv) : Prop :=
  ∀ name info, env.constants name = some info → info.type.ClosedN 0

theorem DirectTyping.weakN (typed : DirectTyping env U ctx e ty)
    (closed : ClosedConstantTypes env) (extension : Ctx.LiftN n k ctx next) :
    DirectTyping env U next (e.liftN n k) (ty.liftN n k) := by
  induction typed generalizing k next with
  | bvar found => exact .bvar (found.weakN extension)
  | sort wf => exact .sort wf
  | constant found levels arity =>
    rw [(closed _ _ found).instL.liftN_eq (Nat.zero_le _)]
    exact .constant found levels arity
  | application _ _ ihf iha =>
    exact VExpr.liftN_inst_hi .. ▸ .application (ihf extension) (iha extension)
  | lambda _ _ ihd ihb => exact .lambda (ihd extension) (ihb extension.succ)
  | forallType _ _ ihd ihb => exact .forallType (ihd extension) (ihb extension.succ)

theorem DirectTyping.lift (typed : DirectTyping env U ctx e ty)
    (closed : ClosedConstantTypes env) (binder : VExpr) :
    DirectTyping env U (binder::ctx) e.lift ty.lift :=
  typed.weakN closed .one

/-- Substituting an already typed value preserves direct typing, including
under nested binders. No fixed bound on binding depth is involved. -/
theorem DirectTyping.instN (typed : DirectTyping env U before e ty)
    (closed : ClosedConstantTypes env) (argument : DirectTyping env U base value domain)
    (substitution : Ctx.InstN base value domain k before after) :
    DirectTyping env U after (e.inst value k) (ty.inst value k) := by
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
      | succ found => exact (ih found).lift closed _
  | sort wf => exact .sort wf
  | constant found levels arity =>
    rw [(closed _ _ found).instL.instN_eq (Nat.zero_le _)]
    exact .constant found levels arity
  | application _ _ ihf iha =>
    exact VExpr.inst_inst_hi .. ▸ .application (ihf substitution) (iha substitution)
  | lambda _ _ ihd ihb => exact .lambda (ihd substitution) (ihb substitution.succ)
  | forallType _ _ ihd ihb => exact .forallType (ihd substitution) (ihb substitution.succ)

theorem DirectTyping.instantiate (typed : DirectTyping env U (domain::ctx) body ty)
    (closed : ClosedConstantTypes env) (argument : DirectTyping env U ctx value domain) :
    DirectTyping env U ctx (body.inst value) (ty.inst value) :=
  typed.instN closed argument .zero

theorem DirectTyping.closed_term (typed : DirectTyping env U ctx e ty) :
    e.ClosedN ctx.length := by
  induction typed with
  | bvar found => exact found.lt
  | sort | constant => trivial
  | application _ _ ihf iha => exact ⟨ihf,iha⟩
  | lambda _ _ ihd ihb | forallType _ _ ihd ihb => exact ⟨ihd,ihb⟩

/-- A closed, directly typed declaration can be used under any input scope. -/
theorem DirectTyping.in_context (typed : DirectTyping env U [] e ty)
    (closed : ClosedConstantTypes env) (typeClosed : ty.ClosedN 0) (ctx : List VExpr) :
    DirectTyping env U ctx e ty := by
  induction ctx with
  | nil => exact typed
  | cons binder rest ih =>
    simpa only [typed.closed_term.lift_eq,typeClosed.lift_eq] using ih.lift closed binder

theorem lookup_complete (found : Lookup ctx n ty) :
    ∃ result, lookup ctx n = some result ∧ result.val = ty := by
  induction found with
  | zero => exact ⟨_,rfl,rfl⟩
  | succ h ih =>
    obtain ⟨result,success,same⟩ := ih
    simp only [lookup,success,bind,Option.bind]
    exact ⟨_,rfl,congrArg VExpr.lift same⟩

/-- Formal type inference succeeds for syntax-directed derivations, under
ANY optional conversion/exposure implementation. No checker-success premise. -/
theorem DirectTyping.infer_complete (typed : DirectTyping env U ctx e ty)
    (conv : Conversion env) (exposure : Exposure env) :
    ∃ result, inferWith env conv U ctx e exposure = some result ∧ result.val = ty := by
  induction typed with
  | bvar found =>
    obtain ⟨result,success,same⟩ := lookup_complete found
    simp only [inferWith,noKnownTypes,success,bind,Option.bind]
    exact ⟨_,rfl,same⟩
  | sort wf =>
    simp only [inferWith,noKnownTypes,dif_pos wf]
    exact ⟨_,rfl,rfl⟩
  | constant registered levels count =>
    simp only [inferWith,noKnownTypes]
    split
    · rename_i missing
      rw [registered] at missing
      contradiction
    · rename_i info found
      have same := Option.some.inj (found.symm.trans registered)
      subst info
      simp only [dif_pos levels,dif_pos count]
      exact ⟨_,rfl,rfl⟩
  | application first second ihf iha =>
    obtain ⟨⟨ft,hf⟩,first,eqf⟩ := ihf
    obtain ⟨⟨argTy,ha⟩,second,eqa⟩ := iha
    dsimp only at eqf eqa
    subst ft
    subst argTy
    simp only [inferWith,noKnownTypes,first,second,bind,Option.bind,dif_pos rfl]
    exact ⟨_,rfl,rfl⟩
  | lambda domain body ihd ihb =>
    obtain ⟨⟨dt,hd⟩,first,eqd⟩ := ihd
    obtain ⟨⟨bt,hb⟩,second,eqb⟩ := ihb
    dsimp only at eqd eqb
    subst dt
    subst bt
    simp only [inferWith,noKnownTypes,first,second,bind,Option.bind]
    exact ⟨_,rfl,rfl⟩
  | forallType domain body ihd ihb =>
    obtain ⟨⟨dt,hd⟩,first,eqd⟩ := ihd
    obtain ⟨⟨bt,hb⟩,second,eqb⟩ := ihb
    dsimp only at eqd eqb
    subst dt
    subst bt
    simp only [inferWith,noKnownTypes,first,second,bind,Option.bind]
    exact ⟨_,rfl,rfl⟩

theorem DirectTyping.check_complete (typed : DirectTyping env U ctx e ty)
    (conv : Conversion env) (exposure : Exposure env) :
    ∃ result, checkWith env conv U ctx e ty exposure = some result := by
  obtain ⟨⟨actual,h⟩,success,same⟩ := typed.infer_complete conv exposure
  dsimp only at same
  subst actual
  simp only [checkWith,success,bind,Option.bind,dif_pos rfl]
  exact ⟨_,rfl⟩

/-- Direct derivations assign a unique syntactic type. General Lean typing
allows conversion; this lemma deliberately concerns the syntax-directed
fragment used to compose certificates. -/
theorem DirectTyping.unique (first : DirectTyping env U ctx e a)
    (second : DirectTyping env U ctx e b) : a = b := by
  obtain ⟨r,hr,ea⟩ := first.infer_complete (noConversion env) (noExposure env)
  obtain ⟨s,hs,eb⟩ := second.infer_complete (noConversion env) (noExposure env)
  have eqn := Option.some.inj (hr.symm.trans hs)
  exact ea.symm.trans ((congrArg Subtype.val eqn).trans eb)

/-- Cached child derivations have their syntax-directed type. This is a
typing invariant of constructed artifacts, not an assumption that inference
or compilation succeeds. -/
def KnownTypes.Direct (known : KnownTypes env U) : Prop :=
  ∀ ctx e result, known ctx e = some result → DirectTyping env U ctx e result.val

theorem KnownTypes.Direct.orElse
    (first : KnownTypes.Direct a) (second : KnownTypes.Direct b) :
    KnownTypes.Direct (a.orElse b) := by
  intro ctx e result found
  cases ha : a ctx e with
  | none => exact second ctx e result (by simpa [KnownTypes.orElse,ha] using found)
  | some hit =>
    have eqn : hit = result := by simpa [KnownTypes.orElse,ha] using found
    subst result
    exact first ctx e hit ha

private theorem direct_cache_or_miss (typed : DirectTyping env U ctx e ty)
    (coherent : KnownTypes.Direct known)
    (conv : Conversion env) (exposure : Exposure env)
    (miss : known ctx e = none → ∃ result,
      inferWith env conv U ctx e exposure known = some result ∧ result.val = ty) :
    ∃ result, inferWith env conv U ctx e exposure known = some result ∧ result.val = ty := by
  cases cached : known ctx e with
  | none => exact miss cached
  | some result =>
    exact ⟨result, by rw [inferWith.eq_def,cached],
      (coherent ctx e result cached).unique typed⟩

/-- Child-proof reuse preserves completeness. A successful child is not
rechecked recursively, and the invariant rules out a cache silently changing
the expected syntactic type of an enclosing fact application. -/
theorem DirectTyping.infer_known_complete (typed : DirectTyping env U ctx e ty)
    (coherent : KnownTypes.Direct known)
    (conv : Conversion env) (exposure : Exposure env) :
    ∃ result, inferWith env conv U ctx e exposure known = some result ∧ result.val = ty := by
  induction typed with
  | bvar found =>
    apply direct_cache_or_miss (.bvar found) coherent conv exposure
    intro missing
    obtain ⟨result,success,same⟩ := lookup_complete found
    simp only [inferWith,missing,success,bind,Option.bind]
    exact ⟨_,rfl,same⟩
  | sort wf =>
    apply direct_cache_or_miss (.sort wf) coherent conv exposure
    intro missing
    simp only [inferWith,missing,dif_pos wf]
    exact ⟨_,rfl,rfl⟩
  | constant registered levels count =>
    apply direct_cache_or_miss (.constant registered levels count) coherent conv exposure
    intro missing
    simp only [inferWith,missing]
    split
    · rename_i absent
      rw [registered] at absent
      contradiction
    · rename_i info found
      have eqn := Option.some.inj (found.symm.trans registered)
      subst info
      simp only [dif_pos levels,dif_pos count]
      exact ⟨_,rfl,rfl⟩
  | application first second ihf iha =>
    apply direct_cache_or_miss (.application first second) coherent conv exposure
    intro missing
    obtain ⟨⟨ft,hf⟩,hfirst,eqf⟩ := ihf
    obtain ⟨⟨argTy,ha⟩,hsecond,eqa⟩ := iha
    dsimp only at eqf eqa
    subst ft; subst argTy
    simp only [inferWith,missing,hfirst,hsecond,bind,Option.bind,dif_pos rfl]
    exact ⟨_,rfl,rfl⟩
  | lambda domain body ihd ihb =>
    apply direct_cache_or_miss (.lambda domain body) coherent conv exposure
    intro missing
    obtain ⟨⟨dt,hd⟩,first,eqd⟩ := ihd
    obtain ⟨⟨bt,hb⟩,second,eqb⟩ := ihb
    dsimp only at eqd eqb
    subst dt; subst bt
    simp only [inferWith,missing,first,second,bind,Option.bind]
    exact ⟨_,rfl,rfl⟩
  | forallType domain body ihd ihb =>
    apply direct_cache_or_miss (.forallType domain body) coherent conv exposure
    intro missing
    obtain ⟨⟨dt,hd⟩,first,eqd⟩ := ihd
    obtain ⟨⟨bt,hb⟩,second,eqb⟩ := ihb
    dsimp only at eqd eqb
    subst dt; subst bt
    simp only [inferWith,missing,first,second,bind,Option.bind]
    exact ⟨_,rfl,rfl⟩

theorem DirectTyping.check_known_complete (typed : DirectTyping env U ctx e ty)
    (coherent : KnownTypes.Direct known)
    (conv : Conversion env) (exposure : Exposure env) :
    ∃ result, checkWith env conv U ctx e ty exposure known = some result := by
  obtain ⟨⟨actual,h⟩,success,same⟩ := typed.infer_known_complete coherent conv exposure
  dsimp only at same
  subst actual
  simp only [checkWith,success,bind,Option.bind,dif_pos rfl]
  exact ⟨_,rfl⟩

/-- The fixed standard-library signatures used by compact natural literals.
These are declaration conditions, not successful inference premises. -/
structure NatSignatures (env : VEnv) : Prop where
  zero : env.constants ``Nat.zero = some ⟨0,.const ``Nat []⟩
  successor : env.constants ``Nat.succ = some ⟨0,.forallE (.const ``Nat []) (.const ``Nat [])⟩
  multiply : env.constants ``Nat.mul = some ⟨0,.forallE (.const ``Nat [])
    (.forallE (.const ``Nat []) (.const ``Nat []))⟩

theorem NatSignatures.zero_typed (signatures : NatSignatures env) :
    DirectTyping env U ctx (.const ``Nat.zero []) (.const ``Nat []) :=
  .constant signatures.zero (by simp) rfl

theorem NatSignatures.successor_typed (signatures : NatSignatures env)
    (typed : DirectTyping env U ctx a (.const ``Nat [])) :
    DirectTyping env U ctx (.app (.const ``Nat.succ []) a) (.const ``Nat []) := by
  exact .application (.constant signatures.successor (by simp) rfl) typed

theorem NatSignatures.multiply_typed (signatures : NatSignatures env)
    (left : DirectTyping env U ctx a (.const ``Nat []))
    (right : DirectTyping env U ctx b (.const ``Nat [])) :
    DirectTyping env U ctx (.app (.app (.const ``Nat.mul []) a) b) (.const ``Nat []) := by
  exact .application (.application (.constant signatures.multiply (by simp) rfl) left) right

/-- Literals remain inferable above the compact representation's threshold;
the proof is uniform in their magnitude and in the optional converters. -/
theorem NatSignatures.numeral_typed (signatures : NatSignatures env) (n : Nat) :
    DirectTyping env U ctx (LeanTyped.numeral n) (.const ``Nat []) := by
  apply LeanTyped.numeral_induction (fun e => DirectTyping env U ctx e (.const ``Nat []))
  · exact signatures.zero_typed
  · intro a ha; exact signatures.successor_typed ha
  · intro a ha
    have two : DirectTyping env U ctx (LeanTyped.numeral 2) (.const ``Nat []) := by
      rw [LeanTyped.numeral_two]
      exact signatures.successor_typed (signatures.successor_typed signatures.zero_typed)
    exact signatures.multiply_typed two ha

end IRComparison.LeanTypeInference
