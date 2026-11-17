import IRComparison.Frontend.WordOrdinarySourceRetag

/-! Internal typed substitution for the original source derivation. This is
binding transport, not another accepted-source judgment or normalization pass.
It derives typing after captured substitutions from one original typing proof. -/
namespace IRComparison.WordFrontend.OrdinarySource
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic
set_option maxHeartbeats 2400000

private theorem rename_lift (v : VExpr) : coreRename Nat.succ v = v.lift := by
  have same : (fun i => liftVar 1 i 0) = Nat.succ := by funext i; simp [liftVar,Nat.add_comm]
  simpa only [same] using coreRename_lift v 1 0

private theorem rename_comp (e : VExpr) (ρ τ : Nat → Nat) :
    coreRename ρ (coreRename τ e) = coreRename (ρ ∘ τ) e := by
  induction e generalizing ρ τ <;> simp_all [coreRename,LeanBindings.underRename_comp]

private theorem under_rename (σ : Nat → VExpr) (ρ : Nat → Nat) :
    coreUnder (σ ∘ ρ) = coreUnder σ ∘ LeanBindings.underRename ρ := by
  funext n; cases n <;> rfl

private theorem substitute_rename (e : VExpr) (σ : Nat → VExpr) (ρ : Nat → Nat) :
    coreSubstitute σ (coreRename ρ e) = coreSubstitute (σ ∘ ρ) e := by
  induction e generalizing σ ρ <;> simp_all [coreRename,coreSubstitute,under_rename]

private theorem under_mapRename (σ : Nat → VExpr) (ρ : Nat → Nat) :
    coreUnder (fun n => coreRename ρ (σ n)) =
      fun n => coreRename (LeanBindings.underRename ρ) (coreUnder σ n) := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    simp only [coreUnder,← rename_lift,rename_comp]
    rfl

private theorem rename_substitute (e : VExpr) (σ : Nat → VExpr) (ρ : Nat → Nat) :
    coreRename ρ (coreSubstitute σ e) = coreSubstitute (fun n => coreRename ρ (σ n)) e := by
  induction e generalizing σ ρ <;> simp_all [coreRename,coreSubstitute,under_mapRename]

private theorem substitute_under_lift (e : VExpr) (σ : Nat → VExpr) :
    coreSubstitute (coreUnder σ) e.lift = (coreSubstitute σ e).lift := by
  simp only [← rename_lift,substitute_rename,rename_substitute]
  congr 1
  funext n
  exact (rename_lift (σ n)).symm

private theorem under_comp (σ τ : Nat → VExpr) :
    coreUnder (fun n => coreSubstitute σ (τ n)) =
      fun n => coreSubstitute (coreUnder σ) (coreUnder τ n) := by
  funext n
  cases n with
  | zero => rfl
  | succ n => exact (substitute_under_lift _ _).symm

private theorem substitute_comp (e : VExpr) (σ τ : Nat → VExpr) :
    coreSubstitute σ (coreSubstitute τ e) =
      coreSubstitute (fun n => coreSubstitute σ (τ n)) e := by
  induction e generalizing σ τ <;> simp_all [coreSubstitute,under_comp]

private theorem substitute_id (e : VExpr) : coreSubstitute VExpr.bvar e = e := by
  have same : coreUnder VExpr.bvar = VExpr.bvar := by funext n; cases n <;> simp [coreUnder,VExpr.lift,VExpr.liftN,liftVar,Nat.add_comm]
  induction e <;> simp_all [coreSubstitute]

private theorem substitute_inst (body value : VExpr) (σ : Nat → VExpr) :
    coreSubstitute σ (body.inst value) =
      (coreSubstitute (coreUnder σ) body).inst (coreSubstitute σ value) := by
  simp only [← coreSubstitute_inst,substitute_comp]
  congr 1
  funext n
  cases n with
  | zero => simp [coreUnder,VExpr.instVar,coreSubstitute]
  | succ n =>
    simp only [coreUnder,← rename_lift,substitute_rename,Function.comp_def]
    exact (substitute_id _).symm

private theorem substitute_eq_of_closed (e : VExpr) (scope : e.ClosedN depth)
    (σ : Nat → VExpr) (same : ∀ n, n < depth → σ n = .bvar n) :
    coreSubstitute σ e = e := by
  induction e generalizing depth σ with
  | bvar n => exact same n scope
  | sort | const => rfl
  | app f a ihf iha => simp only [coreSubstitute,ihf scope.1 σ same,iha scope.2 σ same]
  | lam ty b iht ihb | forallE ty b iht ihb =>
    have next : ∀ n, n < depth+1 → coreUnder σ n = .bvar n := by
      intro n bound
      cases n with
      | zero => rfl
      | succ n => simp [coreUnder,same n (by omega),VExpr.lift,VExpr.liftN,liftVar,Nat.add_comm]
    simp only [coreSubstitute,iht scope.1 σ same,ihb scope.2 _ next]

theorem substitute_closed (scope : e.ClosedN 0) (σ : Nat → VExpr) :
    coreSubstitute σ e = e := substitute_eq_of_closed e scope σ (by omega)

/-- Internal environment property: every source variable is replaced by a
value of its transported type. The public source judgment does not require
this property; identity and binder-extension constructors establish it. -/
def TypedMapping (env : VEnv) (before after : List VExpr) (σ : Nat → VExpr) : Prop :=
  ∀ n ty, Lookup before n ty → CastTyping env 0 (SourceCasts env) after (σ n) (coreSubstitute σ ty)

theorem TypedMapping.identity : TypedMapping env ctx ctx VExpr.bvar := by
  intro n ty found
  rw [substitute_id]
  exact .bvar found

theorem TypedMapping.under (mapping : TypedMapping env before after σ)
    (closed : ClosedConstantTypes env) (domain : VExpr) :
    TypedMapping env (domain::before) (coreSubstitute σ domain::after) (coreUnder σ) := by
  intro n ty found
  cases found with
  | zero => simpa only [coreUnder,substitute_under_lift] using
      (CastTyping.bvar (Lookup.zero (Γ := after) (ty := coreSubstitute σ domain)))
  | succ found =>
    simpa only [coreUnder,substitute_under_lift] using
      (mapping _ _ found).lift closed SourceCasts.closed (coreSubstitute σ domain)

theorem TypedMapping.underClosed (mapping : TypedMapping env before after σ)
    (closed : ClosedConstantTypes env) (domain : VExpr) (domainClosed : domain.ClosedN 0) :
    TypedMapping env (domain::before) (domain::after) (coreUnder σ) := by
  simpa only [substitute_closed domainClosed] using mapping.under closed domain

/-- Reusing a previously typed value needs no new target binder. This is the
shared environment step for function aliases and already-retained arguments. -/
theorem TypedMapping.consClosed (mapping : TypedMapping env before after τ)
    (argument : CastTyping env 0 (SourceCasts env) after value domain)
    (domainClosed : domain.ClosedN 0) :
    TypedMapping env (domain::before) after (fun n => match n with | 0 => value | k+1 => τ k) := by
  intro n ty found
  cases found with
  | zero => simpa only [domainClosed.lift_eq,substitute_closed domainClosed] using argument
  | succ found =>
    simpa only [← rename_lift,substitute_rename,Function.comp_def] using mapping _ _ found

theorem Signature.Spelling.substitute (spelling : Signature.Spelling signature ty)
    (σ : Nat → Lean.Expr) : LeanBindings.substitute σ ty = ty := by
  induction spelling generalizing σ with
  | result result => cases result <;> rfl
  | arrow head tail binder info ih =>
    simp only [LeanBindings.substitute,ih]
    congr 1
    cases head with
    | scalar a => exact a.substitute_native σ
    | state | natural | unit => rfl

theorem mappingUnderRepresented (represented : ∀ n, Represents (σ n) (τ n)) :
    ∀ n, Represents (LeanBindings.underSubst σ n) (coreUnder τ n) := by
  intro n
  cases n with
  | zero => exact .bvar
  | succ n => exact (represented n).lift

/-- Transport an existing typing derivation through a captured environment.
Substitution and binders share this one proof for all original constructs. -/
theorem typingMapped (typed : CastTyping env 0 (SourceCasts env) before e ty)
    (closed : ClosedConstantTypes env) (mapping : TypedMapping env before after σ) :
    CastTyping env 0 (SourceCasts env) after (coreSubstitute σ e) (coreSubstitute σ ty) := by
  induction typed generalizing after σ with
  | bvar found => exact mapping _ _ found
  | sort wf => exact .sort wf
  | constant found levels arity =>
    rw [substitute_closed ((closed _ _ found).instL) σ]
    exact .constant found levels arity
  | application _ _ ihf iha =>
    rw [substitute_inst]
    exact .application (ihf mapping) (iha mapping)
  | convertedApplication _ _ cast ihf iha =>
    have stable := SourceCasts.closed _ _ _ cast
    rw [substitute_inst]
    apply CastTyping.convertedApplication (ihf mapping) (iha mapping)
    simpa only [substitute_closed stable.1,substitute_closed stable.2.1] using stable.2.2 after
  | functionApplication _ view cast _ ihf iha =>
    have stable := SourceCasts.closed _ _ _ cast
    have a := substitute_closed stable.1 σ
    have b := substitute_closed stable.2.1 σ
    simp only [coreSubstitute] at b
    rw [substitute_inst]
    apply CastTyping.functionApplication (ihf mapping) _ _ (iha mapping)
    · simpa only [a,b] using view
    · simpa only [a,b] using stable.2.2 after
  | lambda _ _ ihd ihb => exact .lambda (ihd mapping) (ihb (mapping.under closed _))
  | forallType _ _ ihd ihb => exact .forallType (ihd mapping) (ihb (mapping.under closed _))

theorem checkedTypingMapped (typed : CheckedTyping env 0 (SourceCasts env) before e ty)
    (closed : ClosedConstantTypes env) (mapping : TypedMapping env before after σ) :
    CheckedTyping env 0 (SourceCasts env) after (coreSubstitute σ e) (coreSubstitute σ ty) := by
  cases typed with
  | exact h => exact .exact (typingMapped h closed mapping)
  | converted h cast =>
    have stable := SourceCasts.closed _ _ _ cast
    exact .converted (typingMapped h closed mapping) (by
      simpa only [substitute_closed stable.1,substitute_closed stable.2.1] using stable.2.2 after)

/-- Opening formal parameters shifts captures but does not evaluate them. -/
def openMapping : Nat → (Nat → VExpr) → (Nat → VExpr)
  | 0, mapping => mapping
  | n+1, mapping => coreUnder (openMapping n mapping)

def openReferences : Nat → (Nat → Lean.Expr) → (Nat → Lean.Expr)
  | 0, mapping => mapping
  | n+1, mapping => LeanBindings.underSubst (openReferences n mapping)

private theorem openMapping_commute (count : Nat) (τ : Nat → VExpr) :
    openMapping count (coreUnder τ) = coreUnder (openMapping count τ) := by
  induction count with
  | zero => rfl
  | succ n ih => exact congrArg coreUnder ih

private theorem substitute_lambdas (domains : List VExpr) (body : VExpr)
    (closed : ∀ ty ∈ domains, ty.ClosedN 0) (τ : Nat → VExpr) :
    coreSubstitute τ (domains.foldr VExpr.lam body) =
      domains.foldr VExpr.lam (coreSubstitute (openMapping domains.length τ) body) := by
  induction domains generalizing τ with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.foldr_cons,coreSubstitute,substitute_closed (closed head (by simp)),
      ih (fun ty member => closed ty (List.mem_cons_of_mem _ member)),List.length_cons,
      openMapping,openMapping_commute]

/-- Lambda annotations and binding positions are retained by substitution.
Only the original lambda spine and body representation are supplied. -/
theorem lambdaSourceMapped_represents {body : Lean.Expr} {domains : List Parameter}
    (shape : StructuralBody.LambdaSource fn (domains.map Parameter.native) body)
    (bodyRep : Represents body bodyCore)
    (represented : ∀ n, Represents (σ n) (τ n)) :
    Represents (LeanBindings.substitute σ fn)
      ((domains.map Parameter.core).foldr VExpr.lam
        (coreSubstitute (openMapping domains.length τ) bodyCore)) := by
  have original : Represents fn ((domains.map Parameter.core).foldr VExpr.lam bodyCore) := by
    have params : List.Forall₂ Represents (domains.map Parameter.native) (domains.map Parameter.core) := by
      clear shape bodyRep
      induction domains with
      | nil => exact .nil
      | cons head tail ih => exact .cons head.represented ih
    exact FunctionSyntax.lambdaSource_represents shape params bodyRep
  have domainClosed : ∀ ty ∈ domains.map Parameter.core, ty.ClosedN 0 := by
    intro ty member
    obtain ⟨parameter,_,rfl⟩ := List.mem_map.mp member
    exact parameter.closed
  simpa only [substitute_lambdas _ _ domainClosed,List.length_map] using original.substitute σ τ represented

theorem TypedMapping.prepend (mapping : TypedMapping env before after τ)
    (closed : ClosedConstantTypes env) (front : List VExpr)
    (typesClosed : ∀ ty ∈ front, ty.ClosedN 0) :
    TypedMapping env (front ++ before) (front ++ after) (openMapping front.length τ) := by
  induction front with
  | nil => exact mapping
  | cons head tail ih =>
    exact (ih (fun ty member => typesClosed ty (List.mem_cons_of_mem _ member))).underClosed
      closed head (typesClosed head (by simp))

theorem openMapping_represented (represented : ∀ n, Represents (σ n) (τ n)) (count : Nat) :
    ∀ n, Represents (openReferences count σ n) (openMapping count τ n) := by
  induction count with
  | zero => exact represented
  | succ n ih => exact mappingUnderRepresented ih

/-- A captured helper body supplies all intermediate Word/BV32 argument
prefix types from the original derivation, even in a different target scope. -/
theorem Body.typingPrefixesMapped
    (source : Body ds (declared.reverse.map Slot.value ++ Γ) result raw)
    (parameters : List.Forall₂ Parameter.Related declared actual)
    (library : ScopedSyntax.Library env) (closed : ClosedConstantTypes env)
    (mapping : TypedMapping env Γ.core ctx τ)
    (represented : ∀ n, Represents (σ n) (τ n)) :
    ∃ core, Represents (LeanBindings.substitute (openReferences declared.length σ) raw) core ∧
      ∀ n, CastTyping env 0 (SourceCasts env)
        (((actual.take n ++ declared.drop n).map Parameter.core).reverse ++ ctx)
        core (optionType result.core) := by
  obtain ⟨original,rep,types⟩ := source.typingPrefixes parameters library closed
  refine ⟨coreSubstitute (openMapping declared.length τ) original,
    rep.substitute _ _ (openMapping_represented represented _),?_⟩
  intro n
  let front := ((actual.take n ++ declared.drop n).map Parameter.core).reverse
  have frontClosed : ∀ ty ∈ front, ty.ClosedN 0 := by
    intro ty member
    obtain ⟨parameter,_,rfl⟩ := List.mem_map.mp (List.mem_reverse.mp member)
    exact parameter.closed
  have length : front.length = declared.length := by
    have same := List.Forall₂.length_eq parameters
    simp only [front,List.length_reverse,List.length_map,List.length_append,List.length_take,List.length_drop,same]
    omega
  have transported := typingMapped (types n) closed (mapping.prepend closed front frontClosed)
  have resultClosed : (optionType result.core).ClosedN 0 := ⟨by trivial,result.closed⟩
  simpa only [length,substitute_closed resultClosed] using transported

/-- No argument checker result is supplied: both inferred and declared types
are transported from the original call's lexical argument derivation. -/
theorem Arguments.evidenceMapped (source : Arguments Γ declared raws)
    (library : ScopedSyntax.Library env) (closed : ClosedConstantTypes env)
    (mapping : TypedMapping env Γ.core ctx τ)
    (represented : ∀ n, Represents (σ n) (τ n)) :
    ∃ actual cores, List.Forall₂ Parameter.Related declared actual ∧
      List.Forall₂ Represents (raws.map (LeanBindings.substitute σ)) cores ∧
      List.Forall₂ (fun parameter core => CastTyping env 0 (SourceCasts env) ctx core parameter.core) actual cores ∧
      List.Forall₂ (fun parameter core => CheckedTyping env 0 (SourceCasts env) ctx core parameter.core) declared cores := by
  obtain ⟨actual,cores,shapes,reps,types,checks⟩ := source.evidence library
  refine ⟨actual,cores.map (coreSubstitute τ),shapes,?_,?_,?_⟩
  · apply List.forall₂_map_left_iff.mpr
    apply List.forall₂_map_right_iff.mpr
    exact reps.imp (fun _ _ rep => rep.substitute σ τ represented)
  · apply List.forall₂_map_right_iff.mpr
    exact types.imp (fun parameter core typed => by
      simpa only [substitute_closed parameter.closed] using typingMapped typed closed mapping)
  · apply List.forall₂_map_right_iff.mpr
    exact checks.imp (fun parameter core typed => by
      simpa only [substitute_closed parameter.closed] using checkedTypingMapped typed closed mapping)

private theorem substitute_constantHead (head : LeanTypeReduction.constantHead e = some (name,levels))
    (τ : Nat → VExpr) : LeanTypeReduction.constantHead (coreSubstitute τ e) = some (name,levels) := by
  induction e with
  | app f a ih _ => exact ih head
  | const => exact head
  | bvar | sort | lam | forallE => cases head

/-- The only additional scalar environment fact is the shape of retained
scalar references. Helpers and State slots are not required to be scalars. -/
theorem scalarShapeMapped (shape : LexicalScalarSyntax.ValueShape env before e ty)
    (typed : CastTyping env 0 (SourceCasts env) before e ty)
    (closed : ClosedConstantTypes env) (mapping : TypedMapping env before after τ)
    (values : ∀ n, Lookup before n ty →
      LexicalScalarSyntax.ValueShape env after (τ n) (coreSubstitute τ ty)) :
    LexicalScalarSyntax.ValueShape env after (coreSubstitute τ e) (coreSubstitute τ ty) := by
  cases shape with
  | bound => cases typed with | bvar found => exact values _ found
  | constant head allowed => exact .constant (substitute_constantHead head τ) allowed
  | beta domain resultAnnotation bodyTyped =>
    have next := typingMapped bodyTyped closed (mapping.underClosed closed domain.core domain.closed)
    simp only [substitute_closed resultAnnotation.closed] at next
    simpa only [coreSubstitute,substitute_closed domain.closed,substitute_closed resultAnnotation.closed] using
      (LexicalScalarSyntax.ValueShape.beta (arg := coreSubstitute τ _) domain resultAnnotation next)

/-- Scalar types and value shapes after capture substitution both follow
from the original scalar rule, including lexical let and beta bodies. -/
theorem Scalar.evidenceMapped (source : Scalar Γ raw annotation)
    (library : ScopedSyntax.Library env) (closed : ClosedConstantTypes env)
    (mapping : TypedMapping env Γ.core ctx τ)
    (represented : ∀ n, Represents (σ n) (τ n))
    (values : ∀ n (a : WordBinder.Annotation), Lookup Γ.core n a.core →
      LexicalScalarSyntax.ValueShape env ctx (τ n) a.core) :
    ∃ core, Represents (LeanBindings.substitute σ raw) core ∧
      CastTyping env 0 (SourceCasts env) ctx core annotation.core ∧
      LexicalScalarSyntax.ValueShape env ctx core annotation.core := by
  obtain ⟨core,rep,typed,shape⟩ := source.typing library
  exact ⟨_,rep.substitute σ τ represented,
    by simpa only [substitute_closed annotation.closed] using typingMapped typed closed mapping,
    by
      have mapped := scalarShapeMapped shape typed closed mapping (fun n found => by
        simpa only [substitute_closed annotation.closed] using values n annotation found)
      simpa only [substitute_closed annotation.closed] using mapped⟩

/-- General captured-body typing follows from the original derivation;
there is no premise about the substituted or retained body. -/
theorem Body.typingMapped (source : Body ds Γ result raw)
    (library : ScopedSyntax.Library env) (closed : ClosedConstantTypes env)
    (mapping : TypedMapping env Γ.core ctx τ)
    (represented : ∀ n, Represents (σ n) (τ n)) :
    ∃ core, Represents (LeanBindings.substitute σ raw) core ∧
      CastTyping env 0 (SourceCasts env) ctx core (optionType result.core) := by
  obtain ⟨core,rep,typed⟩ := source.typing library closed
  refine ⟨_,rep.substitute σ τ represented,?_⟩
  have resultClosed : (optionType result.core).ClosedN 0 := ⟨by trivial,result.closed⟩
  simpa only [substitute_closed resultClosed] using OrdinarySource.typingMapped typed closed mapping

theorem Function.typingMapped (source : Function ds Γ raw signature)
    (library : ScopedSyntax.Library env) (closed : ClosedConstantTypes env)
    (mapping : TypedMapping env Γ.core ctx τ)
    (represented : ∀ n, Represents (σ n) (τ n)) :
    ∃ core, Represents (LeanBindings.substitute σ raw) core ∧
      CastTyping env 0 (SourceCasts env) ctx core signature.core := by
  obtain ⟨core,rep,typed⟩ := source.typing library closed
  exact ⟨_,rep.substitute σ τ represented,by
    simpa only [substitute_closed signature.closed] using OrdinarySource.typingMapped typed closed mapping⟩

/-- Bootstrap the ordinary State-only source scope into the actual frontend
context. The three legacy scalar inputs are outside the source scope. -/
theorem initialMapping : TypedMapping env (Context.core [.value .state]) context VExpr.bvar := by
  intro n ty found
  rw [substitute_id]
  cases found with
  | zero => exact .bvar .zero
  | succ found => cases found

/-- State, read-value, loop-counter and administrative Unit binders all
extend the same environment correspondence. -/
theorem openParameterMapping {Γ : Context} (mapping : TypedMapping env Γ.core ctx τ)
    (represented : ∀ n, Represents ((σ : StructuralBody.Substitution).reference n) (τ n))
    (closed : ClosedConstantTypes env) (parameter : Parameter) :
    TypedMapping env (Context.core (.value parameter::Γ)) (parameter.core::ctx) (coreUnder τ) ∧
      ∀ n, Represents ((StructuralBody.under σ).reference n) (coreUnder τ n) := by
  refine ⟨mapping.underClosed closed _ parameter.closed,?_⟩
  simpa only [StructuralBody.under_reference] using mappingUnderRepresented represented

/-- Construct the continuation's type environment at an original function
let. Its substituted typing is a conclusion, not a new source premise. -/
theorem Function.bindMapping (source : Function ds Γ raw signature)
    (library : ScopedSyntax.Library env) (closed : ClosedConstantTypes env)
    (mapping : TypedMapping env Γ.core ctx τ)
    (represented : ∀ n, Represents ((σ : StructuralBody.Substitution).reference n) (τ n)) :
    ∃ next, TypedMapping env (Context.core (.function signature::Γ)) ctx next ∧
      ∀ n, Represents ((StructuralBody.letSubstitution σ raw).reference n) (next n) := by
  obtain ⟨core,rep,typed⟩ := source.typingMapped library closed mapping represented
  refine ⟨(fun n => match n with | 0 => core | k+1 => τ k),
    mapping.consClosed typed signature.closed,?_⟩
  intro n
  cases n with
  | zero => simpa only [StructuralBody.letSubstitution,StructuralBody.Substitution.reference,
      StructuralBody.Substitution.apply_eq] using rep
  | succ n => exact represented n

/-- Internal substitutions preserve static register notation. A reference can
be a retained value, a Unit value or a captured lambda, but never a partially
applied register accessor. This is established by bindings, not a source
restriction on program computations. -/
structure RegisterMapping (σ : StructuralBody.Substitution) : Prop where
  static : ∀ n, LexicalScalarSyntax.StaticRegisters (σ.reference n)
  head : ∀ n, (σ.reference n).getAppFn.constName? ≠ some ``HybridWord.State.regs

private theorem rename_head (raw : Lean.Expr) (ρ : Nat → Nat) :
    (LeanBindings.rename ρ raw).getAppFn.constName? = raw.getAppFn.constName? := by
  induction raw with
  | app f a ih _ => exact ih
  | _ => rfl

theorem RegisterMapping.initial : RegisterMapping .identity :=
  ⟨fun _ => trivial,fun _ h => by cases h⟩

theorem RegisterMapping.under (mapping : RegisterMapping σ) : RegisterMapping (StructuralBody.under σ) := by
  constructor
  · intro n
    cases n with
    | zero => simp only [StructuralBody.under_reference,LeanBindings.underSubst]; trivial
    | succ n =>
      simpa only [StructuralBody.under_reference,LeanBindings.underSubst] using
        (mapping.static n).rename Nat.succ
  · intro n
    cases n with
    | zero => simp only [StructuralBody.under_reference,LeanBindings.underSubst]; intro h; cases h
    | succ n =>
      simpa only [StructuralBody.under_reference,LeanBindings.underSubst,rename_head] using mapping.head n

private theorem static_application
    (left : LexicalScalarSyntax.StaticRegisters f) (right : LexicalScalarSyntax.StaticRegisters a)
    (notRegister : f.getAppFn.constName? ≠ some ``HybridWord.State.regs) :
    LexicalScalarSyntax.StaticRegisters (.app f a) := by
  cases f with
  | app g st =>
    cases g with
    | const name levels =>
      by_cases nameEq : name = ``HybridWord.State.regs
      · subst name; exact False.elim (notRegister rfl)
      · simpa [LexicalScalarSyntax.StaticRegisters,nameEq] using And.intro left right
    | _ => exact ⟨left,right⟩
  | _ => exact ⟨left,right⟩

/-- Only static numeral notation and the source expression are inspected.
No parser/checker result or retained-body judgment is a premise. -/
theorem RegisterMapping.substitute (mapping : RegisterMapping σ)
    (source : LexicalScalarSyntax.StaticRegisters raw) :
    LexicalScalarSyntax.StaticRegisters (σ.apply raw) := by
  rw [StructuralBody.Substitution.apply_eq]
  induction raw generalizing σ with
  | bvar n => exact mapping.static n
  | fvar n => trivial
  | mvar n => trivial
  | sort u => trivial
  | const n u => trivial
  | lit l => trivial
  | forallE n t b i it ib => trivial
  | lam n t b i it ib =>
    simpa only [StructuralBody.Substitution.apply_eq,LeanBindings.substitute,StructuralBody.under_reference] using
      ib mapping.under source
  | letE n t v b f it iv ib =>
    exact ⟨iv mapping source.1,by
      simpa only [StructuralBody.Substitution.apply_eq,LeanBindings.substitute,StructuralBody.under_reference] using
        ib mapping.under source.2⟩
  | mdata d b ih => exact ih mapping source
  | proj n i b ih => exact ih mapping source
  | app f a iff ia =>
    cases f with
    | bvar n => exact static_application (mapping.static n) (ia mapping source.2) (mapping.head n)
    | app g st =>
      cases g with
      | bvar n =>
        exact static_application (iff mapping source.1) (ia mapping source.2) (mapping.head n)
      | const name levels =>
        by_cases hn : name = ``HybridWord.State.regs
        · subst name
          cases levels with
          | nil =>
            obtain ⟨⟨view⟩,child⟩ := source
            have number : LeanBindings.substitute σ.reference a = view.form.native view.value := by
              calc
                _ = LeanBindings.substitute σ.reference (view.form.native view.value) :=
                  congrArg (LeanBindings.substitute σ.reference) view.shape
                _ = _ := by cases view.form <;> rfl
            have childStatic := iff mapping (by simpa [LexicalScalarSyntax.StaticRegisters] using child)
            change Nonempty (NatNotation.View (LeanBindings.substitute σ.reference a)) ∧ _
            exact ⟨⟨⟨view.value,view.form,number⟩⟩,childStatic.2⟩
          | cons level levels => exact ⟨iff mapping source.1,ia mapping source.2⟩
        · have parts : LexicalScalarSyntax.StaticRegisters (.app (.const name levels) st) ∧
              LexicalScalarSyntax.StaticRegisters a := by simpa [LexicalScalarSyntax.StaticRegisters,hn] using source
          have left := iff mapping parts.1
          have right := ia mapping parts.2
          simpa [LeanBindings.substitute,LexicalScalarSyntax.StaticRegisters,hn] using And.intro left right
      | _ => exact ⟨iff mapping source.1,ia mapping source.2⟩
    | _ => exact ⟨iff mapping source.1,ia mapping source.2⟩

/-- A source helper is a lambda or a reference to an earlier helper. It
cannot turn an ordinary application into an untracked register access. -/
theorem Function.mappedHead (source : Function ds Γ raw signature) (mapping : RegisterMapping σ) :
    (σ.apply raw).getAppFn.constName? ≠ some ``HybridWord.State.regs := by
  cases source with
  | «variable» found =>
    simpa only [StructuralBody.Substitution.apply_eq,LeanBindings.substitute] using mapping.head _
  | lambda head tail result shape body =>
    have lambdaHead {value : Lean.Expr} {domains : List Lean.Expr} {body : Lean.Expr}
        (form : StructuralBody.LambdaSource value domains body) :
        (σ.apply value).getAppFn.constName? ≠ some ``HybridWord.State.regs := by
      cases form <;> simp only [StructuralBody.Substitution.apply_eq,LeanBindings.substitute,
        Lean.Expr.getAppFn,Lean.Expr.constName?] <;> intro h <;> cases h
    exact lambdaHead shape

theorem RegisterMapping.functionLet (mapping : RegisterMapping σ)
    (source : Function ds Γ value signature) (static : LexicalScalarSyntax.StaticRegisters value) :
    RegisterMapping (StructuralBody.letSubstitution σ value) := by
  constructor
  · intro n
    cases n with
    | zero => exact mapping.substitute static
    | succ n => exact mapping.static n
  · intro n
    cases n with
    | zero => exact source.mappedHead mapping
    | succ n => exact mapping.head n

/-- Reopening captures and binding an arbitrary number of retained actuals
preserves the same static-register invariant. -/
theorem RegisterMapping.closure (mapping : RegisterMapping σ)
    (static : ∀ raw ∈ args, LexicalScalarSyntax.StaticRegisters raw)
    (heads : ∀ raw ∈ args, raw.getAppFn.constName? ≠ some ``HybridWord.State.regs) :
    RegisterMapping (StructuralBody.closureSubstitution capture target σ args) := by
  constructor
  · intro n
    change LexicalScalarSyntax.StaticRegisters (StructuralBody.closureReference capture target σ args n)
    cases found : args.reverse[n]? with
    | some value =>
      simpa only [StructuralBody.closureReference,found] using
        static value (List.mem_reverse.mp (List.mem_of_getElem? found))
    | none =>
      simpa only [StructuralBody.closureReference,found] using (mapping.static (n-args.length)).rename (·+(target-capture))
  · intro n
    change (StructuralBody.closureReference capture target σ args n).getAppFn.constName? ≠ _
    cases found : args.reverse[n]? with
    | some value =>
      simpa only [StructuralBody.closureReference,found] using
        heads value (List.mem_reverse.mp (List.mem_of_getElem? found))
    | none =>
      simpa only [StructuralBody.closureReference,found,rename_head] using mapping.head (n-args.length)

theorem Body.typingEntry (source : Body ds [.value .state] result raw)
    (library : ScopedSyntax.Library env) (closed : ClosedConstantTypes env) :
    ∃ core, Represents raw core ∧
      CastTyping env 0 (SourceCasts env) context core (optionType result.core) := by
  simpa only [LeanBindings.substitute_id] using
    source.typingMapped library closed initialMapping (fun _ => Represents.bvar)

end IRComparison.WordFrontend.OrdinarySource
