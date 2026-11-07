import IRComparison.Frontend.LeanDefinition
import Lean4Lean.Theory.Typing.Lemmas

namespace IRComparison.LeanTyped
open Lean4Lean

/-- Proof-side translation of instantiated universe levels. Polymorphic source
    definitions are not part of the current entry point. -/
def level : Lean.Level → Option VLevel
  | .zero => some .zero
  | .succ u => return .succ (← level u)
  | .max u v => return .max (← level u) (← level v)
  | .imax u v => return .imax (← level u) (← level v)
  | _ => none

theorem level_wf (u : Lean.Level) (h : level u = some v) : v.WF 0 := by
  induction u generalizing v <;> simp_all [level]
  case zero => subst v; trivial
  case succ u ih =>
    obtain ⟨w, hw, rfl⟩ := h
    exact ih (v := w) hw
  case max u w ihu ihw =>
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    exact ⟨ihu ha, ihw hb⟩
  case imax u w ihu ihw =>
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    exact ⟨ihu ha, ihw hb⟩

def numeral : Nat → VExpr
  | 0 => .const ``Nat.zero []
  | n+1 => .app (.const ``Nat.succ []) (numeral n)

/-- A proof-side view in the existing Lean4Lean calculus. Binder names are
    irrelevant, but no condition on their spelling is imposed on the source.
    This relation is NOT the still-missing native-function quotation theorem. -/
inductive Represents : Lean.Expr → VExpr → Prop where
  | bvar : Represents (.bvar n) (.bvar n)
  | sort (h : level u = some v) : Represents (.sort u) (.sort v)
  | constant (h : us.mapM level = some vs) : Represents (.const name us) (.const name vs)
  | app : Represents f f' → Represents a a' → Represents (.app f a) (.app f' a')
  | lam : Represents ty ty' → Represents b b' →
      Represents (.lam name ty b info) (.lam ty' b')
  | forallE : Represents ty ty' → Represents b b' →
      Represents (.forallE name ty b info) (.forallE ty' b')
  | letE : Represents ty ty' → Represents value value' → Represents b b' →
      Represents (.letE name ty value b flag) (.app (.lam ty' b') value')
  | metadata : Represents b b' → Represents (.mdata data b) b'
  | natural : Represents (.lit (.natVal n)) (numeral n)

/-- Only used for proofs. The HLS compiler still consumes the original Expr. -/
def translate : (e : Lean.Expr) → Option {v : VExpr // Represents e v}
  | .bvar n => some ⟨.bvar n, .bvar⟩
  | .sort u => do
      match h : level u with
      | some v => return ⟨.sort v, .sort h⟩
      | none => none
  | .const name us => do
      match h : us.mapM level with
      | some vs => return ⟨.const name vs, .constant h⟩
      | none => none
  | .app f a => do
      let ⟨f', hf⟩ ← translate f
      let ⟨a', ha⟩ ← translate a
      return ⟨.app f' a', .app hf ha⟩
  | .lam _ ty b _ => do
      let ⟨ty', ht⟩ ← translate ty
      let ⟨b', hb⟩ ← translate b
      return ⟨.lam ty' b', .lam ht hb⟩
  | .forallE _ ty b _ => do
      let ⟨ty', ht⟩ ← translate ty
      let ⟨b', hb⟩ ← translate b
      return ⟨.forallE ty' b', .forallE ht hb⟩
  | .letE _ ty value b _ => do
      let ⟨ty', ht⟩ ← translate ty
      let ⟨value', hv⟩ ← translate value
      let ⟨b', hb⟩ ← translate b
      return ⟨.app (.lam ty' b') value', .letE ht hv hb⟩
  | .mdata _ b => do
      let ⟨b', hb⟩ ← translate b
      return ⟨b', .metadata hb⟩
  | .lit (.natVal n) => some ⟨numeral n, .natural⟩
  | _ => none

private theorem levels_wf (us : List Lean.Level) (h : us.mapM level = some vs) :
    ∀ v ∈ vs, v.WF 0 := by
  induction us generalizing vs with
  | nil =>
      simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
      subst vs
      simp
  | cons u us ih =>
      cases hu : level u with
      | none => simp [List.mapM_cons, hu] at h
      | some a =>
          cases hus : us.mapM level with
          | none => simp [List.mapM_cons, hu, hus] at h
          | some rest =>
              simp [List.mapM_cons, hu, hus] at h
              subst vs
              intro v hv
              rcases List.mem_cons.mp hv with rfl | hv
              · exact level_wf u hu
              · exact ih hus v hv

private theorem numeral_levelWF (n : Nat) : (numeral n).LevelWF 0 := by
  induction n <;> simp_all [numeral, VExpr.LevelWF]

theorem Represents.levelWF (h : Represents e v) : v.LevelWF 0 := by
  induction h <;> simp_all [VExpr.LevelWF, numeral_levelWF]
  case sort h => exact level_wf _ h
  case constant h => exact levels_wf _ h

theorem Represents.instL_empty (h : Represents e v) : v.instL [] = v := by
  simpa [VLevel.params] using h.levelWF.instL_id

def coreRename (ρ : Nat → Nat) : VExpr → VExpr
  | .bvar n => .bvar (ρ n)
  | .sort u => .sort u
  | .const c us => .const c us
  | .app f a => .app (coreRename ρ f) (coreRename ρ a)
  | .lam ty b => .lam (coreRename ρ ty) (coreRename (LeanBindings.underRename ρ) b)
  | .forallE ty b => .forallE (coreRename ρ ty) (coreRename (LeanBindings.underRename ρ) b)

@[simp] theorem coreRename_numeral (ρ) (n : Nat) : coreRename ρ (numeral n) = numeral n := by
  induction n <;> simp_all [numeral, coreRename]

theorem Represents.rename (h : Represents e v) (ρ : Nat → Nat) :
    Represents (LeanBindings.rename ρ e) (coreRename ρ v) := by
  induction h generalizing ρ with
  | bvar => exact .bvar
  | sort h => exact .sort h
  | constant h => exact .constant h
  | app hf ha ihf iha => exact .app (ihf ρ) (iha ρ)
  | lam ht hb iht ihb => exact .lam (iht ρ) (ihb (LeanBindings.underRename ρ))
  | forallE ht hb iht ihb => exact .forallE (iht ρ) (ihb (LeanBindings.underRename ρ))
  | letE ht hv hb iht ihv ihb => exact .letE (iht ρ) (ihv ρ) (ihb (LeanBindings.underRename ρ))
  | metadata hb ih => exact .metadata (ih ρ)
  | natural => simpa only [coreRename_numeral] using (Represents.natural (n := _))

private theorem underRename_lift (n k : Nat) :
    LeanBindings.underRename (fun i => liftVar n i k) = fun i => liftVar n i (k+1) := by
  funext i
  cases i <;> simp [LeanBindings.underRename]

theorem coreRename_lift (v : VExpr) (n k : Nat) :
    coreRename (fun i => liftVar n i k) v = v.liftN n k := by
  induction v generalizing k <;> simp_all [coreRename, VExpr.liftN, underRename_lift]

theorem Represents.lift (h : Represents e v) :
    Represents (LeanBindings.rename Nat.succ e) v.lift := by
  have eq : (fun i => liftVar 1 i 0) = Nat.succ := by funext i; simp [liftVar, Nat.add_comm]
  simpa only [← eq, coreRename_lift] using h.rename Nat.succ

def coreUnder (σ : Nat → VExpr) : Nat → VExpr
  | 0 => .bvar 0
  | n+1 => (σ n).lift

def coreSubstitute (σ : Nat → VExpr) : VExpr → VExpr
  | .bvar n => σ n
  | .sort u => .sort u
  | .const c us => .const c us
  | .app f a => .app (coreSubstitute σ f) (coreSubstitute σ a)
  | .lam ty b => .lam (coreSubstitute σ ty) (coreSubstitute (coreUnder σ) b)
  | .forallE ty b => .forallE (coreSubstitute σ ty) (coreSubstitute (coreUnder σ) b)

@[simp] theorem coreSubstitute_numeral (σ) (n : Nat) :
    coreSubstitute σ (numeral n) = numeral n := by
  induction n <;> simp_all [numeral, coreSubstitute]

private theorem under_represents (σ : Nat → Lean.Expr) (τ : Nat → VExpr)
    (h : ∀ n, Represents (σ n) (τ n)) :
    ∀ n, Represents (LeanBindings.underSubst σ n) (coreUnder τ n) := by
  intro n
  cases n with
  | zero => exact .bvar
  | succ n => exact (h n).lift

theorem Represents.substitute (h : Represents e v) (σ : Nat → Lean.Expr) (τ : Nat → VExpr)
    (maps : ∀ n, Represents (σ n) (τ n)) :
    Represents (LeanBindings.substitute σ e) (coreSubstitute τ v) := by
  induction h generalizing σ τ with
  | bvar => exact maps _
  | sort h => exact .sort h
  | constant h => exact .constant h
  | app hf ha ihf iha => exact .app (ihf σ τ maps) (iha σ τ maps)
  | lam ht hb iht ihb => exact .lam (iht σ τ maps) (ihb _ _ (under_represents σ τ maps))
  | forallE ht hb iht ihb => exact .forallE (iht σ τ maps) (ihb _ _ (under_represents σ τ maps))
  | letE ht hv hb iht ihv ihb => exact .letE (iht σ τ maps) (ihv σ τ maps) (ihb _ _ (under_represents σ τ maps))
  | metadata hb ih => exact .metadata (ih σ τ maps)
  | natural => simpa only [coreSubstitute_numeral] using (Represents.natural (n := _))

private theorem coreUnder_inst (a : VExpr) (k : Nat) :
    coreUnder (fun n => VExpr.instVar n a k) = fun n => VExpr.instVar n a (k+1) := by
  funext n
  cases n <;> simp [coreUnder]

theorem coreSubstitute_inst (v a : VExpr) (k : Nat) :
    coreSubstitute (fun n => VExpr.instVar n a k) v = v.inst a k := by
  induction v generalizing k <;> simp_all [coreSubstitute, VExpr.inst, coreUnder_inst]

theorem Represents.instantiate (body : Represents b b') (arg : Represents a a') :
    Represents (LeanBindings.instantiate a b) (b'.inst a') := by
  rw [← coreSubstitute_inst b' a' 0]
  apply body.substitute
  intro n
  cases n with
  | zero => simpa using arg
  | succ n => simpa using (Represents.bvar (n := n))

variable {env : VEnv} {U : Nat} {context : List VExpr}

/-- Connect actual Expr substitution to the existing typed beta rule. Typing
    premises are explicit and still have to be supplied by the source bridge. -/
theorem typed_beta (ht : Represents ty ty') (hb : Represents body body')
    (ha : Represents arg arg')
    (bodyTyped : env.HasType U (ty' :: context) body' resultType)
    (argTyped : env.HasType U context arg' ty') :
    Represents (.app (.lam name ty body info) arg) (.app (.lam ty' body') arg') ∧
    Represents (LeanBindings.instantiate arg body) (body'.inst arg') ∧
    env.IsDefEq U context (.app (.lam ty' body') arg')
      (body'.inst arg') (resultType.inst arg') :=
  ⟨.app (.lam ht hb) ha, hb.instantiate ha, .beta bodyTyped argTyped⟩

theorem typed_let (ht : Represents ty ty') (hb : Represents body body')
    (ha : Represents arg arg')
    (bodyTyped : env.HasType U (ty' :: context) body' resultType)
    (argTyped : env.HasType U context arg' ty') :
    Represents (.letE name ty arg body flag) (.app (.lam ty' body') arg') ∧
    Represents (LeanBindings.instantiate arg body) (body'.inst arg') ∧
    env.IsDefEq U context (.app (.lam ty' body') arg')
      (body'.inst arg') (resultType.inst arg') :=
  ⟨.letE ht ha hb, hb.instantiate ha, .beta bodyTyped argTyped⟩

/-- A view of the exact declaration already selected from the native environment.
    The HLS representation and the proof-side representation share that source. -/
structure DefinitionView (a : LeanDefinition.Artifact nativeEnv name) where
  body : {v : VExpr // Represents a.declaration.value v}
  type : {v : VExpr // Represents a.declaration.type v}

def viewDefinition (a : LeanDefinition.Artifact nativeEnv name) : Option (DefinitionView a) := do
  let body ← translate a.declaration.value
  let type ← translate a.declaration.type
  return ⟨body, type⟩

/-- The delta equation exported from a declaration. It does not contain an
    optimization result or assume that an optimization preserves semantics. -/
def DefinitionView.equation (view : DefinitionView a) : VDefEq where
  uvars := 0
  type := view.type.val
  lhs := .const a.declaration.name []
  rhs := view.body.val

/-- Specification environment extension. This operation does not itself prove
    that the entire imported environment is well formed. -/
def DefinitionView.extend (view : DefinitionView a) (base : VEnv) : VEnv :=
  base.addDefEq view.equation

theorem DefinitionView.unfold (view : DefinitionView a) (base : VEnv) (U : Nat)
    (context : List VExpr) :
    (view.extend base).IsDefEq U context (.const a.declaration.name [])
      view.body.val view.type.val := by
  have step : (view.extend base).IsDefEq U context (view.equation.lhs.instL [])
      (view.equation.rhs.instL []) (view.equation.type.instL []) :=
    .extra (df := view.equation) (Or.inl rfl) (by simp) rfl
  simpa only [DefinitionView.equation, VExpr.instL, List.map_nil,
    view.body.property.instL_empty, view.type.property.instL_empty] using step

def intType : VExpr := .const ``Int []

def scalarType : VExpr := .forallE intType (.forallE intType (.forallE intType intType))

private theorem Represents.intType (h : Represents (.const ``Int []) v) : v = intType := by
  cases h with
  | constant h => simp at h; subst h; rfl

private theorem scalarType_representation (ht : LeanDefinition.ScalarFunctionType type)
    (h : Represents type v) : v = scalarType := by
  cases ht
  cases h with
  | forallE ha hb =>
    cases hb with
    | forallE hc hd =>
      cases hd with
      | forallE he hf =>
        simp only [ha.intType, hc.intType, he.intType, hf.intType]
        rfl

theorem DefinitionView.type_shape (view : DefinitionView a) : view.type.val = scalarType :=
  scalarType_representation a.typed view.type.property

/-- Apply a named declaration's exported delta equation to three typed integer
    arguments. This only unfolds the source, and does not assume HLS correctness. -/
theorem DefinitionView.apply_three (view : DefinitionView a) (base : VEnv) (U : Nat)
    (context : List VExpr)
    (hi : (view.extend base).HasType U context i intType)
    (hx : (view.extend base).HasType U context x intType)
    (hy : (view.extend base).HasType U context y intType) :
    (view.extend base).IsDefEq U context
      (.app (.app (.app (.const a.declaration.name []) i) x) y)
      (.app (.app (.app view.body.val i) x) y) intType := by
  have step := view.unfold base U context
  rw [view.type_shape] at step
  exact .appDF (.appDF (.appDF step hi) hx) hy

/-- Any number of integer binders, not a rule specialized to a test function. -/
def intArrows : Nat → VExpr
  | 0 => intType
  | n+1 => .forallE intType (intArrows n)

def intLambdas : Nat → VExpr → VExpr
  | 0, b => b
  | n+1, b => .lam intType (intLambdas n b)

def applications (f : VExpr) : List VExpr → VExpr
  | [] => f
  | a::as => applications (.app f a) as

private theorem intArrows_inst (n : Nat) (a : VExpr) (k : Nat) :
    (intArrows n).inst a k = intArrows n := by
  induction n generalizing k <;> simp_all [intArrows, intType, VExpr.inst]

/-- Reading the exact standard type declaration, rather than adding a new
    axiom asserting that arbitrary source bodies are well typed. -/
theorem int_hasType (declared : env.constants ``Int = some ⟨0, .sort (.succ .zero)⟩)
    (context : List VExpr) : env.HasType U context intType (.sort (.succ .zero)) :=
  .constDF declared (by simp) (by simp) rfl .nil

/-- Lift an open-body equality through all its binders using only basic rules.
    No inversion, unique typing, or subject reduction theorem is imported. -/
theorem intLambdas_congr
    (declared : env.constants ``Int = some ⟨0, .sort (.succ .zero)⟩)
    (n : Nat) (context : List VExpr)
    (body : env.IsDefEq U (List.replicate n intType ++ context) left right intType) :
    env.IsDefEq U context (intLambdas n left) (intLambdas n right) (intArrows n) := by
  induction n generalizing context with
  | zero => exact body
  | succ n ih =>
      apply VEnv.IsDefEq.lamDF (int_hasType declared context)
      apply ih (intType :: context)
      simpa only [List.replicate_succ', List.append_assoc, List.singleton_append] using body

/-- Apply a proved function equality to a list of typed arguments. The proof
    handles every arity and obtains intermediate equalities by congruence. -/
theorem applications_congr
    (args : List VExpr)
    (fn : env.IsDefEq U context f g (intArrows args.length))
    (typed : ∀ a ∈ args, env.HasType U context a intType) :
    env.IsDefEq U context (applications f args) (applications g args) intType := by
  induction args generalizing f g with
  | nil => exact fn
  | cons a args ih =>
      have step := VEnv.IsDefEq.appDF fn (typed a (by simp))
      simp only [intArrows_inst] at step
      exact ih step (fun b hb => typed b (by simp [hb]))

theorem Represents.unique (first : Represents e v) (second : Represents e w) : v = w := by
  induction first generalizing w <;> cases second <;> try simp_all
  all_goals grind

/-- Read the open body from the same represented function. This is structural
    correspondence, not a fresh assumption about its value. -/
theorem represented_function_body (shape : LeanScalar.ThreeIntLambdas source body)
    (represented : Represents source core) :
    ∃ bodyCore, Represents body bodyCore ∧ core = intLambdas 3 bodyCore := by
  cases shape
  cases represented with
  | lam ht hb =>
    cases hb with
    | lam ht' hb' =>
      cases hb' with
      | lam ht'' hb'' =>
        refine ⟨_, hb'', ?_⟩
        simp only [ht.intType, ht'.intType, ht''.intType]
        rfl

/-- Source-name unfolding, open-body correspondence and application compose
    without the incomplete higher-order metatheory. The open-body equality
    remains an explicit compiler obligation, not an assumed finished bridge. -/
theorem DefinitionView.apply_body_equivalence (view : DefinitionView a) (base : VEnv)
    (declared : (view.extend base).constants ``Int = some ⟨0, .sort (.succ .zero)⟩)
    (sourceBody : Represents a.function.body sourceCore)
    (body : (view.extend base).IsDefEq U (List.replicate 3 intType ++ context)
      sourceCore targetCore intType)
    (args : List VExpr) (arity : args.length = 3)
    (typed : ∀ arg ∈ args, (view.extend base).HasType U context arg intType) :
    (view.extend base).IsDefEq U context
      (applications (.const a.declaration.name []) args)
      (applications (intLambdas 3 targetCore) args) intType := by
  obtain ⟨bodyCore, representedBody, same⟩ :=
    represented_function_body a.function.shape view.body.property
  have eqBody := representedBody.unique sourceBody
  subst bodyCore
  have unfolded := view.unfold base U context
  rw [view.type_shape, same] at unfolded
  have lifted := intLambdas_congr declared 3 context body
  apply applications_congr args
  · simpa only [arity] using unfolded.trans lifted
  · exact typed

/-- Substitute arguments in their application order, respecting all remaining
    binders. This works at every arity, including zero. -/
def instantiateArgs (body : VExpr) : List VExpr → VExpr
  | [] => body
  | a::as => instantiateArgs (body.inst a as.length) as

private theorem intLambdas_inst (n : Nat) (body a : VExpr) (k : Nat) :
    (intLambdas n body).inst a k = intLambdas n (body.inst a (k+n)) := by
  induction n generalizing k <;> simp_all [intLambdas, intType, VExpr.inst, Nat.add_comm, Nat.add_left_comm]

theorem int_context_inst (n : Nat) (a : VExpr) (context : List VExpr) :
    Ctx.InstN context a intType n (List.replicate (n+1) intType ++ context)
      (List.replicate n intType ++ context) := by
  induction n with
  | zero => exact .zero
  | succ n ih =>
      simpa only [List.replicate_succ, List.cons_append, intType, VExpr.inst] using
        (Ctx.InstN.succ (A := intType) ih)

/-- Multiple beta computations, proved with the audited substitution lemma.
    Ordered is an environment condition, not an assumption about optimizer
    output. Intermediate typing is derived, not supplied per computation. -/
theorem applications_beta
    (ordered : env.Ordered)
    (declared : env.constants ``Int = some ⟨0, .sort (.succ .zero)⟩)
    (args : List VExpr) (body : VExpr)
    (bodyTyped : env.HasType U (List.replicate args.length intType ++ context) body intType)
    (typed : ∀ a ∈ args, env.HasType U context a intType) :
    env.IsDefEq U context (applications (intLambdas args.length body) args)
      (instantiateArgs body args) intType := by
  induction args generalizing body with
  | nil => exact bodyTyped
  | cons a args ih =>
      have ha := typed a (by simp)
      have tailTyped := fun b hb => typed b (List.mem_cons_of_mem a hb)
      have bodyInContext : env.HasType U (List.replicate args.length intType ++ intType :: context)
          body intType := by
        simpa only [List.length_cons, List.replicate_succ', List.append_assoc,
          List.singleton_append] using bodyTyped
      have lambdaTyped := intLambdas_congr declared args.length (intType :: context) bodyInContext
      have beta := VEnv.IsDefEq.beta lambdaTyped ha
      simp only [intArrows_inst, intLambdas_inst, Nat.zero_add] at beta
      have first := applications_congr args beta tailTyped
      have nextTyped := VEnv.HasType.instN ordered (int_context_inst args.length a context) bodyTyped ha
      have rest := ih (body.inst a args.length) nextTyped tailTyped
      exact first.trans rest

/-- Expr-side substitution under k remaining binders. -/
def argumentAt (arg : Lean.Expr) : Nat → Nat → Lean.Expr
  | 0 => fun | 0 => arg | n+1 => .bvar n
  | k+1 => LeanBindings.underSubst (argumentAt arg k)

private theorem argumentAt_represents (h : Represents a a') (k : Nat) :
    ∀ n, Represents (argumentAt a k n) (VExpr.instVar n a' k) := by
  induction k with
  | zero =>
      intro n
      cases n with
      | zero => simpa [argumentAt] using h
      | succ n => simpa [argumentAt] using (Represents.bvar (n := n))
  | succ k ih =>
      have lifted := under_represents (argumentAt a k) (fun n => VExpr.instVar n a' k) ih
      simpa only [argumentAt, coreUnder_inst] using lifted

theorem Represents.instantiate_at (body : Represents b b') (arg : Represents a a') (k : Nat) :
    Represents (LeanBindings.substitute (argumentAt a k) b) (b'.inst a' k) := by
  rw [← coreSubstitute_inst]
  exact body.substitute _ _ (argumentAt_represents arg k)

def integer : Int → VExpr
  | .ofNat n => .app (.const ``Int.ofNat []) (numeral n)
  | .negSucc n => .app (.const ``Int.neg []) (.app (.const ``Int.ofNat []) (numeral (n+1)))

theorem integer_represents (n : Int) : Represents (LeanBindings.quoteInt n) (integer n) := by
  cases n with
  | ofNat n => exact .app (.constant rfl) .natural
  | negSucc n => exact .app (.constant rfl) (.app (.constant rfl) .natural)

theorem appliedBody_represents (body : Represents b core) (i x y : Int) :
    Represents (LeanBindings.appliedBody b i x y)
      (instantiateArgs core [integer i, integer x, integer y]) :=
  ((body.instantiate_at (integer_represents i) 2).instantiate_at
    (integer_represents x) 1).instantiate_at (integer_represents y) 0

/-- Named source to its fully instantiated body, under the standard source
    typing/environment premises. No per-input optimization equality is assumed. -/
theorem DefinitionView.apply_and_instantiate (view : DefinitionView a) (base : VEnv)
    (ordered : (view.extend base).Ordered)
    (declared : (view.extend base).constants ``Int = some ⟨0, .sort (.succ .zero)⟩)
    (sourceBody : Represents a.function.body sourceCore)
    (bodyTyped : (view.extend base).HasType U (List.replicate 3 intType ++ context) sourceCore intType)
    (args : List VExpr) (arity : args.length = 3)
    (typed : ∀ arg ∈ args, (view.extend base).HasType U context arg intType) :
    (view.extend base).IsDefEq U context (applications (.const a.declaration.name []) args)
      (instantiateArgs sourceCore args) intType := by
  have first := view.apply_body_equivalence base declared sourceBody bodyTyped args arity typed
  have forArgs : (view.extend base).HasType U (List.replicate args.length intType ++ context)
      sourceCore intType := arity.symm ▸ bodyTyped
  have second := applications_beta ordered declared args sourceCore forArgs typed
  rw [arity] at second
  exact first.trans second

/-- Adding a source unfolding rule preserves Ordered when the declared
    source body is typed BEFORE that equation is added. This avoids using the
    new equation itself as a circular justification of its source typing. -/
theorem DefinitionView.extend_ordered (view : DefinitionView a) (base : VEnv)
    (ordered : base.Ordered)
    (registered : base.constants a.declaration.name = some ⟨0, view.type.val⟩)
    (bodyTyped : base.HasType 0 [] view.body.val view.type.val) :
    (view.extend base).Ordered := by
  apply VEnv.Ordered.defeq ordered
  constructor
  · have ht := VEnv.HasType.const (U := 0) (Γ := []) (ls := []) registered (by simp) rfl
    simpa only [view.type.property.instL_empty] using ht
  · exact bodyTyped

/-- Construct the required declaration typing from the open body and the
    exact syntax correspondence. No HLS-result equality is a premise. -/
theorem DefinitionView.extend_ordered_from_body (view : DefinitionView a) (base : VEnv)
    (ordered : base.Ordered)
    (declared : base.constants ``Int = some ⟨0, .sort (.succ .zero)⟩)
    (registered : base.constants a.declaration.name = some ⟨0, view.type.val⟩)
    (sourceBody : Represents a.function.body sourceCore)
    (bodyTyped : base.HasType 0 (List.replicate 3 intType) sourceCore intType) :
    (view.extend base).Ordered := by
  apply view.extend_ordered base ordered registered
  obtain ⟨bodyCore, representedBody, same⟩ :=
    represented_function_body a.function.shape view.body.property
  have eqBody := representedBody.unique sourceBody
  subst bodyCore
  rw [same, view.type_shape]
  exact intLambdas_congr declared 3 [] bodyTyped

/-- The exported equation names the same source declaration selected by the
    executable entry, and no other function's body. -/
theorem DefinitionView.source (a : LeanDefinition.Artifact nativeEnv name)
    (view : DefinitionView a) :
    view.equation.lhs = .const name [] ∧
    Represents a.declaration.value view.equation.rhs ∧
    Represents a.declaration.type view.equation.type := by
  exact ⟨congrArg (fun n => VExpr.const n []) a.named, view.body.property, view.type.property⟩

/-- Object-level equality in the formalized source language. Unlike definitional
    equality this can also use proved standard-library facts. -/
def eqInt (left right : VExpr) : VExpr :=
  .app (.app (.app (.const ``Eq [.succ .zero]) intType) left) right

def binaryFactType (leftHead rightHead : VExpr) : VExpr :=
  .forallE intType (.forallE intType
    (eqInt (.app (.app leftHead (.bvar 1)) (.bvar 0))
      (.app (.app rightHead (.bvar 1)) (.bvar 0))))

/-- Instantiate a registered GENERAL library theorem. The registration is an
    exact type lookup, not an assumption of correctness for an input program. -/
theorem apply_binary_fact
    (registered : env.constants factName = some ⟨0, binaryFactType leftHead rightHead⟩)
    (leftClosed : leftHead.ClosedN) (rightClosed : rightHead.ClosedN)
    (leftLevels : leftHead.LevelWF 0) (rightLevels : rightHead.LevelWF 0)
    (hx : env.HasType U context x intType) (hy : env.HasType U context y intType) :
    env.HasType U context (.app (.app (.const factName []) x) y)
      (eqInt (.app (.app leftHead x) y) (.app (.app rightHead x) y)) := by
  have llevels : leftHead.instL [] = leftHead := by
    simpa [VLevel.params] using leftLevels.instL_id
  have rlevels : rightHead.instL [] = rightHead := by
    simpa [VLevel.params] using rightLevels.instL_id
  have fact := VEnv.HasType.const (U := U) (Γ := context) (ls := []) registered (by simp) rfl
  simp only [binaryFactType, eqInt, intType, VExpr.instL, List.map_cons, List.map_nil,
    VLevel.inst, llevels, rlevels] at fact
  have first := VEnv.HasType.app fact hx
  have lc : ∀ a k, leftHead.inst a k = leftHead := fun _ k => leftClosed.instN_eq (Nat.zero_le k)
  have rc : ∀ a k, rightHead.inst a k = rightHead := fun _ k => rightClosed.instN_eq (Nat.zero_le k)
  simp only [VExpr.inst, VExpr.instVar_lower, VExpr.instVar_succ, VExpr.instVar_zero, lc, rc] at first
  have second := VEnv.HasType.app first hy
  simpa only [eqInt, intType, VExpr.inst, VExpr.instVar_zero, VExpr.inst_lift, lc, rc] using second

private theorem numeral_closed (n depth : Nat) : (numeral n).ClosedN depth := by
  induction n <;> simp_all [numeral, VExpr.ClosedN]

theorem Represents.closed (h : Represents e v) (depth : Nat)
    (scope_ok : LeanScalar.wellScoped depth e = true) : v.ClosedN depth := by
  induction h generalizing depth <;>
    simp_all [LeanScalar.wellScoped, VExpr.ClosedN, numeral_closed]
  all_goals grind

/-- Syntactic shape of a general binary equality fact, with arbitrary binder
    names but exact Int arguments and equality type. -/
inductive BinaryFactShape : Lean.Expr → Lean.Expr → Lean.Expr → Prop where
  | intro : BinaryFactShape
      (.forallE x (.const ``Int []) (.forallE y (.const ``Int [])
        (.app (.app (.app (.const ``Eq [.succ .zero]) (.const ``Int []))
          (.app (.app left (.bvar 1)) (.bvar 0)))
          (.app (.app right (.bvar 1)) (.bvar 0))) yi) xi) left right

theorem BinaryFactShape.represents (shape : BinaryFactShape type left right)
    (hl : Represents left leftCore) (hr : Represents right rightCore) :
    Represents type (binaryFactType leftCore rightCore) := by
  cases shape
  exact .forallE (.constant rfl) (.forallE (.constant rfl)
    (.app (.app (.app (.constant rfl) (.constant rfl)) (.app (.app hl .bvar) .bvar))
      (.app (.app hr .bvar) .bvar)))

/-- A fixed, kernel-checked library theorem read from the same native environment.
    This view neither generates nor verifies an input-program equivalence. -/
structure BinaryFactView (nativeEnv : Lean.Environment) (name : Lean.Name) where
  declaration : Lean.TheoremVal
  found : nativeEnv.find? name = some (.thmInfo declaration)
  named : declaration.name = name
  monomorphic : declaration.levelParams = []
  left : Lean.Expr
  right : Lean.Expr
  shape : BinaryFactShape declaration.type left right
  leftScope : LeanScalar.wellScoped 0 left = true
  rightScope : LeanScalar.wellScoped 0 right = true
  leftCore : {v : VExpr // Represents left v}
  rightCore : {v : VExpr // Represents right v}

def viewBinaryFact (nativeEnv : Lean.Environment) (name : Lean.Name) : Option (BinaryFactView nativeEnv name) :=
  match found : nativeEnv.find? name with
  | some (.thmInfo declaration) => do
      if named : declaration.name = name then
        if mono : declaration.levelParams = [] then
          match shape : declaration.type with
          | .forallE _ (.const ``Int []) (.forallE _ (.const ``Int [])
              (.app (.app (.app (.const ``Eq [.succ .zero]) (.const ``Int []))
                (.app (.app left (.bvar 1)) (.bvar 0)))
                (.app (.app right (.bvar 1)) (.bvar 0))) _) _ =>
              if hl : LeanScalar.wellScoped 0 left then
                if hr : LeanScalar.wellScoped 0 right then
                  let leftCore ← translate left
                  let rightCore ← translate right
                  return ⟨declaration, found, named, mono, left, right,
                    shape ▸ .intro, hl, hr, leftCore, rightCore⟩
                else none
              else none
          | _ => none
        else none
      else none
  | _ => none

def BinaryFactView.signature (view : BinaryFactView nativeEnv name) : VConstant :=
  ⟨0, binaryFactType view.leftCore.val view.rightCore.val⟩

theorem BinaryFactView.signature_represents (view : BinaryFactView nativeEnv name) :
    Represents view.declaration.type view.signature.type :=
  view.shape.represents view.leftCore.property view.rightCore.property

/-- Add a declaration without overwriting an existing name. The native library
    fact must already be kernel checked; model-wide validity is a separate
    source-environment obligation, just as for importing source definitions. -/
def BinaryFactView.install (view : BinaryFactView nativeEnv name) (base : VEnv) : Option VEnv :=
  base.addConst name view.signature

theorem BinaryFactView.apply (view : BinaryFactView nativeEnv name)
    (installed : view.install base = some env)
    (hx : env.HasType U context x intType) (hy : env.HasType U context y intType) :
    env.HasType U context (.app (.app (.const name []) x) y)
      (eqInt (.app (.app view.leftCore.val x) y) (.app (.app view.rightCore.val x) y)) := by
  exact apply_binary_fact (VEnv.addConst_self installed)
    (view.leftCore.property.closed 0 view.leftScope) (view.rightCore.property.closed 0 view.rightScope)
    view.leftCore.property.levelWF view.rightCore.property.levelWF hx hy

theorem BinaryFactView.install_ordered (view : BinaryFactView nativeEnv name)
    (installed : view.install base = some env) (ordered : base.Ordered)
    (typeValid : view.signature.WF base) : env.Ordered :=
  .const ordered typeValid installed

namespace Standard

/-- Native Lean facts about the exact standard instances recognized by the
    frontend. These hold for all arguments and introduce no new axioms.
    Exporting and using them in the formal source bridge is a separate step. -/
theorem add (x y : Int) :
    @HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) x y = Int.add x y := rfl

theorem sub (x y : Int) :
    @HSub.hSub Int Int Int (@instHSub Int Int.instSub) x y = Int.sub x y := rfl

theorem mul (x y : Int) :
    @HMul.hMul Int Int Int (@instHMul Int Int.instMul) x y = Int.mul x y := rfl

theorem div (x y : Int) :
    @HDiv.hDiv Int Int Int (@instHDiv Int Int.instDiv) x y = Int.ediv x y := rfl

theorem neg (x : Int) : @Neg.neg Int Int.instNegInt x = Int.neg x := rfl

theorem literal (n : Nat) : @OfNat.ofNat Int n (@instOfNat n) = Int.ofNat n := rfl

/-- Ignoring the decision implementation is valid only for a correctly typed
    decision. Scope checking alone must not be confused with this premise. -/
theorem select (c yes no : Int) (decision : Decidable ((c != 0) = true)) :
    @ite Int ((c != 0) = true) decision yes no = (if c ≠ 0 then yes else no) := by
  by_cases h : c = 0 <;> simp [h]

end Standard

end IRComparison.LeanTyped
