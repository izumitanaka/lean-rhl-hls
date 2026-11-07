import IRComparison.Frontend.LeanScalar

namespace IRComparison.LeanBindings

/-- Rename free de Bruijn positions while preserving the newest binder. -/
def underRename (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n+1 => ρ n + 1

/-- Pure binding operations on the actual Lean.Expr representation.
    We do not assume equations for Lean's opaque C++ instantiation functions. -/
def rename (ρ : Nat → Nat) : Lean.Expr → Lean.Expr
  | .bvar n => .bvar (ρ n)
  | .app f a => .app (rename ρ f) (rename ρ a)
  | .lam name ty body info => .lam name (rename ρ ty) (rename (underRename ρ) body) info
  | .forallE name ty body info => .forallE name (rename ρ ty) (rename (underRename ρ) body) info
  | .letE name ty value body flag =>
      .letE name (rename ρ ty) (rename ρ value) (rename (underRename ρ) body) flag
  | .mdata data body => .mdata data (rename ρ body)
  | .proj name field body => .proj name field (rename ρ body)
  | e => e

def underSubst (σ : Nat → Lean.Expr) : Nat → Lean.Expr
  | 0 => .bvar 0
  | n+1 => rename Nat.succ (σ n)

def substitute (σ : Nat → Lean.Expr) : Lean.Expr → Lean.Expr
  | .bvar n => σ n
  | .app f a => .app (substitute σ f) (substitute σ a)
  | .lam name ty body info => .lam name (substitute σ ty) (substitute (underSubst σ) body) info
  | .forallE name ty body info =>
      .forallE name (substitute σ ty) (substitute (underSubst σ) body) info
  | .letE name ty value body flag =>
      .letE name (substitute σ ty) (substitute σ value) (substitute (underSubst σ) body) flag
  | .mdata data body => .mdata data (substitute σ body)
  | .proj name field body => .proj name field (substitute σ body)
  | e => e

@[simp] theorem underRename_id : underRename id = id := by
  funext n; cases n <;> rfl

@[simp] theorem underRename_comp (ρ τ : Nat → Nat) :
    underRename (ρ ∘ τ) = underRename ρ ∘ underRename τ := by
  funext n; cases n <;> rfl

@[simp] theorem rename_id (e : Lean.Expr) : rename id e = e := by
  induction e <;> simp_all [rename]

theorem rename_comp (e : Lean.Expr) (ρ τ : Nat → Nat) :
    rename ρ (rename τ e) = rename (ρ ∘ τ) e := by
  induction e generalizing ρ τ <;> simp_all [rename]

@[simp] theorem underSubst_bvars (ρ : Nat → Nat) :
    underSubst (fun n => Lean.Expr.bvar (ρ n)) = fun n => Lean.Expr.bvar (underRename ρ n) := by
  funext n; cases n <;> rfl

theorem substitute_bvars (e : Lean.Expr) (ρ : Nat → Nat) :
    substitute (fun n => Lean.Expr.bvar (ρ n)) e = rename ρ e := by
  induction e generalizing ρ <;> simp_all [substitute, rename]

@[simp] theorem substitute_id (e : Lean.Expr) : substitute Lean.Expr.bvar e = e := by
  simpa using substitute_bvars e id

private theorem underSubst_rename (σ : Nat → Lean.Expr) (ρ : Nat → Nat) :
    underSubst (σ ∘ ρ) = underSubst σ ∘ underRename ρ := by
  funext n; cases n <;> rfl

theorem substitute_rename (e : Lean.Expr) (σ : Nat → Lean.Expr) (ρ : Nat → Nat) :
    substitute σ (rename ρ e) = substitute (σ ∘ ρ) e := by
  induction e generalizing σ ρ <;> simp_all [rename, substitute, underSubst_rename]

private theorem underSubst_mapRename (σ : Nat → Lean.Expr) (ρ : Nat → Nat) :
    underSubst (fun n => rename ρ (σ n)) =
      fun n => rename (underRename ρ) (underSubst σ n) := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
      simp only [underSubst, rename_comp]
      rfl

theorem rename_substitute (e : Lean.Expr) (σ : Nat → Lean.Expr) (ρ : Nat → Nat) :
    rename ρ (substitute σ e) = substitute (fun n => rename ρ (σ n)) e := by
  induction e generalizing σ ρ <;> simp_all [rename, substitute, underSubst_mapRename]

private theorem underSubst_comp (σ τ : Nat → Lean.Expr) :
    underSubst (fun n => substitute σ (τ n)) =
      fun n => substitute (underSubst σ) (underSubst τ n) := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
      simp only [underSubst, rename_substitute, substitute_rename]
      rfl

theorem substitute_comp (e : Lean.Expr) (σ τ : Nat → Lean.Expr) :
    substitute σ (substitute τ e) = substitute (fun n => substitute σ (τ n)) e := by
  induction e generalizing σ τ <;> simp_all [substitute, underSubst_comp]

private theorem underRename_maps (ρ : Nat → Nat) (depth target : Nat)
    (maps : ∀ n, n < depth → ρ n < target) :
    ∀ n, n < depth+1 → underRename ρ n < target+1 := by
  intro n hn
  cases n with
  | zero => simp [underRename]
  | succ n => simpa [underRename] using maps n (by omega)

theorem rename_wellScoped (e : Lean.Expr) (depth target : Nat)
    (scope_ok : LeanScalar.wellScoped depth e = true) (ρ : Nat → Nat)
    (maps : ∀ n, n < depth → ρ n < target) :
    LeanScalar.wellScoped target (rename ρ e) = true := by
  induction e generalizing depth target ρ <;>
    simp_all [LeanScalar.wellScoped, rename]
  case app f a hf ha => exact ⟨hf depth target scope_ok.1 ρ maps, ha depth target scope_ok.2 ρ maps⟩
  case lam name ty body info ht hb =>
    exact ⟨ht depth target scope_ok.1 ρ maps,
      hb (depth+1) (target+1) scope_ok.2 (underRename ρ) (underRename_maps ρ depth target maps)⟩
  case forallE name ty body info ht hb =>
    exact ⟨ht depth target scope_ok.1 ρ maps,
      hb (depth+1) (target+1) scope_ok.2 (underRename ρ) (underRename_maps ρ depth target maps)⟩
  case letE name ty value body flag ht hv hb =>
    exact ⟨⟨ht depth target scope_ok.1.1 ρ maps, hv depth target scope_ok.1.2 ρ maps⟩,
      hb (depth+1) (target+1) scope_ok.2 (underRename ρ) (underRename_maps ρ depth target maps)⟩
  case mdata data body ih => exact ih depth target scope_ok ρ maps
  case proj name field body ih => exact ih depth target scope_ok ρ maps

private theorem underSubst_wellScoped (σ : Nat → Lean.Expr) (depth target : Nat)
    (maps : ∀ n, n < depth → LeanScalar.wellScoped target (σ n) = true) :
    ∀ n, n < depth+1 → LeanScalar.wellScoped (target+1) (underSubst σ n) = true := by
  intro n hn
  cases n with
  | zero => simp [underSubst, LeanScalar.wellScoped]
  | succ n =>
    exact rename_wellScoped (σ n) target (target+1) (maps n (by omega)) Nat.succ
      (by intro k hk; omega)

theorem substitute_wellScoped (e : Lean.Expr) (depth target : Nat)
    (scope_ok : LeanScalar.wellScoped depth e = true) (σ : Nat → Lean.Expr)
    (maps : ∀ n, n < depth → LeanScalar.wellScoped target (σ n) = true) :
    LeanScalar.wellScoped target (substitute σ e) = true := by
  induction e generalizing depth target σ <;>
    simp_all [LeanScalar.wellScoped, substitute]
  case app f a hf ha => exact ⟨hf depth target scope_ok.1 σ maps, ha depth target scope_ok.2 σ maps⟩
  case lam name ty body info ht hb =>
    exact ⟨ht depth target scope_ok.1 σ maps,
      hb (depth+1) (target+1) scope_ok.2 (underSubst σ) (underSubst_wellScoped σ depth target maps)⟩
  case forallE name ty body info ht hb =>
    exact ⟨ht depth target scope_ok.1 σ maps,
      hb (depth+1) (target+1) scope_ok.2 (underSubst σ) (underSubst_wellScoped σ depth target maps)⟩
  case letE name ty value body flag ht hv hb =>
    exact ⟨⟨ht depth target scope_ok.1.1 σ maps, hv depth target scope_ok.1.2 σ maps⟩,
      hb (depth+1) (target+1) scope_ok.2 (underSubst σ) (underSubst_wellScoped σ depth target maps)⟩
  case mdata data body ih => exact ih depth target scope_ok σ maps
  case proj name field body ih => exact ih depth target scope_ok σ maps

private theorem underSubst_fixed (σ : Nat → Lean.Expr) (depth : Nat)
    (h : ∀ n, n < depth → σ n = .bvar n) :
    ∀ n, n < depth+1 → underSubst σ n = .bvar n := by
  intro n hn
  cases n with
  | zero => rfl
  | succ n => simp [underSubst, h n (by omega), rename]

/-- A scoped expression cannot observe substitutions outside its scope.
    Proof arguments and annotations are included in the syntactic statement. -/
theorem substitute_eq_of_wellScoped (e : Lean.Expr) (depth : Nat)
    (scope_ok : LeanScalar.wellScoped depth e = true) (σ : Nat → Lean.Expr)
    (fixed : ∀ n, n < depth → σ n = .bvar n) : substitute σ e = e := by
  induction e generalizing depth σ <;>
    simp_all [LeanScalar.wellScoped, substitute]
  case app f a hf ha => exact ⟨hf depth scope_ok.1 σ fixed, ha depth scope_ok.2 σ fixed⟩
  case lam name ty body info ht hb =>
    exact ⟨ht depth scope_ok.1 σ fixed,
      hb (depth+1) scope_ok.2 (underSubst σ) (underSubst_fixed σ depth fixed)⟩
  case forallE name ty body info ht hb =>
    exact ⟨ht depth scope_ok.1 σ fixed,
      hb (depth+1) scope_ok.2 (underSubst σ) (underSubst_fixed σ depth fixed)⟩
  case letE name ty value body flag ht hv hb =>
    exact ⟨ht depth scope_ok.1.1 σ fixed, hv depth scope_ok.1.2 σ fixed,
      hb (depth+1) scope_ok.2 (underSubst σ) (underSubst_fixed σ depth fixed)⟩
  case mdata data body ih => exact ih depth scope_ok σ fixed
  case proj name field body ih => exact ih depth scope_ok σ fixed

/-- No choice of the surrounding variable environment changes closed syntax. -/
theorem substitute_closed (e : Lean.Expr) (scope_ok : LeanScalar.wellScoped 0 e = true)
    (σ : Nat → Lean.Expr) : substitute σ e = e :=
  substitute_eq_of_wellScoped e 0 scope_ok σ (by intro n hn; omega)

theorem accepted_function_closed (result : LeanScalar.FunctionArtifact source)
    (accepted : LeanScalar.compileFunction source = some result) (σ : Nat → Lean.Expr) :
    substitute σ source = source :=
  substitute_closed source (LeanScalar.compileFunction_wellScoped source result accepted) σ

def instantiate (value body : Lean.Expr) : Lean.Expr :=
  substitute (fun | 0 => value | n+1 => .bvar n) body

@[simp] theorem instantiate_zero (value : Lean.Expr) : instantiate value (.bvar 0) = value := rfl

@[simp] theorem instantiate_succ (value : Lean.Expr) (n : Nat) :
    instantiate value (.bvar (n+1)) = .bvar n := rfl

open NativeRHL.ExprAnalysis

private theorem rename_conditional (ρ) (test decision yes no : Lean.Expr) :
    rename ρ (conditional test decision yes no) =
      conditional (rename ρ test) (rename ρ decision) (rename ρ yes) (rename ρ no) := rfl

/-- Scalar interpretation respects actual binder renaming, under arbitrary
    enclosing scopes, not just for closed test expressions. -/
theorem denotes_rename (h : Denotes e env v) (ρ : Nat → Nat) (target : Environment)
    (compatible : ∀ n, target (ρ n) = env n) : Denotes (rename ρ e) target v := by
  induction h generalizing ρ target with
  | «variable» =>
      simp only [rename]
      rw [← compatible]
      exact .variable
  | literal => exact .literal
  | elaboratedLiteral => exact .elaboratedLiteral
  | surfaceLiteral => exact .surfaceLiteral
  | neg _ ih => exact .neg (ih ρ target compatible)
  | surfaceNeg _ ih => exact .surfaceNeg (ih ρ target compatible)
  | add _ _ ha hb => exact .add (ha ρ target compatible) (hb ρ target compatible)
  | sub _ _ ha hb => exact .sub (ha ρ target compatible) (hb ρ target compatible)
  | mul _ _ ha hb => exact .mul (ha ρ target compatible) (hb ρ target compatible)
  | div _ _ ha hb => exact .div (ha ρ target compatible) (hb ρ target compatible)
  | mod _ _ ha hb => exact .mod (ha ρ target compatible) (hb ρ target compatible)
  | surfaceAdd _ _ ha hb => exact .surfaceAdd (ha ρ target compatible) (hb ρ target compatible)
  | surfaceSub _ _ ha hb => exact .surfaceSub (ha ρ target compatible) (hb ρ target compatible)
  | surfaceMul _ _ ha hb => exact .surfaceMul (ha ρ target compatible) (hb ρ target compatible)
  | surfaceDiv _ _ ha hb => exact .surfaceDiv (ha ρ target compatible) (hb ρ target compatible)
  | surfaceMod _ _ ha hb => exact .surfaceMod (ha ρ target compatible) (hb ρ target compatible)
  | branch _ _ _ hc ha hb =>
      rw [rename_conditional]
      exact .branch (hc ρ target compatible) (ha ρ target compatible) (hb ρ target compatible)
  | letValue hv hb ihv ihb =>
      apply Denotes.letValue (ihv ρ target compatible)
      apply ihb (underRename ρ) (bind target _)
      intro n
      cases n with
      | zero => rfl
      | succ n => exact compatible n
  | metadata _ ih => exact .metadata (ih ρ target compatible)

/-- Capture-avoiding substitution implements the environment meaning of
    binding. This is the general bridge needed for beta/zeta rules. -/
theorem denotes_substitute (h : Denotes e env v) (σ : Nat → Lean.Expr) (target : Environment)
    (compatible : ∀ n, Denotes (σ n) target (env n)) :
    Denotes (substitute σ e) target v := by
  induction h generalizing σ target with
  | «variable» => exact compatible _
  | literal => exact .literal
  | elaboratedLiteral => exact .elaboratedLiteral
  | surfaceLiteral => exact .surfaceLiteral
  | neg _ ih => exact .neg (ih σ target compatible)
  | surfaceNeg _ ih => exact .surfaceNeg (ih σ target compatible)
  | add _ _ ha hb => exact .add (ha σ target compatible) (hb σ target compatible)
  | sub _ _ ha hb => exact .sub (ha σ target compatible) (hb σ target compatible)
  | mul _ _ ha hb => exact .mul (ha σ target compatible) (hb σ target compatible)
  | div _ _ ha hb => exact .div (ha σ target compatible) (hb σ target compatible)
  | mod _ _ ha hb => exact .mod (ha σ target compatible) (hb σ target compatible)
  | surfaceAdd _ _ ha hb => exact .surfaceAdd (ha σ target compatible) (hb σ target compatible)
  | surfaceSub _ _ ha hb => exact .surfaceSub (ha σ target compatible) (hb σ target compatible)
  | surfaceMul _ _ ha hb => exact .surfaceMul (ha σ target compatible) (hb σ target compatible)
  | surfaceDiv _ _ ha hb => exact .surfaceDiv (ha σ target compatible) (hb σ target compatible)
  | surfaceMod _ _ ha hb => exact .surfaceMod (ha σ target compatible) (hb σ target compatible)
  | branch _ _ _ hc ha hb =>
      exact .branch (hc σ target compatible) (ha σ target compatible) (hb σ target compatible)
  | letValue hv hb ihv ihb =>
      apply Denotes.letValue (ihv σ target compatible)
      apply ihb (underSubst σ) (bind target _)
      intro n
      cases n with
      | zero => exact .variable
      | succ n =>
          exact denotes_rename (compatible n) Nat.succ (bind target _) (fun _ => rfl)
  | metadata _ ih => exact .metadata (ih σ target compatible)

theorem denotes_instantiate (argument : Denotes a env x)
    (body : Denotes b (bind env x) y) : Denotes (instantiate a b) env y := by
  apply denotes_substitute body
  intro n
  cases n with
  | zero => exact argument
  | succ n => exact .variable

/-- A general zeta computation fact in the scalar fragment. The initializer's
    defined meaning is retained; an unused initializer is not silently ignored. -/
theorem let_computes_by_substitution (argument : Denotes a env x)
    (body : Denotes b (bind env x) y) :
    Denotes (.letE name (.const ``Int []) a b flag) env y ∧
    Denotes (instantiate a b) env y :=
  ⟨.letValue argument body, denotes_instantiate argument body⟩

/-- Closed integer syntax; no Meta evaluation or opaque quotation operation. -/
def quoteInt : Int → Lean.Expr
  | .ofNat n => .app (.const ``Int.ofNat []) (.lit (.natVal n))
  | .negSucc n => .app (.const ``Int.neg [])
      (.app (.const ``Int.ofNat []) (.lit (.natVal (n+1))))

@[simp] theorem rename_quoteInt (ρ) (v : Int) : rename ρ (quoteInt v) = quoteInt v := by
  cases v <;> rfl

@[simp] theorem substitute_quoteInt (σ) (v : Int) :
    substitute σ (quoteInt v) = quoteInt v := by
  cases v <;> rfl

theorem denotes_quoteInt (v : Int) (env : Environment) : Denotes (quoteInt v) env v := by
  cases v with
  | ofNat n => exact .literal
  | negSucc n => exact .neg (.literal (n := n+1))

/-- A specification of beta computation on Expr using the pure operation above.
    This is not a claim about Lean's opaque instantiate1 implementation. -/
inductive Beta : Lean.Expr → Lean.Expr → Prop where
  | step : Beta (.app (.lam name ty body info) value) (instantiate value body)
  | function : Beta f g → Beta (.app f a) (.app g a)
  | trans : Beta a b → Beta b c → Beta a c

theorem Beta.wellScoped (h : Beta e e') (depth : Nat)
    (scope_ok : LeanScalar.wellScoped depth e = true) :
    LeanScalar.wellScoped depth e' = true := by
  induction h with
  | step =>
    simp only [LeanScalar.wellScoped, Bool.and_eq_true] at scope_ok
    apply substitute_wellScoped _ (depth+1) depth scope_ok.1.2
    intro n hn
    cases n with
    | zero => exact scope_ok.2
    | succ n => simpa [LeanScalar.wellScoped] using (show n < depth by omega)
  | function h ih =>
    simp only [LeanScalar.wellScoped, Bool.and_eq_true] at scope_ok ⊢
    exact ⟨ih scope_ok.1, scope_ok.2⟩
  | trans h₁ h₂ ih₁ ih₂ => exact ih₂ (ih₁ scope_ok)

@[simp] theorem quoteInt_wellScoped (v : Int) (depth : Nat) :
    LeanScalar.wellScoped depth (quoteInt v) = true := by
  cases v <;> rfl

/-- The actual residual syntax after applying three arguments. -/
def appliedBody (body : Lean.Expr) (i x y : Int) : Lean.Expr :=
  instantiate (quoteInt y)
    (substitute (underSubst (fun | 0 => quoteInt x | n+1 => .bvar n))
      (substitute (underSubst (underSubst (fun | 0 => quoteInt i | n+1 => .bvar n))) body))

theorem three_beta (shape : LeanScalar.ThreeIntLambdas source body) (i x y : Int) :
    Beta (.app (.app (.app source (quoteInt i)) (quoteInt x)) (quoteInt y))
      (appliedBody body i x y) := by
  cases shape
  exact .trans (.function (.function .step)) (.trans (.function .step) .step)

/-- Preserve arbitrary outer environments, rather than assuming closed syntax. -/
theorem appliedBody_denotes
    (h : Denotes body (bind (bind (bind env i) x) y) v) :
    Denotes (appliedBody body i x y) env v := by
  apply denotes_instantiate (denotes_quoteInt y env)
  have first : Denotes
      (substitute (underSubst (underSubst (fun | 0 => quoteInt i | n+1 => .bvar n))) body)
      (bind (bind env x) y) v := by
    apply denotes_substitute h
    intro n
    match n with
    | 0 => exact .variable
    | 1 => exact .variable
    | 2 => simpa [underSubst] using denotes_quoteInt i (bind (bind env x) y)
    | n+3 => exact .variable
  apply denotes_substitute first
  intro n
  match n with
  | 0 => exact .variable
  | 1 => simpa [underSubst] using denotes_quoteInt x (bind env y)
  | n+2 => exact .variable

/-- Applying an accepted definition leaves no dangling term variables,
    including in annotations and condition-decision arguments. -/
theorem compiled_application_closed (result : LeanScalar.FunctionArtifact source)
    (accepted : LeanScalar.compileFunction source = some result) (i x y : Int) :
    LeanScalar.wellScoped 0 (appliedBody result.body i x y) = true := by
  apply (three_beta result.shape i x y).wellScoped 0
  simp only [LeanScalar.wellScoped, Bool.and_eq_true, quoteInt_wellScoped, and_true]
  exact LeanScalar.compileFunction_wellScoped source result accepted

/-- Every accepted scalar function has a beta residual with exactly the value
    consumed by both IR backends. This does not assume a per-input value proof. -/
theorem compiled_application (result : LeanScalar.FunctionArtifact source)
    (i x y : Int) (s : State) :
    Beta (.app (.app (.app source (quoteInt i)) (quoteInt x)) (quoteInt y))
      (appliedBody result.body i x y) ∧
    Denotes (appliedBody result.body i x y) (fun _ => 0)
      (result.scalar.native i x y s) ∧
    result.scalar.code.expr.eval i x y s = some (result.scalar.native i x y s) := by
  refine ⟨three_beta result.shape i x y, ?_, result.scalar.code.correct i x y s⟩
  apply appliedBody_denotes
  have env : LeanScalar.environment LeanScalar.initialLayout i x y s =
      bind (bind (bind (fun _ => 0) i) x) y := by
    funext n
    match n with
    | 0 | 1 | 2 | _+3 => rfl
  rw [← env]
  exact result.scalar.denotes i x y s

end IRComparison.LeanBindings
