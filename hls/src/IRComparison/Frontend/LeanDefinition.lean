import IRComparison.Frontend.LeanBindings

namespace IRComparison.LeanDefinition

/-- Exact declared type accepted by the current scalar frontend. The binder
    names and binder information are preserved, rather than canonicalized. -/
inductive ScalarFunctionType : Lean.Expr → Prop where
  | intro : ScalarFunctionType
      (.forallE a (.const ``Int []) (.forallE b (.const ``Int [])
        (.forallE c (.const ``Int []) (.const ``Int []) ci) bi) ai)

def checkType : (type : Lean.Expr) → Option (PLift (ScalarFunctionType type))
  | .forallE _ (.const ``Int []) (.forallE _ (.const ``Int [])
      (.forallE _ (.const ``Int []) (.const ``Int []) _) _) _ => some ⟨.intro⟩
  | _ => none

/-- The result retains its exact declaration in the actual Lean environment.
    Environment validity is NOT proved by merely reading this declaration. -/
structure Artifact (env : Lean.Environment) (name : Lean.Name) where
  declaration : Lean.DefinitionVal
  found : env.find? name = some (.defnInfo declaration)
  named : declaration.name = name
  safe : declaration.safety = .safe
  monomorphic : declaration.levelParams = []
  typed : ScalarFunctionType declaration.type
  function : LeanScalar.FunctionArtifact declaration.value
  accepted : LeanScalar.compileFunction declaration.value = some function

def compile (env : Lean.Environment) (name : Lean.Name) : Option (Artifact env name) :=
  match found : env.find? name with
  | some (.defnInfo declaration) => do
      if named : declaration.name = name then
        match safe : declaration.safety with
        | .safe =>
          if monomorphic : declaration.levelParams = [] then
            let ⟨typed⟩ ← checkType declaration.type
            match accepted : LeanScalar.compileFunction declaration.value with
            | some function => return ⟨declaration, found, named, safe, monomorphic,
                typed, function, accepted⟩
            | none => none
          else none
        | _ => none
      else none
  | _ => none

/-- Specification of zero-universe delta unfolding of a safe definition.
    Like Beta, this specifies a Lean calculation rule; it is not a verified
    implementation of the kernel's reducer. -/
inductive Delta (env : Lean.Environment) : Lean.Expr → Lean.Expr → Prop where
  | definition (found : env.find? name = some (.defnInfo declaration))
      (safe : declaration.safety = .safe) (monomorphic : declaration.levelParams = []) :
      Delta env (.const name []) declaration.value
  | function : Delta env f g → Delta env (.app f a) (.app g a)

def applyThree (source : Lean.Expr) (i x y : Int) : Lean.Expr :=
  .app (.app (.app source (LeanBindings.quoteInt i))
    (LeanBindings.quoteInt x)) (LeanBindings.quoteInt y)

/-- The source is now the named definition, not a body supplied independently.
    Interpretation of the residual remains the explicitly documented fragment. -/
theorem Artifact.application (a : Artifact env name) (i x y : Int) (s : State) :
    Delta env (applyThree (.const name []) i x y) (applyThree a.declaration.value i x y) ∧
    LeanBindings.Beta (applyThree a.declaration.value i x y)
      (LeanBindings.appliedBody a.function.body i x y) ∧
    NativeRHL.ExprAnalysis.Denotes (LeanBindings.appliedBody a.function.body i x y)
      (fun _ => 0) (a.function.scalar.native i x y s) ∧
    a.function.scalar.code.expr.eval i x y s = some (a.function.scalar.native i x y s) := by
  exact ⟨.function (.function (.function (.definition a.found a.safe a.monomorphic))),
    LeanBindings.compiled_application a.function i x y s⟩

/-- No successful result can refer to a different definition than the one
    returned by the same environment lookup. -/
theorem Artifact.declaration_unique (a b : Artifact env name) : a.declaration = b.declaration := by
  have h := a.found.symm.trans b.found
  exact Lean.ConstantInfo.defnInfo.inj (Option.some.inj h)

theorem Artifact.application_closed (a : Artifact env name) (i x y : Int) :
    LeanScalar.wellScoped 0 (LeanBindings.appliedBody a.function.body i x y) = true :=
  LeanBindings.compiled_application_closed a.function a.accepted i x y

end IRComparison.LeanDefinition
