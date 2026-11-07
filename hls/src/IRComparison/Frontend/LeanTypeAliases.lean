import IRComparison.Frontend.LeanLibrary

namespace IRComparison.LeanTypeAliases
open Lean4Lean LeanTyped LeanTypeInference

def identityType : VExpr := .forallE (.sort (.param 0)) (.sort (.param 0))
def identityBody : VExpr := .lam (.sort (.param 0)) (.bvar 0)

/-- Recognize the definition of a transparent identity entry by its actual
    body and type, not by a privileged spelling such as outParam. -/
structure Alias (nativeEnv : Lean.Environment) (name : Lean.Name) where
  declaration : Lean.DefinitionVal
  found : nativeEnv.find? name = some (.defnInfo declaration)
  named : declaration.name = name
  safe : declaration.safety = .safe
  arity : declaration.levelParams.length = 1
  type : LeanLibrary.Represents declaration.levelParams declaration.type identityType
  body : LeanLibrary.Represents declaration.levelParams declaration.value identityBody

deriving instance DecidableEq for Lean.DefinitionSafety

def load (nativeEnv : Lean.Environment) (name : Lean.Name) : Option (Alias nativeEnv name) :=
  match found : nativeEnv.find? name with
  | some (.defnInfo declaration) => do
      if named : declaration.name = name then
        if safe : declaration.safety = .safe then
          if arity : declaration.levelParams.length = 1 then
            let ty ← LeanLibrary.translate declaration.levelParams declaration.type
            let body ← LeanLibrary.translate declaration.levelParams declaration.value
            if ht : ty.val = identityType then
              if hb : body.val = identityBody then
                return ⟨declaration, found, named, safe, arity, ht ▸ ty.property, hb ▸ body.property⟩
              else none
            else none
          else none
        else none
      else none
  | _ => none

def Alias.equation (_alias : Alias nativeEnv name) : VDefEq :=
  { uvars := 1, type := identityType, lhs := .const name [.param 0], rhs := identityBody }

def Alias.install (entry : Alias nativeEnv name) (env : VEnv) : VEnv :=
  env.addDefEq entry.equation

theorem Alias.source (entry : Alias nativeEnv name) :
    LeanLibrary.Represents entry.declaration.levelParams entry.declaration.value entry.equation.rhs ∧
    LeanLibrary.Represents entry.declaration.levelParams entry.declaration.type entry.equation.type :=
  ⟨entry.body, entry.type⟩

/-- Prove both sides well typed before extending the environment. The new
    equation is not used to justify its own well-formedness. -/
theorem Alias.install_ordered (entry : Alias nativeEnv name) (ordered : base.Ordered)
    (declared : base.constants name = some ⟨1, identityType⟩) :
    (entry.install base).Ordered := by
  apply VEnv.Ordered.defeq ordered
  constructor
  · have h := VEnv.HasType.const (U := 1) (Γ := []) (ls := [.param 0])
      declared (by simp [VLevel.WF]) rfl
    simpa [Alias.equation, identityType, VExpr.instL, VLevel.inst] using h
  · exact VEnv.HasType.lam (VEnv.HasType.sort (by decide : VLevel.WF 1 (.param 0)))
      (VEnv.HasType.bvar Lookup.zero)

variable {env : VEnv} {U : Nat} {context : List VExpr}

/-- Delta and beta are both explicit. This is not an unchecked erasure of an
    annotation or an assumed equality of an arbitrary input and its output. -/
theorem Alias.reduce (entry : Alias nativeEnv name)
    (registered : env.defeqs entry.equation) (wf : u.WF U)
    (typed : env.HasType U context arg (.sort u)) :
    env.IsDefEq U context (.app (.const name [u]) arg) arg (.sort u) := by
  have delta := VEnv.IsDefEq.extra (env := env) (uvars := U) (Γ := context)
    (df := entry.equation) (ls := [u]) registered (by simpa using wf) rfl
  simp only [Alias.equation, identityType, identityBody, VExpr.instL,
    List.map_cons, List.map_nil, VLevel.inst, List.getD_cons_zero] at delta
  have first := VEnv.IsDefEq.appDF delta typed
  have bodyTyped : env.HasType U (.sort u :: context) (.bvar 0) (.sort u) :=
    .bvar .zero
  have second := VEnv.IsDefEq.beta bodyTyped typed
  simpa only [VExpr.inst, VExpr.instVar_zero] using first.trans second

def Alias.expand (entry : Alias nativeEnv name) (registered : env.defeqs entry.equation)
    (U : Nat) (context : List VExpr) (source : VExpr)
    (base : Conversion env := noConversion env) :
    Option {r : VExpr × VLevel // env.IsDefEq U context source r.1 (.sort r.2)} := do
  match source with
  | .app (.const head [u]) arg =>
      if same : head = name then
        if wf : u.WF U then
          let typed ← checkWith env base U context arg (.sort u)
          return ⟨(arg,u), same ▸ entry.reduce registered wf typed.down⟩
        else none
      else none
  | _ => none

def Alias.conversion (entry : Alias nativeEnv name) (registered : env.defeqs entry.equation)
    (base : Conversion env := noConversion env) :
    Conversion env := fun U context actual expected => do
  if let some step := entry.expand registered U context actual base then
    if same : step.val.1 = expected then
      return ⟨step.val.2, same ▸ step.property⟩
  if let some step := entry.expand registered U context expected base then
    if same : step.val.1 = actual then
      return ⟨step.val.2, same ▸ step.property.symm⟩
  none

end IRComparison.LeanTypeAliases
