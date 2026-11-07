import IRComparison.Frontend.LeanTyped

namespace IRComparison.LeanSourceEntry
open Lean4Lean LeanTyped

/-- Lean compiler metadata has no computational meaning. Remove it at every
    expression position, including inside typeclass arguments and types. -/
def strip : Lean.Expr → Lean.Expr
  | .mdata _ e => strip e
  | .app f a => .app (strip f) (strip a)
  | .lam n ty b bi => .lam n (strip ty) (strip b) bi
  | .forallE n ty b bi => .forallE n (strip ty) (strip b) bi
  | .letE n ty v b flag => .letE n (strip ty) (strip v) (strip b) flag
  | .proj n i e => .proj n i (strip e)
  | e => e

theorem represents_original (e : Lean.Expr) (h : Represents (strip e) core) : Represents e core := by
  induction e generalizing core with
  | bvar n => exact h
  | fvar n => exact h
  | mvar n => exact h
  | sort u => exact h
  | const n us => exact h
  | lit l => exact h
  | app f a hf ha => cases h with | app h₁ h₂ => exact .app (hf h₁) (ha h₂)
  | lam n ty b bi ht hb => cases h with | lam h₁ h₂ => exact .lam (ht h₁) (hb h₂)
  | forallE n ty b bi ht hb => cases h with | forallE h₁ h₂ => exact .forallE (ht h₁) (hb h₂)
  | letE n ty v b flag ht hv hb =>
      cases h with | letE h₁ h₂ h₃ => exact .letE (ht h₁) (hv h₂) (hb h₃)
  | mdata data e ih => exact .metadata (ih h)
  | proj n i e ih => cases h

structure Header (env : Lean.Environment) (name : Lean.Name) where
  declaration : Lean.DefinitionVal
  found : env.find? name = some (.defnInfo declaration)
  named : declaration.name = name
  safe : declaration.safety = .safe
  monomorphic : declaration.levelParams = []
  typed : LeanDefinition.ScalarFunctionType (strip declaration.type)
  closed : LeanScalar.wellScoped 0 declaration.value = true
  body : Lean.Expr
  shape : LeanScalar.ThreeIntLambdas (strip declaration.value) body

/-- This entry checks declaration and binder shape, not the legacy Denotes
    parser. Successful compilation must subsequently construct the semantic
    equality against the actual IR evaluator. -/
def load (env : Lean.Environment) (name : Lean.Name) : Option (Header env name) :=
  match found : env.find? name with
  | some (.defnInfo declaration) => do
      if named : declaration.name = name then
        match safe : declaration.safety with
        | .safe =>
          if mono : declaration.levelParams = [] then
            let typed ← LeanDefinition.checkType (strip declaration.type)
            if closed : LeanScalar.wellScoped 0 declaration.value then
              match shape : strip declaration.value with
              | .lam _ (.const ``Int []) (.lam _ (.const ``Int []) (.lam _ (.const ``Int []) body _) _) _ =>
                  return ⟨declaration,found,named,safe,mono,typed.down,closed,body,shape ▸ .intro⟩
              | _ => none
            else none
          else none
        | _ => none
      else none
  | _ => none

theorem Header.represents_function (h : Header env name) (body : Represents h.body core) :
    Represents h.declaration.value (intLambdas 3 core) := by
  apply represents_original
  have shape := h.shape
  generalize he : strip h.declaration.value = source at shape ⊢
  cases shape
  exact .lam (.constant rfl) (.lam (.constant rfl) (.lam (.constant rfl) body))

theorem Header.represents_type (h : Header env name) : Represents h.declaration.type scalarType := by
  apply represents_original
  have shape := h.typed
  generalize he : strip h.declaration.type = type at shape ⊢
  cases shape
  exact .forallE (.constant rfl) (.forallE (.constant rfl) (.forallE (.constant rfl) (.constant rfl)))

end IRComparison.LeanSourceEntry
