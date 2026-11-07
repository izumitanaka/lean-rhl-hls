import IRComparison.Frontend.LeanTypeInference

namespace IRComparison.LeanLibrary
open Lean4Lean

/-- Universe names are bound by the declaration, in declaration order. -/
def parameter (names : List Lean.Name) (name : Lean.Name) : Option Nat :=
  match names with
  | [] => none
  | first :: rest => if name = first then some 0 else (parameter rest name).map Nat.succ

def level (names : List Lean.Name) : Lean.Level → Option VLevel
  | .zero => some .zero
  | .succ u => return .succ (← level names u)
  | .max u v => return .max (← level names u) (← level names v)
  | .imax u v => return .imax (← level names u) (← level names v)
  | .param name => return .param (← parameter names name)
  | .mvar _ => none

/-- Structural correspondence for declaration types with universe binders.
    This imports types only, not definition bodies or reduction equations. -/
inductive Represents (names : List Lean.Name) : Lean.Expr → VExpr → Prop where
  | bvar : Represents names (.bvar n) (.bvar n)
  | sort (h : level names u = some v) : Represents names (.sort u) (.sort v)
  | constant (h : us.mapM (level names) = some vs) :
      Represents names (.const name us) (.const name vs)
  | app : Represents names f f' → Represents names a a' → Represents names (.app f a) (.app f' a')
  | lam : Represents names ty ty' → Represents names b b' →
      Represents names (.lam name ty b info) (.lam ty' b')
  | forallE : Represents names ty ty' → Represents names b b' →
      Represents names (.forallE name ty b info) (.forallE ty' b')
  | letE : Represents names ty ty' → Represents names value value' → Represents names b b' →
      Represents names (.letE name ty value b flag) (.app (.lam ty' b') value')
  | metadata : Represents names b b' → Represents names (.mdata data b) b'
  | natural : Represents names (.lit (.natVal n)) (LeanTyped.numeral n)

def translate (names : List Lean.Name) : (e : Lean.Expr) → Option {v // Represents names e v}
  | .bvar n => some ⟨.bvar n, .bvar⟩
  | .sort u =>
      match h : level names u with
      | some v => some ⟨.sort v, .sort h⟩
      | none => none
  | .const name us =>
      match h : us.mapM (level names) with
      | some vs => some ⟨.const name vs, .constant h⟩
      | none => none
  | .app f a => do
      let ⟨f', hf⟩ ← translate names f
      let ⟨a', ha⟩ ← translate names a
      return ⟨.app f' a', .app hf ha⟩
  | .lam _ ty b _ => do
      let ⟨ty', ht⟩ ← translate names ty
      let ⟨b', hb⟩ ← translate names b
      return ⟨.lam ty' b', .lam ht hb⟩
  | .forallE _ ty b _ => do
      let ⟨ty', ht⟩ ← translate names ty
      let ⟨b', hb⟩ ← translate names b
      return ⟨.forallE ty' b', .forallE ht hb⟩
  | .letE _ ty value b _ => do
      let ⟨ty', ht⟩ ← translate names ty
      let ⟨value', hv⟩ ← translate names value
      let ⟨b', hb⟩ ← translate names b
      return ⟨.app (.lam ty' b') value', .letE ht hv hb⟩
  | .mdata _ b => do
      let ⟨b', hb⟩ ← translate names b
      return ⟨b', .metadata hb⟩
  | .lit (.natVal n) => some ⟨LeanTyped.numeral n, .natural⟩
  | _ => none

structure Declaration (nativeEnv : Lean.Environment) (name : Lean.Name) where
  info : Lean.ConstantInfo
  found : nativeEnv.find? name = some info
  named : info.name = name
  type : {v // Represents info.levelParams info.type v}

def load (nativeEnv : Lean.Environment) (name : Lean.Name) : Option (Declaration nativeEnv name) :=
  match found : nativeEnv.find? name with
  | none => none
  | some info => do
      if named : info.name = name then
        let type ← translate info.levelParams info.type
        return ⟨info, found, named, type⟩
      else none

def Declaration.signature (d : Declaration nativeEnv name) : VConstant :=
  ⟨d.info.levelParams.length, d.type.val⟩

def Declaration.install (d : Declaration nativeEnv name) (base : VEnv) : Option VEnv :=
  base.addConst name d.signature

theorem Declaration.installed (d : Declaration nativeEnv name)
    (h : d.install base = some env) :
    env.constants name = some d.signature ∧ Represents d.info.levelParams d.info.type d.signature.type :=
  ⟨VEnv.addConst_self h, d.type.property⟩

/-- Register types selected from the actual environment. This does not prove
    Ordered or import the semantics of constants by adding arbitrary equations. -/
def installTypes (nativeEnv : Lean.Environment) (base : VEnv) : List Lean.Name → Option VEnv
  | [] => some base
  | name :: rest => do
      let d ← load nativeEnv name
      let next ← d.install base
      installTypes nativeEnv next rest

/-- Every imported signature is the translation of that exact native
    declaration. This is provenance, not an assumed source/target equality. -/
def Faithful (native : Lean.Environment) (env : VEnv) : Prop :=
  ∀ name signature, env.constants name = some signature →
    ∃ d : Declaration native name, signature = d.signature

theorem faithful_empty : Faithful native VEnv.empty := by
  intro name signature h
  cases h

theorem Declaration.install_faithful (d : Declaration native name)
    (baseFaithful : Faithful native base) (installed : d.install base = some env) :
    Faithful native env := by
  unfold Declaration.install VEnv.addConst at installed
  split at installed
  · cases installed
  · cases installed
    intro other signature found
    by_cases same : name = other
    · subst other
      simp only [ite_true, Option.some.injEq] at found
      exact ⟨d,found.symm⟩
    · simp only [same, ite_false] at found
      exact baseFaithful other signature found

theorem installTypes_faithful (names : List Lean.Name)
    (baseFaithful : Faithful native base)
    (installed : installTypes native base names = some env) : Faithful native env := by
  induction names generalizing base with
  | nil => cases installed; exact baseFaithful
  | cons name names ih =>
      simp only [installTypes] at installed
      cases hd : load native name with
      | none => simp [hd] at installed
      | some d =>
        cases he : d.install base with
        | none => simp [hd,he] at installed
        | some next =>
          simp [hd,he] at installed
          exact ih (d.install_faithful baseFaithful he) installed

theorem installTypes_no_equations (names : List Lean.Name)
    (baseEmpty : ∀ equation, ¬ base.defeqs equation)
    (installed : installTypes native base names = some env) : ∀ equation, ¬ env.defeqs equation := by
  induction names generalizing base with
  | nil => cases installed; exact baseEmpty
  | cons name names ih =>
      simp only [installTypes] at installed
      cases hd : load native name with
      | none => simp [hd] at installed
      | some d =>
        cases he : d.install base with
        | none => simp [hd,he] at installed
        | some next =>
          simp [hd,he] at installed
          apply ih (base := next) _ installed
          unfold Declaration.install VEnv.addConst at he
          split at he
          · cases he
          · cases he; exact baseEmpty

end IRComparison.LeanLibrary
