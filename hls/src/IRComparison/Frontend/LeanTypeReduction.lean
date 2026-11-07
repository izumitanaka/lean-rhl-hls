import IRComparison.Frontend.LeanUniverseConversion

namespace IRComparison.LeanTypeReduction
open Lean4Lean LeanTypeInference

structure Definition (nativeEnv : Lean.Environment) (name : Lean.Name) where
  declaration : Lean.DefinitionVal
  found : nativeEnv.find? name = some (.defnInfo declaration)
  named : declaration.name = name
  safe : declaration.safety = .safe
  type : {v // LeanLibrary.Represents declaration.levelParams declaration.type v}
  body : {v // LeanLibrary.Represents declaration.levelParams declaration.value v}

def load (nativeEnv : Lean.Environment) (name : Lean.Name) : Option (Definition nativeEnv name) :=
  match found : nativeEnv.find? name with
  | some (.defnInfo declaration) => do
      if named : declaration.name = name then
        if safe : declaration.safety = .safe then
          let type ← LeanLibrary.translate declaration.levelParams declaration.type
          let body ← LeanLibrary.translate declaration.levelParams declaration.value
          return ⟨declaration, found, named, safe, type, body⟩
        else none
      else none
  | _ => none

def Definition.equation (d : Definition nativeEnv name) : VDefEq where
  uvars := d.declaration.levelParams.length
  lhs := .const name (VLevel.params d.declaration.levelParams.length)
  rhs := d.body.val
  type := d.type.val

def Definition.install (d : Definition nativeEnv name) (base : VEnv) : VEnv :=
  base.addDefEq d.equation

theorem Definition.source (d : Definition nativeEnv name) :
    LeanLibrary.Represents d.declaration.levelParams d.declaration.value d.equation.rhs ∧
    LeanLibrary.Represents d.declaration.levelParams d.declaration.type d.equation.type :=
  ⟨d.body.property, d.type.property⟩

theorem Definition.install_ordered (d : Definition nativeEnv name)
    (ordered : base.Ordered)
    (declared : base.constants name = some ⟨d.declaration.levelParams.length, d.type.val⟩)
    (levels : d.type.val.LevelWF d.declaration.levelParams.length)
    (bodyTyped : base.HasType d.declaration.levelParams.length [] d.body.val d.type.val) :
    (d.install base).Ordered := by
  apply VEnv.Ordered.defeq ordered
  constructor
  · have h := VEnv.HasType.const (Γ := []) declared VLevel.params_wf VLevel.params_length
    simpa only [Definition.equation, levels.instL_id] using h
  · exact bodyTyped

variable {env : VEnv} {U : Nat} {context : List VExpr} {levels : List VLevel}

theorem Definition.unfold (d : Definition nativeEnv name)
    (registered : env.defeqs d.equation)
    (hw : ∀ u ∈ levels, u.WF U) (hc : levels.length = d.declaration.levelParams.length) :
    env.IsDefEq U context (.const name levels) (d.body.val.instL levels) (d.type.val.instL levels) := by
  have h := VEnv.IsDefEq.extra (Γ := context) registered hw hc
  simpa only [Definition.equation, VExpr.instL, VLevel.inst_map_id hc] using h

structure Rule (env : VEnv) where
  nativeEnv : Lean.Environment
  name : Lean.Name
  definition : Definition nativeEnv name
  registered : env.defeqs definition.equation

abbrev Result (env : VEnv) (U : Nat) (context : List VExpr) (source : VExpr) :=
  { r : VExpr × VExpr // env.IsDefEq U context source r.1 r.2 }

def unfoldConstant (rules : List (Rule env)) (U : Nat) (context : List VExpr)
    (name : Lean.Name) (levels : List VLevel) : Option (Result env U context (.const name levels)) := do
  match rules with
  | [] => none
  | rule :: rest =>
      if same : name = rule.name then
        if hw : ∀ u ∈ levels, u.WF U then
          if hc : levels.length = rule.definition.declaration.levelParams.length then
            return ⟨(rule.definition.body.val.instL levels, rule.definition.type.val.instL levels),
              by simpa only [same] using rule.definition.unfold (context := context) rule.registered hw hc⟩
          else none
        else none
      else unfoldConstant rest U context name levels

/-- One typed weak-head computation, using a finite list of actual source
    definitions. Every delta/application/beta step constructs its derivation. -/
def step (rules : List (Rule env)) (conversion : Conversion env) (U : Nat)
    (context : List VExpr) (exposure : Exposure env := noExposure env) :
    (source : VExpr) → Option (Result env U context source)
  | .const name levels => unfoldConstant rules U context name levels
  | .app (.lam domain body) arg => do
      let argTyped ← checkWith env conversion U context arg domain exposure
      let ⟨resultType, bodyTyped⟩ ← inferWith env conversion U (domain :: context) body exposure
      return ⟨(body.inst arg, resultType.inst arg), .beta bodyTyped argTyped.down⟩
  | .app f arg => do
      let reduced ← step rules conversion U context exposure f
      match reduced.val, reduced.property with
      | (fn, .forallE domain codomain), hf =>
          let argTyped ← checkWith env conversion U context arg domain exposure
          let applied := VEnv.IsDefEq.appDF hf argTyped.down
          match fn, applied with
          | .lam binder body, applied =>
              if same : binder = domain then
                let bodyTyped ← checkWith env conversion U (domain :: context) body codomain exposure
                let beta := VEnv.IsDefEq.beta bodyTyped.down argTyped.down
                return ⟨(body.inst arg, codomain.inst arg), applied.trans (by simpa only [same] using beta)⟩
              else return ⟨(.app (.lam binder body) arg, codomain.inst arg), applied⟩
          | other, applied => return ⟨(.app other arg, codomain.inst arg), applied⟩
      | _, _ => none
  | _ => none

/-- Bounded search controls computation cost, not the meaning of a successful
    result. Every number of steps has the same typed correctness guarantee. -/
def reduce (rules : List (Rule env)) (conversion : Conversion env) (U : Nat)
    (context : List VExpr) (exposure : Exposure env := noExposure env) :
    Nat → (source : VExpr) → Option (Result env U context source)
  | 0, _ => none
  | fuel+1, source => do
      let first ← step rules conversion U context exposure source
      if let some next := reduce rules conversion U context exposure fuel first.val.1 then
        if same : next.val.2 = first.val.2 then
          return ⟨(next.val.1, first.val.2), first.property.trans (same ▸ next.property)⟩
        if let some conversionProof := conversion U context next.val.2 first.val.2 then
          return ⟨(next.val.1, first.val.2),
            first.property.trans (.defeqDF conversionProof.property next.property)⟩
      return first

def expose (rules : List (Rule env)) (conversion : Conversion env) (U : Nat)
    (context : List VExpr) (source : VExpr) (fuel : Nat := 32) :
    Option {r : VExpr × VLevel // env.IsDefEq U context source r.1 (.sort r.2)} := do
  let reduced ← reduce rules conversion U context (noExposure env) fuel source
  match reduced.val, reduced.property with
  | (target, .sort u), h => return ⟨(target, u), h⟩
  | _, _ => none

/-- Type conversion by faithful delta/beta reduction on either side. -/
def conversion (rules : List (Rule env)) (base : Conversion env) : Conversion env :=
  fun U context actual expected => do
    if let some r := expose rules base U context actual then
      if same : r.val.1 = expected then
        return ⟨r.val.2, by simpa only [same] using r.property⟩
    if let some r := expose rules base U context expected then
      if same : r.val.1 = actual then
        return ⟨r.val.2, by simpa only [same] using r.property.symm⟩
    base U context actual expected

end IRComparison.LeanTypeReduction
