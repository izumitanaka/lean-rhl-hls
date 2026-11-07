import IRComparison.Frontend.LeanArithmeticNormalization

namespace IRComparison.LeanTypeInference
open Lean4Lean LeanTyped

def lookup : (context : List VExpr) → (n : Nat) → Option {ty // Lookup context n ty}
  | [], _ => none
  | ty :: _, 0 => some ⟨ty.lift, .zero⟩
  | _ :: context, n+1 => do
      let ⟨ty, found⟩ ← lookup context n
      return ⟨ty.lift, .succ found⟩

/-- A conversion procedure must return a typed derivation, not a Boolean
    claim of equality. Different reduction strategies share this interface. -/
abbrev Conversion (env : VEnv) := (U : Nat) → (context : List VExpr) →
  (actual expected : VExpr) → Option {u // env.IsDefEq U context actual expected (.sort u)}

def noConversion (env : VEnv) : Conversion env := fun _ _ _ _ => none

abbrev Exposure (env : VEnv) := (U : Nat) → (context : List VExpr) →
  (source : VExpr) → Option {r : VExpr × VLevel // env.IsDefEq U context source r.1 (.sort r.2)}

def noExposure (env : VEnv) : Exposure env := fun _ _ _ => none

/-- A conservative proof-producing inference function for the proof-side Lean
    calculus. A supplied conversion procedure must provide a typed proof.
    Failure does not establish ill-typedness or change the source language. -/
def inferWith (env : VEnv) (conversion : Conversion env) (U : Nat) (context : List VExpr)
    (e : VExpr) (exposure : Exposure env := noExposure env) :
    Option {ty // env.HasType U context e ty} := match e with
  | .bvar n => do
      let ⟨ty, found⟩ ← lookup context n
      return ⟨ty, .bvar found⟩
  | .sort u =>
      if h : u.WF U then some ⟨.sort (.succ u), .sort h⟩ else none
  | .const name levels => do
      match found : env.constants name with
      | none => none
      | some info =>
          if hw : ∀ u ∈ levels, u.WF U then
            if hc : levels.length = info.uvars then
              return ⟨info.type.instL levels, .const found hw hc⟩
            else none
          else none
  | .app f a => do
      let ⟨ft, hf⟩ ← inferWith env conversion (exposure := exposure) U context f
      let functionView : Option {ty // env.HasType U context f ty} :=
        match ft, hf with
        | .forallE domain body, hf => some ⟨.forallE domain body, hf⟩
        | other, hf => do
            let exposed ← exposure U context other
            return ⟨exposed.val.1, .defeq exposed.property hf⟩
      let ⟨ft, hf⟩ ← functionView
      let ⟨argType, ha⟩ ← inferWith env conversion (exposure := exposure) U context a
      match ft, hf with
      | .forallE domain body, hf =>
          if h : argType = domain then
            return ⟨body.inst a, .app hf (h ▸ ha)⟩
          else do
            let ⟨_, converted⟩ ← conversion U context argType domain
            return ⟨body.inst a, .app hf (.defeq converted ha)⟩
      | _, _ => none
  | .lam domain body => do
      let ⟨dt, hd⟩ ← inferWith env conversion (exposure := exposure) U context domain
      match dt, hd with
      | .sort _, hd =>
          let ⟨bt, hb⟩ ← inferWith env conversion (exposure := exposure) U (domain :: context) body
          return ⟨.forallE domain bt, .lam hd hb⟩
      | _, _ => none
  | .forallE domain body => do
      let ⟨dt, hd⟩ ← inferWith env conversion (exposure := exposure) U context domain
      match dt, hd with
      | .sort u, hd =>
          let ⟨bt, hb⟩ ← inferWith env conversion (exposure := exposure) U (domain :: context) body
          match bt, hb with
          | .sort v, hb => return ⟨.sort (.imax u v), .forallE hd hb⟩
          | _, _ => none
      | _, _ => none

def infer (env : VEnv) (U : Nat) (context : List VExpr) (e : VExpr) :=
  inferWith env (noConversion env) U context e

def checkWith (env : VEnv) (conversion : Conversion env) (U : Nat)
    (context : List VExpr) (e expected : VExpr)
    (exposure : Exposure env := noExposure env) :
    Option (PLift (env.HasType U context e expected)) := do
  let ⟨actual, typed⟩ ← inferWith env conversion (exposure := exposure) U context e
  if same : actual = expected then return ⟨same ▸ typed⟩
  else
    let ⟨_, converted⟩ ← conversion U context actual expected
    return ⟨.defeq converted typed⟩

def check (env : VEnv) (U : Nat) (context : List VExpr) (e expected : VExpr) :=
  checkWith env (noConversion env) U context e expected

theorem infer_sound (result : {ty // env.HasType U context e ty})
    (_accepted : infer env U context e = some result) :
    env.HasType U context e result.val := result.property

theorem check_sound (result : PLift (env.HasType U context e ty))
    (_accepted : check env U context e ty = some result) :
    env.HasType U context e ty := result.down

deriving instance DecidableEq for VConstant

open LeanArithmeticNormalization in
def checkReady (env : VEnv) (U : Nat) (context : List VExpr)
    (conversion : Conversion env := noConversion env)
    (p : Plan nativeEnv source) (exposure : Exposure env := noExposure env) :
    Option (PLift (p.Ready (env := env) (U := U) (context := context))) := match p with
  | .leaf core => checkWith env conversion (exposure := exposure) U context core.val intType
  | .negative flavor _ body => do
      if registered : env.constants flavor.fact = some ⟨0,flavor.signature⟩ then
        let hs ← checkWith env conversion U context (.app flavor.coreHead body.sourceCore) intType exposure
        let ht ← checkWith env conversion U context (LeanNegNormalization.target body.normalizedCore) intType exposure
        let hb ← checkReady env U context conversion body exposure
        return ⟨registered,hs.down,ht.down,hb.down⟩
      else none
  | .elaboratedLiteral n _ => do
      if registered : env.constants ``LeanLiteralNormalization.elaboratedFact = some ⟨0, LeanLiteralNormalization.elaboratedSignature⟩ then
        let hn ← checkWith env conversion U context (numeral n) LeanLiteralNormalization.natType exposure
        let hs ← checkWith env conversion U context (LeanLiteralNormalization.elaboratedCore (numeral n)) intType exposure
        let ht ← checkWith env conversion U context (LeanLiteralNormalization.target (numeral n)) intType exposure
        return ⟨registered, hn.down, hs.down, ht.down⟩
      else none
  | .literal n _ => do
      if registered : env.constants ``Standard.literal = some ⟨0, LeanLiteralNormalization.signature⟩ then
        let hn ← checkWith env conversion U context (numeral n) LeanLiteralNormalization.natType exposure
        let hs ← checkWith env conversion U context (LeanLiteralNormalization.core (numeral n)) intType exposure
        let ht ← checkWith env conversion U context (LeanLiteralNormalization.target (numeral n)) intType exposure
        return ⟨registered, hn.down, hs.down, ht.down⟩
      else none
  | .metadata body => checkReady env U context conversion (exposure := exposure) body
  | .binary op fact left right => do
      if h : env.constants (LeanArithmetic.factName op) = some fact.view.signature then
        let hs ← checkWith env conversion (exposure := exposure) U context fact.view.leftCore.val (intArrows 2)
        let hp ← checkWith env conversion (exposure := exposure) U context (.const op.primitive []) (intArrows 2)
        let hl ← checkReady env U context conversion (exposure := exposure) left
        let hr ← checkReady env U context conversion (exposure := exposure) right
        return ⟨h, hs.down, hp.down, hl.down, hr.down⟩
      else none

open LeanArithmeticNormalization in
structure Result (nativeEnv : Lean.Environment) (env : VEnv) (U : Nat)
    (context : List VExpr) (source : Lean.Expr) where
  plan : Plan nativeEnv source
  ready : plan.Ready (env := env) (U := U) (context := context)
  reflFact : FixedFact nativeEnv ``Standard.intRefl reflType
  transFact : FixedFact nativeEnv ``Standard.intTrans transType
  congrFact : FixedFact nativeEnv ``Standard.intCongr congrType
  reflRegistered : env.constants ``Standard.intRefl = some ⟨0, reflType⟩
  transRegistered : env.constants ``Standard.intTrans = some ⟨0, transType⟩
  congrRegistered : env.constants ``Standard.intCongr = some ⟨0, congrType⟩

/-- This entry constructs its typing obligations. No Ready premise or
    per-input source/target equivalence is supplied by the caller. -/
def normalize (nativeEnv : Lean.Environment) (env : VEnv) (U : Nat)
    (context : List VExpr) (source : Lean.Expr)
    (conversion : Conversion env := noConversion env)
    (exposure : Exposure env := noExposure env) : Option (Result nativeEnv env U context source) := do
  let reflFact ← loadFixedFact nativeEnv ``Standard.intRefl reflType
  let transFact ← loadFixedFact nativeEnv ``Standard.intTrans transType
  let congrFact ← loadFixedFact nativeEnv ``Standard.intCongr congrType
  if hr : env.constants ``Standard.intRefl = some ⟨0, reflType⟩ then
    if ht : env.constants ``Standard.intTrans = some ⟨0, transType⟩ then
      if hc : env.constants ``Standard.intCongr = some ⟨0, congrType⟩ then
        let p ← LeanArithmeticNormalization.plan nativeEnv source
        let ready ← checkReady env U context conversion (exposure := exposure) p
        return ⟨p, ready.down, reflFact, transFact, congrFact, hr, ht, hc⟩
      else none
    else none
  else none

theorem Result.correct (r : Result nativeEnv env U context source) :
    Represents source r.plan.sourceCore ∧
    Represents r.plan.expression r.plan.normalizedCore ∧
    env.HasType U context r.plan.proofTerm (eqInt r.plan.sourceCore r.plan.normalizedCore) :=
  ⟨r.plan.represents_source, r.plan.represents_normalized,
    (r.plan.correct r.reflRegistered r.transRegistered r.congrRegistered r.ready).2.2⟩

theorem normalize_correct (r : Result nativeEnv env U context source)
    (conversion : Conversion env) (exposure : Exposure env)
    (_accepted : normalize nativeEnv env U context source conversion (exposure := exposure) = some r) :
    env.HasType U context r.plan.proofTerm (eqInt r.plan.sourceCore r.plan.normalizedCore) :=
  r.correct.2.2

end IRComparison.LeanTypeInference
