import IRComparison.Core.LoopFacts
import IRComparison.Frontend.LeanSourceToIR
import IRComparison.Frontend.LeanBodyQuotation
import IRComparison.Frontend.LeanProofApplication

namespace IRComparison.LeanLoopNormalization
open Lean4Lean LeanTyped LeanIRQuotation LeanIREvaluation LeanBodyQuotation LeanTypeInference
variable {env : VEnv} {U : Nat} {context : List VExpr}

@[reducible] def stepType : VExpr := .app (.const ``ForInStep [.zero]) stateType
@[reducible] def optionStep : VExpr := .app (.const ``Option [.zero]) stepType
def liftValue (v : VExpr) := VExpr.app (.const ``LoopFacts.lift []) v
def stepEq (a b : VExpr) := applications (.const ``Eq [.succ .zero]) [optionStep,a,b]

def cast (conversion : Conversion env) (t : LeanProofApplication.Typed env U context) (expected : VExpr) :
    Option {p : VExpr // env.HasType U context p expected} := do
  if same : t.type = expected then return ⟨t.term,same ▸ t.correct⟩
  let h ← conversion U context t.type expected
  return ⟨t.term,.defeq h.property t.correct⟩

structure Artifact (source : Lean.Expr) where
  plain : Lean.Expr
  sourceCore : {v // Represents source v}
  plainCore : {v // Represents plain v}
  sourceTyped : env.HasType U context sourceCore.val optionStep
  plainTyped : env.HasType U context plainCore.val optionState
  proof : VExpr
  correct : env.HasType U context proof (stepEq (liftValue plainCore.val) sourceCore.val)

def finish (conversion : Conversion env) (exposure : Exposure env) (source plain : Lean.Expr)
    (proof : LeanProofApplication.Typed env U context) : Option (Artifact (env := env) (U := U) (context := context) source) := do
  let s ← translate source
  let p ← translate plain
  let hs ← checkWith env conversion U context s.val optionStep exposure
  let hp ← checkWith env conversion U context p.val optionState exposure
  let q ← cast conversion proof (stepEq (liftValue p.val) s.val)
  return ⟨plain,s,p,hs.down,hp.down,q.val,q.property⟩

def optionExpr : Lean.Expr := .const ``Option [.zero]
def stateExpr : Lean.Expr := .const ``State []
def stepExpr : Lean.Expr := .app (.const ``ForInStep [.zero]) stateExpr

def bindHead (domain result : Lean.Expr) : Lean.Expr :=
  Lean.mkAppN (.const ``Bind.bind [.zero,.zero]) #[optionExpr,
    Lean.mkAppN (.const ``Monad.toBind [.zero,.zero]) #[optionExpr,.const ``instMonadOption [.zero]],domain,result]

def args (native : Lean.Environment) (fact : Lean.Name) (arguments : List (LeanProofApplication.Typed env U context)) :
    Option (LeanProofApplication.Typed env U context) := do
  let f ← LeanProofApplication.constant native env U context fact
  arguments.foldlM LeanProofApplication.apply f

def declarations : List Lean.Name := [``ForInStep, ``ForInStep.yield, ``LoopFacts.lift,
  ``LoopFacts.someYield, ``LoopFacts.bindState, ``LoopFacts.bindInt, ``LoopFacts.bindUnit,
  ``LoopFacts.branch, ``LoopFacts.compose, ``LoopFacts.imperative, ``LoopFacts.functional,
  ``PUnit, ``PUnit.unit, ``Pure, ``Bind, ``Monad, ``Applicative, ``Alternative]

def beta (conversion : Conversion env) (exposure : Exposure env) (source : Lean.Expr)
    (next : Artifact (env := env) (U := U) (context := context) nextSource) :
    Option (Artifact (env := env) (U := U) (context := context) source) := do
  let sc ← translate source
  let reduced ← LeanTypeReduction.step [] conversion U context exposure sc.val
  if same : reduced.val.1 = next.sourceCore.val then
    if ty : reduced.val.2 = optionStep then
      let hs ← checkWith env conversion U context sc.val optionStep exposure
      let he ← check env U context (.app (.const ``Eq [.succ .zero]) optionStep)
        (.forallE optionStep (.forallE optionStep (.sort .zero)))
      let hl ← checkWith env conversion U context (liftValue next.plainCore.val) optionStep exposure
      have eq : env.IsDefEq U context sc.val next.sourceCore.val optionStep := by
        simpa only [same,ty] using reduced.property
      have congr : env.IsDefEq U context
          (stepEq (liftValue next.plainCore.val) sc.val)
          (stepEq (liftValue next.plainCore.val) next.sourceCore.val) (.sort .zero) := by
        have head := VEnv.IsDefEq.appDF he.down hl.down
        simp only [optionStep,stepType,stateType,VExpr.inst] at head
        exact .appDF head eq
      return ⟨next.plain,sc,next.plainCore,hs.down,next.plainTyped,next.proof,
        .defeq congr.symm next.correct⟩
    else none
  else none

/-- Strip only administrative yielding/binding of Lean's for-loop callback.
    The result remains a Lean expression. The returned proof relates the whole
    callback, including failure, to the normalized state-returning expression. -/
def compile (native : Lean.Environment) {context : List VExpr}
    (conversion : Conversion env) (exposure : Exposure env) :
    Nat → (source : Lean.Expr) → Option (Artifact (env := env) (U := U) (context := context) source)
  | 0, _ => none
  | fuel+1, source => do
    match source with
    | .letE name ty value body flag =>
      let next ← compile native conversion exposure fuel (LeanBindings.instantiate value body)
      beta conversion exposure (.letE name ty value body flag) next
    | .app (.lam name ty body binder) value =>
      let next ← compile native conversion exposure fuel (LeanBindings.instantiate value body)
      beta conversion exposure (.app (.lam name ty body binder) value) next
    | .app head (.app (.app (.const ``ForInStep.yield [.zero]) (.const ``State [])) state) =>
      let sc ← translate state
      let hs ← checkWith env conversion U context sc.val stateType exposure
      let p := Lean.mkAppN (.const ``Option.some [.zero]) #[stateExpr,state]
      let q ← args native ``LoopFacts.someYield [⟨sc.val,stateType,hs.down⟩]
      finish conversion exposure (.app head (.app (.app (.const ``ForInStep.yield [.zero]) (.const ``State [])) state)) p q
    | .app (.app head first) (.lam name ty body binder) =>
      if ty == .const ``PUnit [.succ .zero] then
        let unit := Lean.Expr.const ``PUnit.unit [.succ .zero]
        let next ← compile native conversion exposure fuel (LeanBindings.instantiate unit body)
        let f ← translate (.lam name ty body binder)
        let ft := VExpr.forallE (.const ``PUnit [.succ .zero]) optionStep
        let hf ← checkWith env conversion U context f.val ft exposure
        let hp ← cast conversion (⟨next.proof,_,next.correct⟩ : LeanProofApplication.Typed env U context)
          (stepEq (liftValue next.plainCore.val) (.app f.val (.const ``PUnit.unit [.succ .zero])))
        let q ← args native ``LoopFacts.bindUnit
          [⟨next.plainCore.val,optionState,next.plainTyped⟩,⟨f.val,ft,hf.down⟩,⟨hp.val,_,hp.property⟩]
        finish conversion exposure (.app (.app head first) (.lam name ty body binder)) next.plain q
      else if ty == stateExpr || ty == .const ``Int [] then
        let domain ← translate ty
        let hd ← checkWith env conversion U context domain.val (.sort (.succ .zero)) exposure
        let next ← compile (context := domain.val :: context) native conversion exposure fuel body
        let pc := VExpr.lam domain.val next.plainCore.val
        let oc := VExpr.lam domain.val next.sourceCore.val
        let hp := VEnv.IsDefEq.lamDF hd.down next.plainTyped
        let ho := VEnv.IsDefEq.lamDF hd.down next.sourceTyped
        let expected := stepEq (liftValue (.app (pc.liftN 1) (.bvar 0))) (.app (oc.liftN 1) (.bvar 0))
        let child ← cast conversion (⟨next.proof,_,next.correct⟩ : LeanProofApplication.Typed env U (domain.val :: context)) expected
        let premise : LeanProofApplication.Typed env U context :=
          ⟨.lam domain.val child.val,.forallE domain.val expected,.lamDF hd.down child.property⟩
        let firstCore ← translate first
        let firstType := VExpr.app (.const ``Option [.zero]) domain.val
        let hf ← checkWith env conversion U context firstCore.val firstType exposure
        let q ← args native (if ty == stateExpr then ``LoopFacts.bindState else ``LoopFacts.bindInt)
          [⟨firstCore.val,firstType,hf.down⟩,⟨pc,.forallE domain.val optionState,hp⟩,
           ⟨oc,.forallE domain.val optionStep,ho⟩,premise]
        let plain := Lean.mkAppN (bindHead ty stateExpr) #[first,.lam name ty next.plain binder]
        finish conversion exposure (.app (.app head first) (.lam name ty body binder)) plain q
      else none
    | .app (.app (.app (.app (.app (.const ``ite [.succ .zero]) resultTy) p) decision) yes) no =>
      let a ← compile native conversion exposure fuel yes
      let b ← compile native conversion exposure fuel no
      let pc ← translate p
      let dc ← translate decision
      let hp ← checkWith env conversion U context pc.val (.sort .zero) exposure
      let dt := VExpr.app (.const ``Decidable []) pc.val
      let hd ← checkWith env conversion U context dc.val dt exposure
      let q ← args native ``LoopFacts.branch
        [⟨pc.val,.sort .zero,hp.down⟩,⟨dc.val,dt,hd.down⟩,
         ⟨a.plainCore.val,optionState,a.plainTyped⟩,⟨b.plainCore.val,optionState,b.plainTyped⟩,
         ⟨a.sourceCore.val,optionStep,a.sourceTyped⟩,⟨b.sourceCore.val,optionStep,b.sourceTyped⟩,
         ⟨a.proof,_,a.correct⟩,⟨b.proof,_,b.correct⟩]
      let plain := Lean.mkAppN (.const ``ite [.succ .zero])
        #[.app optionExpr stateExpr,p,decision,a.plain,b.plain]
      finish conversion exposure (Lean.mkAppN (.const ``ite [.succ .zero]) #[resultTy,p,decision,yes,no]) plain q
    | _ => none

end IRComparison.LeanLoopNormalization
