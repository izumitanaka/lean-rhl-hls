import IRComparison.Frontend.LeanNamedBody
import IRComparison.Core.BodyBackends

namespace IRComparison.LeanBodyPipeline
open Lean4Lean LeanTyped LeanIREvaluation LeanBodyQuotation LeanTypeInference

inductive Backend where
  | imperative | functional

def Backend.program : Backend → Lean.Name
  | .imperative => ``BodyBackends.imperative
  | .functional => ``BodyBackends.functional

def Backend.evaluator : Backend → Lean.Name
  | .imperative => ``Imperative.Program.eval
  | .functional => ``Functional.Program.eval

def Backend.fact : Backend → Lean.Name
  | .imperative => ``BodyBackends.imperative_correct
  | .functional => ``BodyBackends.functional_correct

def specification (backend : Backend) (name : Lean.Name) (bodyCode : VExpr) : VExpr :=
  let parameters := [.bvar 6,.bvar 5,.bvar 4,.bvar 3,.bvar 2]
  let program := applications (.const backend.program []) (bodyCode :: parameters)
  let result := applications (.const backend.evaluator []) [.bvar 1,program,.bvar 0]
  let source := applications (.const ``BodyBackends.runSource [])
    ((.const name []) :: parameters ++ [.bvar 1,.bvar 0])
  [intType,intType,(.const ``Nat []),intType,intType,(.const ``Input []),stateType].foldr
    VExpr.forallE (eqState result source)

structure Proof (env : VEnv) (backend : Backend) (name : Lean.Name) (bodyCode : VExpr) where
  term : VExpr
  correct : env.HasType 0 [] term (specification backend name bodyCode)

structure Result (native : Lean.Environment) (name : Lean.Name) where
  source : LeanNamedBody.Result native name
  imperativeProof : Proof source.library.model .imperative name (imperativeCode source.body.imperative)
  functionalProof : Proof source.library.model .functional name (functionalCode source.body.functional)

private def specialize (native : Lean.Environment) (env : VEnv) (name : Lean.Name) (backend : Backend)
    (bodyCode bodyType : VExpr) (premise : LeanProofApplication.Typed env 0 []) :
    Option (Proof env backend name bodyCode) := do
  let f ← LeanProofApplication.constant native env 0 [] backend.fact
  let hc ← check env 0 [] bodyCode bodyType
  let hs ← check env 0 [] (.const name []) LeanNamedBody.bodyType
  let a ← LeanProofApplication.apply f ⟨bodyCode,bodyType,hc.down⟩
  let b ← LeanProofApplication.apply a ⟨.const name [],LeanNamedBody.bodyType,hs.down⟩
  let c ← LeanProofApplication.apply b premise
  if same : c.type = specification backend name bodyCode then
    return ⟨c.term,same ▸ c.correct⟩
  else none

def compile (native : Lean.Environment) (name : Lean.Name) (fuel : Nat := 32) :
    Option (Result native name) := do
  let source ← LeanNamedBody.compile native name
    [``BodyBackends.imperative_correct,``BodyBackends.functional_correct] fuel
  let model := source.library.model
  if hi : model.constants ``Int = some ⟨0,.sort (.succ .zero)⟩ then
    if hs : model.constants ``State = some ⟨0,.sort (.succ .zero)⟩ then
      let ti := imperativeEval (imperativeCode source.body.imperative) (.bvar 3) (.bvar 2) (.bvar 1) (.bvar 0)
      let tf := functionalEval (functionalCode source.body.functional) (.bvar 3) (.bvar 2) (.bvar 1) (.bvar 0)
      have pi : model.HasType 0 LeanNamedBody.context source.imperativeProof
          (eqState ti (applications (.const name []) [.bvar 3,.bvar 2,.bvar 1,.bvar 0])) := by
        obtain ⟨ci,cx,cy,cs,cl⟩ := source.canonical
        simpa only [ci,cx,cy,cs,cl] using source.imperativeCorrect
      have pf : model.HasType 0 LeanNamedBody.context source.functionalProof
          (eqState tf (applications (.const name []) [.bvar 3,.bvar 2,.bvar 1,.bvar 0])) := by
        obtain ⟨ci,cx,cy,cs,cl⟩ := source.canonical
        simpa only [ci,cx,cy,cs,cl] using source.functionalCorrect
      let premiseI : LeanProofApplication.Typed model 0 [] :=
        ⟨LeanNamedBody.close source.imperativeProof,LeanNamedBody.specification name ti,
          LeanNamedBody.close_correct hi hs pi⟩
      let premiseF : LeanProofApplication.Typed model 0 [] :=
        ⟨LeanNamedBody.close source.functionalProof,LeanNamedBody.specification name tf,
          LeanNamedBody.close_correct hi hs pf⟩
      let pi ← specialize native model name .imperative (imperativeCode source.body.imperative)
        (.const ``Imperative.Cmd []) premiseI
      let pf ← specialize native model name .functional (functionalCode source.body.functional)
        (.const ``Functional.Term []) premiseF
      return ⟨source,pi,pf⟩
    else none
  else none

theorem Result.correct (r : Result native name) :
    LeanEnvironmentProvenance.Faithful native r.source.library.model ∧
    r.source.library.model.HasType 0 [] r.imperativeProof.term
      (specification .imperative name (imperativeCode r.source.body.imperative)) ∧
    r.source.library.model.HasType 0 [] r.functionalProof.term
      (specification .functional name (functionalCode r.source.body.functional)) :=
  ⟨r.source.library.faithful,r.imperativeProof.correct,r.functionalProof.correct⟩

end IRComparison.LeanBodyPipeline
