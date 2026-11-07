import IRComparison.Frontend.LeanSourceBody
import IRComparison.Frontend.LeanEntryEnvironment

namespace IRComparison.LeanNamedBody
open Lean4Lean LeanTyped LeanIRQuotation LeanIREvaluation LeanBodyQuotation LeanTypeInference

variable {env : VEnv} {U : Nat} {ctx : List VExpr}

def context : List VExpr := [stateType,intType,intType,intType]
def bodyType : VExpr := .forallE intType (.forallE intType (.forallE intType (.forallE stateType optionState)))
def Canonical (inputs : LeanIREvaluationCompiler.Inputs env 0 context) : Prop :=
  inputs.i = .bvar 3 ∧ inputs.x = .bvar 2 ∧ inputs.y = .bvar 1 ∧ inputs.state = .bvar 0 ∧ inputs.locals = nilInts

def parameters (env : VEnv) : Option {inputs : LeanIREvaluationCompiler.Inputs env 0 context // Canonical inputs} := do
  let hi ← check env 0 context (.bvar 3) intType
  let hx ← check env 0 context (.bvar 2) intType
  let hy ← check env 0 context (.bvar 1) intType
  let hs ← check env 0 context (.bvar 0) stateType
  return ⟨⟨.bvar 3,.bvar 2,.bvar 1,.bvar 0,hi.down,hx.down,hy.down,hs.down,nilInts⟩,rfl,rfl,rfl,rfl,rfl⟩

structure Result (native : Lean.Environment) (name : Lean.Name) where
  library : LeanEntryEnvironment.Loaded native name
  inputs : LeanIREvaluationCompiler.Inputs library.model 0 context
  canonical : Canonical inputs
  bodySource : Lean.Expr
  body : LeanSourceBody.Artifact inputs bodySource
  imperativeProof : VExpr
  functionalProof : VExpr
  imperativeCorrect : library.model.HasType 0 context imperativeProof
    (eqState (imperativeEval (imperativeCode body.imperative) inputs.i inputs.x inputs.y inputs.state inputs.locals)
      (applications (.const name []) [inputs.i,inputs.x,inputs.y,inputs.state]))
  functionalCorrect : library.model.HasType 0 context functionalProof
    (eqState (functionalEval (functionalCode body.functional) inputs.i inputs.x inputs.y inputs.state inputs.locals)
      (applications (.const name []) [inputs.i,inputs.x,inputs.y,inputs.state]))

def declarations : List Lean.Name :=
  LeanLoopNormalization.declarations ++
  [``ReadFacts.natural, ``ReadFacts.naturalA, ``ReadHoistingFacts.commute, ``ReadHoistingFacts.transport, ``Imperative.Cmd.forRange, ``Functional.Term.forRange, ``Nat.cast, ``instNatCastInt,
    ``ForIn, ``ForIn', ``Membership, ``ReadFacts.literal, ``ReadFacts.literalA, ``ReadFacts.literalN, ``ReadFacts.literalAN,
    ``ReadFacts.dynamic, ``ReadFacts.dynamicA, ``IRComparison.Expr.read,
    ``BodyFacts.letImperative, ``BodyFacts.letFunctional,
    ``Imperative.Cmd.letValue, ``Functional.Term.letValue, ``BodyFacts.skipImperative, ``BodyFacts.skipFunctional, ``BodyFacts.returnImperative,
    ``BodyFacts.returnFunctional, ``Imperative.Cmd.skip, ``BodyFacts.seqImperative, ``BodyFacts.seqFunctional,
    ``Imperative.Cmd.seq, ``Functional.Term.letResult, ``State.write, ``BodyFacts.branchImperative, ``BodyFacts.branchFunctional,
    ``Imperative.Cmd.branch, ``Functional.Term.branch, ``BodyFacts.storeImperative, ``BodyFacts.storeFunctional,
    ``BodyFacts.storeImperativeLiteral, ``BodyFacts.storeFunctionalLiteral,
    ``Imperative.Cmd, ``Imperative.Cmd.store, ``Imperative.Cmd.eval,
    ``Functional.Term, ``Functional.Term.letWrite, ``Functional.Term.yield, ``Functional.Term.eval,
    ``List, ``List.cons, ``List.nil, ``Nat, ``OfNat.ofNat, ``instOfNatNat]

def compile (native : Lean.Environment) (name : Lean.Name) (extra : List Lean.Name := []) (fuel : Nat := 32) :
    Option (Result native name) := do
  let library ← LeanEntryEnvironment.load native name (declarations ++ extra)
  let source := LeanSourceEntry.strip library.source.declaration.value
  let bodySource ← match source with
    | .lam _ (.const ``Int []) (.lam _ (.const ``Int []) (.lam _ (.const ``Int [])
        (.lam _ (.const ``State []) body _) _) _) _ => some body
    | _ => none
  let ⟨inputs,canonical⟩ ← parameters library.model
  let body ← LeanSourceBody.compile native inputs library.conversion library.exposure fuel bodySource
  let sourceApplication := applications (.const name []) [inputs.i,inputs.x,inputs.y,inputs.state]
  let rules : List (LeanTypeReduction.Rule library.model) :=
    [⟨native,name,library.source,library.registered⟩]
  let reduced ← LeanTypeReduction.step rules library.conversion 0 context library.exposure sourceApplication
  if same : reduced.val.1 = body.sourceCore.val then
    if typeSame : reduced.val.2 = optionState then
      let eqTyped ← check library.model 0 context eqHead (.forallE optionState (.forallE optionState (.sort .zero)))
      let hi ← checkWith library.model library.conversion 0 context
        (imperativeEval (imperativeCode body.imperative) inputs.i inputs.x inputs.y inputs.state inputs.locals) optionState library.exposure
      let hf ← checkWith library.model library.conversion 0 context
        (functionalEval (functionalCode body.functional) inputs.i inputs.x inputs.y inputs.state inputs.locals) optionState library.exposure
      have sourceEq : library.model.IsDefEq 0 context sourceApplication body.sourceCore.val optionState :=
        by simpa only [same,typeSame] using reduced.property
      return ⟨library,inputs,canonical,bodySource,body,body.imperativeProof,body.functionalProof,
        .defeq (result_congr eqTyped.down hi.down sourceEq).symm body.imperativeCorrect,
        .defeq (result_congr eqTyped.down hf.down sourceEq).symm body.functionalCorrect⟩
    else none
  else none

def specification (name : Lean.Name) (result : VExpr) : VExpr :=
  .forallE intType (.forallE intType (.forallE intType (.forallE stateType
    (eqState result (applications (.const name []) [.bvar 3,.bvar 2,.bvar 1,.bvar 0])))))

def close (proof : VExpr) : VExpr := intLambdas 3 (.lam stateType proof)

theorem close_correct (intDeclared : env.constants ``Int = some ⟨0,.sort (.succ .zero)⟩)
    (stateDeclared : env.constants ``State = some ⟨0,.sort (.succ .zero)⟩)
    (h : env.HasType 0 context proof (eqState result
      (applications (.const name []) [.bvar 3,.bvar 2,.bvar 1,.bvar 0]))) :
    env.HasType 0 [] (close proof) (specification name result) := by
  have stateTyped : env.HasType 0 [intType,intType,intType] stateType (.sort (.succ .zero)) :=
    .constDF stateDeclared (by simp) (by simp) rfl .nil
  exact .lamDF (int_hasType intDeclared _) (.lamDF (int_hasType intDeclared _)
    (.lamDF (int_hasType intDeclared _) (.lamDF stateTyped h)))

end IRComparison.LeanNamedBody
