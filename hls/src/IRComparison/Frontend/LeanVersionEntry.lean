import IRComparison.Frontend.LeanVersionBody

namespace IRComparison.LeanVersionEntry
open Lean4Lean LeanTyped LeanIRQuotation LeanIREvaluation LeanBodyQuotation LeanTypeInference

def declarations : List Lean.Name := LeanNamedBody.declarations ++
  [``Functional.Term.forRangeCaptured,``VersionFacts.capturedLoop,``Functional.Term.bindResult,``VersionFacts.lookupZero,``VersionFacts.lookupSucc,
   ``VersionFacts.yieldSome,``VersionFacts.yieldPure,``VersionFacts.store,``VersionFacts.storeLiteral,
   ``VersionFacts.bind,``VersionFacts.capture,``VersionFacts.branch]

structure Result (native : Lean.Environment) (name : Lean.Name) where
  library : LeanEntryEnvironment.Loaded native name
  emitted : Functional.Term
  proof : VExpr
  correct : library.model.HasType 0 [] proof
    (LeanNamedBody.specification name
      (functionalEval (functionalCode emitted) (.bvar 3) (.bvar 2) (.bvar 1) (.bvar 0)))

def compile (native : Lean.Environment) (name : Lean.Name) : Option (Result native name) := do
  let lib ← LeanEntryEnvironment.load native name declarations
  let .lam _ (.const ``Int []) (.lam _ (.const ``Int []) (.lam _ (.const ``Int [])
      (.lam _ (.const ``State []) body _) _) _) _ := LeanSourceEntry.strip lib.source.declaration.value | none
  let ⟨inputs,canonical⟩ ← LeanNamedBody.parameters lib.model
  let a ← LeanVersionBody.compile native inputs [inputs.state] lib.conversion lib.exposure 128 body
  let original := applications (.const name []) [inputs.i,inputs.x,inputs.y,inputs.state]
  let rules : List (LeanTypeReduction.Rule lib.model) := [⟨native,name,lib.source,lib.registered⟩]
  let reduced ← LeanTypeReduction.step rules lib.conversion 0 LeanNamedBody.context lib.exposure original
  if same : reduced.val.1 = a.sourceCore.val then
    if resultType : reduced.val.2 = optionState then
      let heq ← check lib.model 0 LeanNamedBody.context eqHead (.forallE optionState (.forallE optionState (.sort .zero)))
      let ht ← checkWith lib.model lib.conversion 0 LeanNamedBody.context
        (LeanVersionBody.evaluate a.emitted inputs [inputs.state]) optionState lib.exposure
      have hname : lib.model.IsDefEq 0 LeanNamedBody.context original a.sourceCore.val optionState := by
        simpa only [same,resultType] using reduced.property
      have connected := VEnv.IsDefEq.defeq (result_congr heq.down ht.down hname).symm a.correct
      if hi : lib.model.constants ``Int = some ⟨0,.sort (.succ .zero)⟩ then
        if hs : lib.model.constants ``State = some ⟨0,.sort (.succ .zero)⟩ then
          have canonicalProof : lib.model.HasType 0 LeanNamedBody.context a.proof
              (eqState (functionalEval (functionalCode a.emitted) (.bvar 3) (.bvar 2) (.bvar 1) (.bvar 0))
                (applications (.const name []) [.bvar 3,.bvar 2,.bvar 1,.bvar 0])) := by
            obtain ⟨ci,cx,cy,cs,cl⟩ := canonical
            simpa only [LeanVersionBody.evaluate,LeanVersionBody.statesCode,List.foldr,
              original,functionalEval,ci,cx,cy,cs,cl] using connected
          return ⟨lib,a.emitted,LeanNamedBody.close a.proof,LeanNamedBody.close_correct hi hs canonicalProof⟩
        else none
      else none
    else none
  else none

end IRComparison.LeanVersionEntry
