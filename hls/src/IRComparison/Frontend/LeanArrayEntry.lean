import IRComparison.Core.ArrayIR
import IRComparison.Frontend.LeanArrayNormalization
import IRComparison.Frontend.LeanNamedScalar
import IRComparison.Frontend.LeanProofApplication

namespace IRComparison.LeanArrayEntry
open Lean4Lean LeanTyped LeanIRQuotation LeanTypeInference

@[reducible] def arrayType : VExpr := .app (.const ``Array [.zero]) intType
@[reducible] def optionArray : VExpr := .app (.const ``Option [.zero]) arrayType
@[reducible] def someArrayHead : VExpr := .app (.const ``Option.some [.zero]) arrayType
@[reducible] def arrayEqHead : VExpr := .app (.const ``Eq [.succ .zero]) optionArray
def resultEq (a b : VExpr) : VExpr := .app (.app arrayEqHead a) (.app someArrayHead b)

def evaluator (functional : Bool) (e a : VExpr) : VExpr :=
  if functional then applications (.const ``ArrayIR.Functional.eval [])
    [.app (.const ``ArrayIR.Functional.map []) e,a]
  else applications (.const ``ArrayIR.Imperative.eval [])
    [.app (.const ``ArrayIR.Imperative.generate []) e,a]

variable {env : VEnv} {U : Nat} {ctx : List VExpr}

theorem result_congr (hs : env.HasType U ctx someArrayHead (.forallE arrayType optionArray))
    (he : env.HasType U ctx arrayEqHead (.forallE optionArray (.forallE optionArray (.sort .zero))))
    (ht : env.HasType U ctx target optionArray)
    (h : env.IsDefEq U ctx source body arrayType) :
    env.IsDefEq U ctx (resultEq target source) (resultEq target body) (.sort .zero) := by
  have someEq := VEnv.IsDefEq.appDF hs h
  simp only [optionArray, arrayType, VExpr.inst, List.map_cons, List.map_nil] at someEq
  have eqHead := VEnv.IsDefEq.appDF he ht
  simp only [optionArray, arrayType, VExpr.inst, List.map_cons, List.map_nil] at eqHead
  exact VEnv.IsDefEq.appDF eqHead someEq

def parameters (env : VEnv) : Option (LeanIREvaluationCompiler.Inputs env 0 [intType,arrayType]) := do
  let hz ← check env 0 [intType,arrayType] (integer 0) intType
  let hv ← check env 0 [intType,arrayType] (.bvar 0) intType
  let hs ← check env 0 [intType,arrayType] (.const ``ArrayIR.emptyState []) (.const ``State [])
  return ⟨integer 0,.bvar 0,integer 0,.const ``ArrayIR.emptyState [],hz.down,hv.down,hz.down,hs.down,nilInts⟩

def declarations : List Lean.Name :=
  [``ArrayNormalizationFacts.identity, ``ArrayNormalizationFacts.fuse, ``ArrayNormalizationFacts.result, ``Array, ``Array.map, ``ArrayIR.emptyState,
   ``ArrayIR.Imperative, ``ArrayIR.Imperative.generate, ``ArrayIR.Imperative.eval,
   ``ArrayIR.Functional, ``ArrayIR.Functional.map, ``ArrayIR.Functional.eval,
   ``ArrayIR.imperative_correct, ``ArrayIR.functional_correct]

def specification (functional : Bool) (name : Lean.Name) (e : Expr) : VExpr :=
  .forallE arrayType (resultEq (evaluator functional (code e) (.bvar 0)) (.app (.const name []) (.bvar 0)))

structure Result (native : Lean.Environment) (name : Lean.Name) where
  library : LeanEntryEnvironment.Loaded native name
  emitted : Expr
  imperativeProof : VExpr
  functionalProof : VExpr
  imperativeCorrect : library.model.HasType 0 [] imperativeProof (specification false name emitted)
  functionalCorrect : library.model.HasType 0 [] functionalProof (specification true name emitted)

/-- The same ordinary Array.map source is connected independently to the
    sequential generator and functional mapping semantics. -/
def compile (native : Lean.Environment) (name : Lean.Name) (fuel : Nat := 64) : Option (Result native name) := do
  let lib ← LeanEntryEnvironment.load native name declarations
  let .lam _ (.app (.const ``Array [.zero]) (.const ``Int [])) source _ :=
    LeanSourceEntry.strip lib.source.declaration.value | none
  let normalized ← LeanArrayNormalization.compile (context := [arrayType]) native (.bvar 0)
    lib.conversion lib.exposure fuel source
  let .lam _ (.const ``Int []) body _ := normalized.mapper | none
  let inputs ← parameters lib.model
  let parsed ← LeanSourceToIR.compile native inputs lib.conversion lib.exposure fuel body
  let bridge ← LeanIRTransport.connect native inputs lib.conversion lib.exposure
    parsed.sourceCore parsed.sourceTyped parsed.target parsed.sourceProof parsed.sourceEquality
  let f := VExpr.lam intType parsed.sourceCore.val
  let applied := VExpr.app (f.liftN 1) (.bvar 0)
  let reduced ← LeanTypeReduction.step [] lib.conversion 0 [intType,arrayType] lib.exposure applied
  if bodySame : reduced.val.1 = bridge.sourceCore.val then
    if bodyType : reduced.val.2 = intType then
      let someTyped ← check lib.model 0 [intType,arrayType] LeanNamedScalar.someHead (.forallE intType optionInt)
      let eqTyped ← check lib.model 0 [intType,arrayType] LeanNamedScalar.eqHead
        (.forallE optionInt (.forallE optionInt (.sort .zero)))
      let target := eval (code parsed.emitted) inputs.i inputs.x inputs.y inputs.state inputs.locals
      let targetTyped ← checkWith lib.model lib.conversion 0 [intType,arrayType] target optionInt lib.exposure
      have hb : lib.model.IsDefEq 0 [intType,arrayType] applied bridge.sourceCore.val intType :=
        by simpa only [bodySame,bodyType] using reduced.property
      have converted := VEnv.IsDefEq.defeq
        (LeanNamedScalar.result_congr someTyped.down eqTyped.down targetTyped.down hb).symm bridge.correct
      let intTyped ← check lib.model 0 [arrayType] intType (.sort (.succ .zero))
      let premise : LeanProofApplication.Typed lib.model 0 [arrayType] :=
        ⟨.lam intType bridge.proof,.forallE intType (eqResult target (someInt applied)),.lamDF intTyped.down converted⟩
      let he ← check lib.model 0 [arrayType] (code parsed.emitted) (.const ``Expr [])
      let hf ← checkWith lib.model lib.conversion 0 [arrayType] f (.forallE intType intType) lib.exposure
      let ha ← check lib.model 0 [arrayType] (.bvar 0) arrayType
      let sourceCore ← translate source
      let sourceApplication := VExpr.app (.const name []) (.bvar 0)
      let rules : List (LeanTypeReduction.Rule lib.model) := [⟨native,name,lib.source,lib.registered⟩]
      let named ← LeanTypeReduction.step rules lib.conversion 0 [arrayType] lib.exposure sourceApplication
      if namedSame : named.val.1 = sourceCore.val then
        if namedType : named.val.2 = arrayType then
          have hname : lib.model.IsDefEq 0 [arrayType] sourceApplication sourceCore.val arrayType :=
            by simpa only [namedSame,namedType] using named.property
          let one (functional : Bool) : Option {p // lib.model.HasType 0 [] p (specification functional name parsed.emitted)} := do
            let fact ← LeanProofApplication.constant native lib.model 0 [arrayType]
              (if functional then ``ArrayIR.functional_correct else ``ArrayIR.imperative_correct)
            let proof ← ([⟨code parsed.emitted,.const ``Expr [],he.down⟩,
              ⟨f,.forallE intType intType,hf.down⟩,⟨.bvar 0,arrayType,ha.down⟩,premise] :
              List (LeanProofApplication.Typed lib.model 0 [arrayType])).foldlM LeanProofApplication.apply fact
            let output := evaluator functional (code parsed.emitted) (.bvar 0)
            let normal := LeanArrayNormalization.mapped normalized.mapperCore.val (.bvar 0)
            let hm ← checkWith lib.model lib.conversion 0 [arrayType] normal arrayType lib.exposure
            let ho ← checkWith lib.model lib.conversion 0 [arrayType] output optionArray lib.exposure
            let hp ← LeanLoopNormalization.cast lib.conversion proof (resultEq output normal)
            let proof ← LeanLoopNormalization.args native ``ArrayNormalizationFacts.result
              [⟨output,optionArray,ho.down⟩,⟨normal,arrayType,hm.down⟩,
               ⟨normalized.sourceCore.val,arrayType,normalized.sourceTyped⟩,
               ⟨hp.val,_,hp.property⟩,⟨normalized.proof,_,normalized.correct⟩]
            if shape : proof.type = resultEq output sourceCore.val then
              let ho ← checkWith lib.model lib.conversion 0 [arrayType] output optionArray lib.exposure
              let hs ← check lib.model 0 [arrayType] someArrayHead (.forallE arrayType optionArray)
              let hq ← check lib.model 0 [arrayType] arrayEqHead (.forallE optionArray (.forallE optionArray (.sort .zero)))
              let hat ← checkWith lib.model lib.conversion 0 [] arrayType (.sort (.succ .zero)) lib.exposure
              have closed := VEnv.IsDefEq.lamDF hat.down
                (VEnv.IsDefEq.defeq (result_congr hs.down hq.down ho.down hname).symm (shape ▸ proof.correct))
              return ⟨.lam arrayType proof.term,closed⟩
            else none
          let pi ← one false
          let pf ← one true
          return ⟨lib,parsed.emitted,pi.val,pf.val,pi.property,pf.property⟩
        else none
      else none
    else none
  else none

end IRComparison.LeanArrayEntry
