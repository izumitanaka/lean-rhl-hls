import IRComparison.Core.BoundedReadIR
import IRComparison.Frontend.LeanArrayEntry

namespace IRComparison.LeanBoundedReadEntry
open Lean4Lean LeanTyped LeanIRQuotation LeanTypeInference
open LeanArrayEntry (arrayType)

def size (a : VExpr) : VExpr := applications (.const ``Array.size [.zero]) [intType,a]
def fin (a : VExpr) : VExpr := .app (.const ``Fin []) (size a)
def index (a i : VExpr) : VExpr := applications (.const ``Fin.val []) [size a,i]
def context : List VExpr := [fin (.bvar 0),arrayType]
def evaluator (functional : Bool) (a i : VExpr) : VExpr :=
  if functional then applications (.const ``BoundedReadIR.Functional.eval []) [.const ``BoundedReadIR.Functional.index [],a,index a i]
  else applications (.const ``BoundedReadIR.Imperative.eval []) [.const ``BoundedReadIR.Imperative.load [],a,index a i]
def specification (functional : Bool) (name : Lean.Name) : VExpr :=
  .forallE arrayType (.forallE (fin (.bvar 0))
    (eqResult (evaluator functional (.bvar 1) (.bvar 0))
      (someInt (applications (.const name []) [.bvar 1,.bvar 0]))))

def declarations : List Lean.Name :=
  [``Array, ``Array.size, ``Fin, ``Fin.val, ``GetElem,
   ``BoundedReadIR.Imperative, ``BoundedReadIR.Imperative.load, ``BoundedReadIR.Imperative.eval,
   ``BoundedReadIR.Functional, ``BoundedReadIR.Functional.index, ``BoundedReadIR.Functional.eval,
   ``BoundedReadIR.imperative_correct, ``BoundedReadIR.functional_correct]

structure Result (native : Lean.Environment) (name : Lean.Name) where
  library : LeanEntryEnvironment.Loaded native name
  imperativeProof : VExpr
  functionalProof : VExpr
  imperativeCorrect : library.model.HasType 0 [] imperativeProof (specification false name)
  functionalCorrect : library.model.HasType 0 [] functionalProof (specification true name)

/-- The exact imported read theorem is instantiated with the actual source
    bound proof. No unchecked removal of proof arguments or GetElem instances. -/
def compile (native : Lean.Environment) (name : Lean.Name) : Option (Result native name) := do
  let lib ← LeanEntryEnvironment.load native name declarations
  let .lam _ _ (.lam _ _ body _) _ := LeanSourceEntry.strip lib.source.declaration.value | none
  let .app _ boundProof := body | none
  let core ← translate body
  let bound ← translate boundProof
  let hb ← inferWith lib.model lib.conversion 0 context bound.val lib.exposure
  let ha ← check lib.model 0 context (.bvar 1) arrayType
  let hi ← checkWith lib.model lib.conversion 0 context (.bvar 0) (fin (.bvar 1)) lib.exposure
  let rules : List (LeanTypeReduction.Rule lib.model) := [⟨native,name,lib.source,lib.registered⟩]
  let original := applications (.const name []) [.bvar 1,.bvar 0]
  let reduced ← LeanTypeReduction.step rules lib.conversion 0 context lib.exposure original
  if same : reduced.val.1 = core.val then
    if resultType : reduced.val.2 = intType then
      have hname : lib.model.IsDefEq 0 context original core.val intType :=
        by simpa only [same,resultType] using reduced.property
      let one (functional : Bool) : Option {p // lib.model.HasType 0 [] p (specification functional name)} := do
        let fact ← LeanProofApplication.constant native lib.model 0 context
          (if functional then ``BoundedReadIR.functional_correct else ``BoundedReadIR.imperative_correct)
        let proof ← ([⟨.bvar 1,arrayType,ha.down⟩,⟨.bvar 0,fin (.bvar 1),hi.down⟩,
          ⟨bound.val,hb.val,hb.property⟩] : List (LeanProofApplication.Typed lib.model 0 context)).foldlM LeanProofApplication.apply fact
        let output := evaluator functional (.bvar 1) (.bvar 0)
        if shape : proof.type = eqResult output (someInt core.val) then
          let ht ← checkWith lib.model lib.conversion 0 context output optionInt lib.exposure
          let hs ← check lib.model 0 context LeanNamedScalar.someHead (.forallE intType optionInt)
          let hq ← check lib.model 0 context LeanNamedScalar.eqHead (.forallE optionInt (.forallE optionInt (.sort .zero)))
          let hat ← checkWith lib.model lib.conversion 0 [] arrayType (.sort (.succ .zero)) lib.exposure
          let hft ← checkWith lib.model lib.conversion 0 [arrayType] (fin (.bvar 0)) (.sort (.succ .zero)) lib.exposure
          have converted := VEnv.IsDefEq.defeq
            (LeanNamedScalar.result_congr hs.down hq.down ht.down hname).symm (shape ▸ proof.correct)
          return ⟨.lam arrayType (.lam (fin (.bvar 0)) proof.term),.lamDF hat.down (.lamDF hft.down converted)⟩
        else none
      let pi ← one false
      let pf ← one true
      return ⟨lib,pi.val,pf.val,pi.property,pf.property⟩
    else none
  else none

end IRComparison.LeanBoundedReadEntry
