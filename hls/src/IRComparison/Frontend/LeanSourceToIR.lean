import IRComparison.Frontend.LeanIRTransport
import IRComparison.Frontend.LeanSelectBridge

namespace IRComparison.LeanSourceToIR
open Lean4Lean LeanTyped LeanTypeInference LeanIRQuotation
variable {env : VEnv} {U : Nat} {context : List VExpr}

structure Artifact (inputs : LeanIREvaluationCompiler.Inputs env U context) (source : Lean.Expr) where
  emitted : Expr
  target : LeanIREvaluationCompiler.Artifact inputs emitted
  sourceCore : {v // Represents source v}
  sourceTyped : env.HasType U context sourceCore.val intType
  sourceProof : VExpr
  sourceEquality : env.HasType U context sourceProof (eqInt sourceCore.val target.value)

/-- Bind source variables to the supplied typed inputs, independently of where
    a surrounding state binder occurs in the Lean context. -/
def boundVariable (nativeEnv : Lean.Environment) (inputs : LeanIREvaluationCompiler.Inputs env U context)
    (n : Nat) : Option (Artifact inputs (.bvar n)) := do
  let _ ← loadFixedFact nativeEnv ``Standard.intRefl reflType
  if registered : env.constants ``Standard.intRefl = some ⟨0,reflType⟩ then
    for which in [LeanIREvaluation.Slot.index, .left, .right] do
      let target ← LeanIREvaluationCompiler.slot nativeEnv inputs which
      if same : target.value = .bvar n then
        return {
          emitted := LeanIREvaluationCompiler.slotExpr which, target := target
          sourceCore := ⟨.bvar n,.bvar⟩
          sourceTyped := by simpa only [same] using target.valueTyped
          sourceProof := .app (.const ``Standard.intRefl []) target.value
          sourceEquality := by simpa only [same] using apply_refl registered target.valueTyped }
    for localIndex in List.range (LeanIREvaluationCompiler.localCount inputs.locals) do
      let target ← LeanIREvaluationCompiler.localAt nativeEnv inputs localIndex
      if same : target.value = .bvar n then
        return {
          emitted := .local localIndex, target := target
          sourceCore := ⟨.bvar n,.bvar⟩
          sourceTyped := by simpa only [same] using target.valueTyped
          sourceProof := .app (.const ``Standard.intRefl []) target.value
          sourceEquality := by simpa only [same] using apply_refl registered target.valueTyped }
    none
  else none

/-- Bound scalar values may be coercions of a loop index rather than bvars. -/
def knownValue (nativeEnv : Lean.Environment) (inputs : LeanIREvaluationCompiler.Inputs env U context)
    (source : Lean.Expr) : Option (Artifact inputs source) := do
  let core ← translate source
  if registered : env.constants ``Standard.intRefl = some ⟨0,reflType⟩ then
    for n in List.range (LeanIREvaluationCompiler.localCount inputs.locals) do
      let target ← LeanIREvaluationCompiler.localAt nativeEnv inputs n
      if same : core.val = target.value then
        return ⟨.local n,target,core,same ▸ target.valueTyped,
          .app (.const ``Standard.intRefl []) target.value,
          by simpa only [same] using apply_refl registered target.valueTyped⟩
    none
  else none

def normalized (nativeEnv : Lean.Environment) (inputs : LeanIREvaluationCompiler.Inputs env U context)
    (conversion : Conversion env) (exposure : Exposure env) (source : Lean.Expr) :
    Option (Artifact inputs source) := do
  let original ← LeanLetNormalization.leading nativeEnv env U context conversion exposure 32 source
  let parsed ← LeanScalar.compile LeanScalar.initialLayout original.expression
  let target ← LeanIREvaluationCompiler.compile nativeEnv inputs parsed.code.expr
  if same : original.targetCore.val = target.value then
    return ⟨parsed.code.expr,target,original.sourceCore,original.sourceTyped,original.proof,
      same ▸ original.correct⟩
  else none

def branch (nativeEnv : Lean.Environment) (inputs : LeanIREvaluationCompiler.Inputs env U context)
    (conversion : Conversion env) (exposure : Exposure env)
    (c : Artifact inputs test) (a : Artifact inputs yes) (b : Artifact inputs no)
    (decision : Lean.Expr) :
    Option (Artifact inputs (NativeRHL.ExprAnalysis.conditional test decision yes no)) := do
  let _ ← loadFixedFact nativeEnv ``LeanSelectBridge.fact LeanSelectBridge.signature
  if registered : env.constants ``LeanSelectBridge.fact = some ⟨0,LeanSelectBridge.signature⟩ then
    let d ← translate decision
    let hd ← checkWith env conversion U context d.val (LeanSelectBridge.decisionType c.sourceCore.val) exposure
    let source := LeanSelectBridge.source c.sourceCore.val d.val a.sourceCore.val b.sourceCore.val
    let hs ← checkWith env conversion U context source intType exposure
    let target ← LeanIREvaluationCompiler.select nativeEnv inputs c.target a.target b.target
    if same : target.value = LeanSelectBridge.target c.target.value a.target.value b.target.value then
      return {
        emitted := .select c.emitted a.emitted b.emitted, target := target
        sourceCore := ⟨source,LeanSelectBridge.represents c.sourceCore.property d.property a.sourceCore.property b.sourceCore.property⟩
        sourceTyped := hs.down
        sourceProof := applications (.const ``LeanSelectBridge.fact [])
          [c.sourceCore.val,c.target.value,a.sourceCore.val,a.target.value,b.sourceCore.val,b.target.value,
            d.val,c.sourceProof,a.sourceProof,b.sourceProof]
        sourceEquality := by
          simpa only [same] using LeanSelectBridge.apply_fact registered
            c.sourceTyped c.target.valueTyped a.sourceTyped a.target.valueTyped
            b.sourceTyped b.target.valueTyped hd.down c.sourceEquality a.sourceEquality b.sourceEquality }
    else none
  else none

def letValue (inputs : LeanIREvaluationCompiler.Inputs env U context)
    (conversion : Conversion env) (exposure : Exposure env)
    (value body : Lean.Expr) (next : Artifact inputs (LeanBindings.instantiate value body)) :
    Option (Artifact inputs (.letE name (.const ``Int []) value body flag)) := do
  let v ← translate value
  let b ← translate body
  let hv ← checkWith env conversion U context v.val intType exposure
  let hb ← checkWith env conversion U (intType :: context) b.val intType exposure
  if heq : env.constants ``Eq = some ⟨1,LeanLetNormalization.equalityType⟩ then
    if hint : env.constants ``Int = some ⟨0,.sort (.succ .zero)⟩ then
      let same := (b.property.instantiate v.property).unique next.sourceCore.property
      return {
        emitted := next.emitted, target := next.target
        sourceCore := ⟨.app (.lam intType b.val) v.val,.letE (.constant rfl) v.property b.property⟩
        sourceTyped := .app (.lam (int_hasType hint context) hb.down) hv.down
        sourceProof := next.sourceProof
        sourceEquality := LeanLetNormalization.let_proof heq hint hb.down hv.down next.target.valueTyped
          (by simpa only [same] using next.sourceEquality) }
    else none
  else none

/-- Reuse a scalar proof through a typed beta/let computation at any binder
    type, including locally defined functions. No source-specific equality
    certificate is assumed. -/
def beta (inputs : LeanIREvaluationCompiler.Inputs env U context)
    (conversion : Conversion env) (exposure : Exposure env) (source : Lean.Expr)
    (next : Artifact inputs nextSource) : Option (Artifact inputs source) := do
  let core ← translate source
  let reduced ← LeanTypeReduction.step [] conversion U context exposure core.val
  if same : reduced.val.1 = next.sourceCore.val then
    if resultType : reduced.val.2 = intType then
      let hs ← checkWith env conversion U context core.val intType exposure
      if heq : env.constants ``Eq = some ⟨1,LeanLetNormalization.equalityType⟩ then
        if hint : env.constants ``Int = some ⟨0,.sort (.succ .zero)⟩ then
          have h : env.IsDefEq U context core.val next.sourceCore.val intType :=
            by simpa only [same,resultType] using reduced.property
          return { next with
            sourceCore := core, sourceTyped := hs.down
            sourceEquality := .defeq
              (LeanLetNormalization.equality_congr heq hint h.symm next.target.valueTyped)
              next.sourceEquality }
        else none
      else none
    else none
  else none

def binary (nativeEnv : Lean.Environment) (inputs : LeanIREvaluationCompiler.Inputs env U context)
    (conversion : Conversion env) (exposure : Exposure env) (op : LeanScalar.Op)
    (surface : Bool) (head : Lean.Expr)
    (headMatches : head = if surface then op.surfaceHead else .const op.primitive [])
    (a : Artifact inputs left) (b : Artifact inputs right) :
    Option (Artifact inputs (.app (.app head left) right)) := do
  let h ← translate head
  let source := VExpr.app (.app h.val a.sourceCore.val) b.sourceCore.val
  let hs ← checkWith env conversion U context source intType exposure
  let hp ← checkWith env conversion U context (.const op.primitive []) (intArrows 2) exposure
  let target ← LeanIREvaluationCompiler.binary nativeEnv inputs op a.target b.target
  if same : target.value = .app (.app (.const op.primitive []) a.target.value) b.target.value then
    if hc : env.constants ``Standard.intCongr = some ⟨0,congrType⟩ then
      if isSurface : surface then
        let fact ← LeanArithmetic.loadOperator nativeEnv op
        if hf : env.constants (LeanArithmetic.factName op) = some fact.view.signature then
          if ht : env.constants ``Standard.intTrans = some ⟨0,transType⟩ then
            let headEq : h.val = fact.view.leftCore.val := by
              apply Represents.unique h.property
              simpa [headMatches, isSurface] using fact.left_represents
            return {
              emitted := LeanIREvaluationCompiler.binaryExpr op a.emitted b.emitted, target := target
              sourceCore := ⟨source,.app (.app h.property a.sourceCore.property) b.sourceCore.property⟩
              sourceTyped := hs.down
              sourceProof := composeBinary source (.const op.primitive []) a.sourceCore.val b.sourceCore.val
                a.target.value b.target.value
                (.app (.app (.const (LeanArithmetic.factName op) []) a.sourceCore.val) b.sourceCore.val)
                a.sourceProof b.sourceProof
              sourceEquality := by
                rw [same]
                apply composeBinary_correct ht hc hs.down hp.down a.sourceTyped b.sourceTyped
                  a.target.valueTyped b.target.valueTyped
                · simpa only [source, headEq] using fact.apply hf a.sourceTyped b.sourceTyped
                · exact a.sourceEquality
                · exact b.sourceEquality }
          else none
        else none
      else
        let headEq : h.val = .const op.primitive [] := by
          apply Represents.unique h.property
          simpa [headMatches, isSurface] using (Represents.constant (name := op.primitive) (us := []) rfl)
        return {
          emitted := LeanIREvaluationCompiler.binaryExpr op a.emitted b.emitted, target := target
          sourceCore := ⟨source,.app (.app h.property a.sourceCore.property) b.sourceCore.property⟩
          sourceTyped := hs.down
          sourceProof := applications (.const ``Standard.intCongr [])
            [.const op.primitive [],a.sourceCore.val,a.target.value,b.sourceCore.val,b.target.value,a.sourceProof,b.sourceProof]
          sourceEquality := by
            simpa only [same, source, headEq] using apply_congr hc hp.down
              a.sourceTyped a.target.valueTyped b.sourceTyped b.target.valueTyped a.sourceEquality b.sourceEquality }
    else none
  else none

def negative (nativeEnv : Lean.Environment) (inputs : LeanIREvaluationCompiler.Inputs env U context)
    (conversion : Conversion env) (exposure : Exposure env) (flavor : LeanNegNormalization.Flavor)
    (body : Artifact inputs arg) : Option (Artifact inputs (.app flavor.head arg)) := do
  let _ ← loadFixedFact nativeEnv flavor.fact flavor.signature
  if registered : env.constants flavor.fact = some ⟨0,flavor.signature⟩ then
    let source := VExpr.app flavor.coreHead body.sourceCore.val
    let hs ← checkWith env conversion U context source intType exposure
    let zero ← LeanIREvaluationCompiler.literal nativeEnv inputs 0
    let target ← LeanIREvaluationCompiler.binary nativeEnv inputs .sub zero body.target
    if same : target.value = LeanNegNormalization.target body.target.value then
      return {
        emitted := .sub (.lit 0) body.emitted, target := target
        sourceCore := ⟨source,.app flavor.represents body.sourceCore.property⟩
        sourceTyped := hs.down
        sourceProof := applications (.const flavor.fact []) [body.sourceCore.val,body.target.value,body.sourceProof]
        sourceEquality := by
          simpa only [same] using LeanNegNormalization.apply_neg flavor registered
            body.sourceTyped body.target.valueTyped body.sourceEquality }
    else none
  else none

def primitiveHead : (head : Lean.Expr) → Option {op : LeanScalar.Op // head = .const op.primitive []}
  | .const ``Int.add [] => some ⟨.add,rfl⟩
  | .const ``Int.sub [] => some ⟨.sub,rfl⟩
  | .const ``Int.mul [] => some ⟨.mul,rfl⟩
  | .const ``Int.ediv [] => some ⟨.div,rfl⟩
  | _ => none

def compile (nativeEnv : Lean.Environment) (inputs : LeanIREvaluationCompiler.Inputs env U context)
    (conversion : Conversion env) (exposure : Exposure env) :
    Nat → (source : Lean.Expr) → Option (Artifact inputs source)
  | 0, source => normalized nativeEnv inputs conversion exposure source
  | fuel+1, source =>
      match source with
      | .bvar n => boundVariable nativeEnv inputs n
      | NativeRHL.ExprAnalysis.conditional test decision yes no => do
          let c ← compile nativeEnv inputs conversion exposure fuel test
          let a ← compile nativeEnv inputs conversion exposure fuel yes
          let b ← compile nativeEnv inputs conversion exposure fuel no
          branch nativeEnv inputs conversion exposure c a b decision
      | .letE name type value body flag => do
          let next ← compile nativeEnv inputs conversion exposure fuel (LeanBindings.instantiate value body)
          beta inputs conversion exposure (.letE name type value body flag) next
      | .app (.lam name type body binder) value => do
          let next ← compile nativeEnv inputs conversion exposure fuel (LeanBindings.instantiate value body)
          beta inputs conversion exposure (.app (.lam name type body binder) value) next
      | .mdata _ body => do
          let a ← compile nativeEnv inputs conversion exposure fuel body
          return { a with sourceCore := ⟨a.sourceCore.val,.metadata a.sourceCore.property⟩ }
      | .app (.const ``Int.neg []) arg => do
          let body ← compile nativeEnv inputs conversion exposure fuel arg
          negative nativeEnv inputs conversion exposure .core body
      | .app (.app (.app (.const ``Neg.neg [.zero]) (.const ``Int [])) (.const ``Int.instNegInt [])) arg => do
          let body ← compile nativeEnv inputs conversion exposure fuel arg
          negative nativeEnv inputs conversion exposure .surface body
      | .app (.app head left) right => do
          if let some ⟨op,same⟩ := LeanScalar.checkBinaryHead head then
            let a ← compile nativeEnv inputs conversion exposure fuel left
            let b ← compile nativeEnv inputs conversion exposure fuel right
            binary nativeEnv inputs conversion exposure op true head same a b
          else if let some ⟨op,same⟩ := primitiveHead head then
            let a ← compile nativeEnv inputs conversion exposure fuel left
            let b ← compile nativeEnv inputs conversion exposure fuel right
            binary nativeEnv inputs conversion exposure op false head same a b
          else (knownValue nativeEnv inputs (.app (.app head left) right)).orElse (fun _ => normalized nativeEnv inputs conversion exposure (.app (.app head left) right))
      | other => (knownValue nativeEnv inputs other).orElse (fun _ => normalized nativeEnv inputs conversion exposure other)

end IRComparison.LeanSourceToIR
