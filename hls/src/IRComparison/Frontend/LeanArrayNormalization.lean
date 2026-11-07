import IRComparison.Frontend.LeanLoopNormalization

namespace IRComparison.ArrayNormalizationFacts

theorem identity (a : Array Int) : a.map (fun z => z) = a := by simp

theorem fuse (a source : Array Int) (f g : Int → Int) (h : a.map g = source) :
    a.map (fun z => f (g z)) = source.map f := by rw [← h,Array.map_map]; rfl

theorem result (output : Option (Array Int)) (normal source : Array Int)
    (h : output = some normal) (hn : normal = source) : output = some source := hn ▸ h

end IRComparison.ArrayNormalizationFacts

namespace IRComparison.LeanArrayNormalization
open Lean4Lean LeanTyped LeanIRQuotation LeanTypeInference
variable {env : VEnv} {U : Nat} {context : List VExpr}
@[reducible] def arrayType : VExpr := .app (.const ``Array [.zero]) intType
def arrayEq (a b : VExpr) := applications (.const ``Eq [.succ .zero]) [arrayType,a,b]
def mapped (f a : VExpr) := applications (.const ``Array.map [.zero,.zero]) [intType,intType,f,a]
def mapExpr (f a : Lean.Expr) := Lean.mkAppN (.const ``Array.map [.zero,.zero]) #[.const ``Int [],.const ``Int [],f,a]

structure Artifact (input : VExpr) (source : Lean.Expr) where
  mapper : Lean.Expr
  mapperCore : {v // Represents mapper v}
  mapperTyped : env.HasType U context mapperCore.val (.forallE intType intType)
  sourceCore : {v // Represents source v}
  sourceTyped : env.HasType U context sourceCore.val arrayType
  proof : VExpr
  correct : env.HasType U context proof (arrayEq (mapped mapperCore.val input) sourceCore.val)

def finish (input : VExpr) (conversion : Conversion env) (exposure : Exposure env)
    (source mapper : Lean.Expr) (p : LeanProofApplication.Typed env U context) :
    Option (Artifact (env := env) (U := U) (context := context) input source) := do
  let f ← translate mapper
  let s ← translate source
  let hf ← checkWith env conversion U context f.val (.forallE intType intType) exposure
  let hs ← checkWith env conversion U context s.val arrayType exposure
  let proof ← LeanLoopNormalization.cast conversion p (arrayEq (mapped f.val input) s.val)
  return ⟨mapper,f,hf.down,s,hs.down,proof.val,proof.property⟩

def compile (native : Lean.Environment) (input : VExpr) (conversion : Conversion env) (exposure : Exposure env) :
    Nat → (source : Lean.Expr) → Option (Artifact (env := env) (U := U) (context := context) input source)
  | 0,_ => none
  | fuel+1,source => do
    match source with
    | .letE name ty value body flag =>
      let next ← compile native input conversion exposure fuel (LeanBindings.instantiate value body)
      finish input conversion exposure (.letE name ty value body flag) next.mapper ⟨next.proof,_,next.correct⟩
    | .app (.app (.app (.app (.const ``Array.map [.zero,.zero]) (.const ``Int [])) (.const ``Int [])) f) a =>
      let previous ← compile native input conversion exposure fuel a
      let fc ← translate f
      let hf ← checkWith env conversion U context fc.val (.forallE intType intType) exposure
      let ha ← checkWith env conversion U context input arrayType exposure
      let proof ← LeanLoopNormalization.args native ``ArrayNormalizationFacts.fuse
        [⟨input,arrayType,ha.down⟩,⟨previous.sourceCore.val,arrayType,previous.sourceTyped⟩,
         ⟨fc.val,.forallE intType intType,hf.down⟩,
         ⟨previous.mapperCore.val,.forallE intType intType,previous.mapperTyped⟩,
         ⟨previous.proof,_,previous.correct⟩]
      let mapper := Lean.Expr.lam `value (.const ``Int [])
        (.app (LeanBindings.rename Nat.succ f)
          (.app (LeanBindings.rename Nat.succ previous.mapper) (.bvar 0))) .default
      finish input conversion exposure (mapExpr f a) mapper proof
    | other =>
      let core ← translate other
      if same : core.val = input then
        let ha ← checkWith env conversion U context input arrayType exposure
        let proof ← LeanLoopNormalization.args native ``ArrayNormalizationFacts.identity [⟨input,arrayType,ha.down⟩]
        finish input conversion exposure other (.lam `value (.const ``Int []) (.bvar 0) .default) proof
      else none

end IRComparison.LeanArrayNormalization
