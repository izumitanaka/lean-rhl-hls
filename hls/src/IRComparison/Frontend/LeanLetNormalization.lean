import IRComparison.Frontend.LeanTypeReduction

namespace IRComparison.LeanLetNormalization
open Lean4Lean LeanTyped LeanTypeInference

def equalityType : VExpr :=
  .forallE (.sort (.param 0)) (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)))

variable {env : VEnv} {U : Nat} {context : List VExpr}

theorem equality_congr
    (eqDeclared : env.constants ``Eq = some ⟨1, equalityType⟩)
    (intDeclared : env.constants ``Int = some ⟨0, .sort (.succ .zero)⟩)
    (left : env.IsDefEq U context a a' intType)
    (right : env.IsDefEq U context b b' intType) :
    env.IsDefEq U context (eqInt a b) (eqInt a' b') (.sort .zero) := by
  have head := VEnv.HasType.const (U := U) (Γ := context) (ls := [.succ .zero])
    eqDeclared (by simp [VLevel.WF]) rfl
  simp only [equalityType, VExpr.instL, VLevel.inst, List.getD_cons_zero] at head
  have typed := VEnv.IsDefEq.appDF head (int_hasType intDeclared context)
  simp only [VExpr.inst, VExpr.instVar_succ, VExpr.instVar_zero] at typed
  have applied := VEnv.IsDefEq.appDF typed left
  simp only [VExpr.inst, VExpr.inst_lift] at applied
  exact VEnv.IsDefEq.appDF applied right

/-- The proof of the normalized body can be reused after beta computation.
    No extra axiom, proof checker, or assumed let/IR equivalence is involved. -/
theorem let_proof
    (eqDeclared : env.constants ``Eq = some ⟨1, equalityType⟩)
    (intDeclared : env.constants ``Int = some ⟨0, .sort (.succ .zero)⟩)
    (bodyTyped : env.HasType U (intType :: context) body intType)
    (valueTyped : env.HasType U context value intType)
    (targetTyped : env.HasType U context target intType)
    (proofTyped : env.HasType U context proof (eqInt (body.inst value) target)) :
    env.HasType U context proof (eqInt (.app (.lam intType body) value) target) := by
  have beta : env.IsDefEq U context (.app (.lam intType body) value) (body.inst value) intType :=
    .beta bodyTyped valueTyped
  exact .defeq (equality_congr eqDeclared intDeclared beta.symm targetTyped) proofTyped

structure Result (nativeEnv : Lean.Environment) (env : VEnv) (U : Nat)
    (context : List VExpr) (source : Lean.Expr) where
  expression : Lean.Expr
  sourceCore : {v // Represents source v}
  targetCore : {v // Represents expression v}
  proof : VExpr
  correct : env.HasType U context proof (eqInt sourceCore.val targetCore.val)
  sourceTyped : env.HasType U context sourceCore.val intType
  targetTyped : env.HasType U context targetCore.val intType
  preserves : ∀ values result, NativeRHL.ExprAnalysis.Denotes source values result →
    NativeRHL.ExprAnalysis.Denotes expression values result

/-- The current scalar source parser admits integer lets. Its actual
    capture-avoiding substitution is connected to the formal beta rule. -/
def normalize (nativeEnv : Lean.Environment) (env : VEnv) (U : Nat)
    (context : List VExpr) (conversion : Conversion env) (exposure : Exposure env) :
    (source : Lean.Expr) → Option (Result nativeEnv env U context source)
  | .letE _ (.const ``Int []) value body _ => do
      let valueCore ← translate value
      let bodyCore ← translate body
      let valueTyped ← checkWith env conversion U context valueCore.val intType exposure
      let bodyTyped ← checkWith env conversion U (intType :: context) bodyCore.val intType exposure
      let next ← LeanTypeInference.normalize nativeEnv env U context
        (LeanBindings.instantiate value body) conversion exposure
      if heq : env.constants ``Eq = some ⟨1, equalityType⟩ then
        if hint : env.constants ``Int = some ⟨0, .sort (.succ .zero)⟩ then
          let same := (bodyCore.property.instantiate valueCore.property).unique next.plan.represents_source
          let nextCorrect := next.plan.correct next.reflRegistered next.transRegistered
            next.congrRegistered next.ready
          return {
            expression := next.plan.expression
            sourceCore := ⟨.app (.lam intType bodyCore.val) valueCore.val,
              .letE (.constant rfl) valueCore.property bodyCore.property⟩
            targetCore := ⟨next.plan.normalizedCore, next.plan.represents_normalized⟩
            proof := next.plan.proofTerm
            correct := let_proof heq hint bodyTyped.down valueTyped.down nextCorrect.2.1
              (by simpa only [same] using nextCorrect.2.2)
            sourceTyped := .app (.lam (int_hasType hint context) bodyTyped.down) valueTyped.down
            targetTyped := nextCorrect.2.1
            preserves := by
              intro values result h
              cases h with
              | letValue hv hb =>
                exact next.plan.preserves_denotes (LeanBindings.denotes_instantiate hv hb) }
        else none
      else none
  | _ => none

def unchangedOrArithmetic (nativeEnv : Lean.Environment) (env : VEnv) (U : Nat)
    (context : List VExpr) (conversion : Conversion env) (exposure : Exposure env)
    (source : Lean.Expr) : Option (Result nativeEnv env U context source) := do
  let parsed ← LeanTypeInference.normalize nativeEnv env U context source conversion exposure
  let typed := parsed.plan.correct parsed.reflRegistered parsed.transRegistered
    parsed.congrRegistered parsed.ready
  return {
    expression := parsed.plan.expression
    sourceCore := ⟨parsed.plan.sourceCore, parsed.plan.represents_source⟩
    targetCore := ⟨parsed.plan.normalizedCore, parsed.plan.represents_normalized⟩
    proof := parsed.plan.proofTerm
    correct := typed.2.2
    sourceTyped := typed.1
    targetTyped := typed.2.1
    preserves := fun _ _ h => parsed.plan.preserves_denotes h }

def Result.compose (first : Result nativeEnv env U context source)
    (second : Result nativeEnv env U context first.expression)
    (transRegistered : env.constants ``Standard.intTrans = some ⟨0, transType⟩) :
    Result nativeEnv env U context source where
  expression := second.expression
  sourceCore := first.sourceCore
  targetCore := second.targetCore
  proof := applications (.const ``Standard.intTrans [])
    [first.sourceCore.val, first.targetCore.val, second.targetCore.val, first.proof, second.proof]
  correct := apply_trans transRegistered first.sourceTyped first.targetTyped second.targetTyped
    first.correct (by
      have same := first.targetCore.property.unique second.sourceCore.property
      simpa only [same] using second.correct)
  sourceTyped := first.sourceTyped
  targetTyped := second.targetTyped
  preserves := fun values result h => second.preserves values result (first.preserves values result h)

/-- Normalize an arbitrary number of leading integer lets. Fuel bounds work;
    at zero the expression is preserved or arithmetic-normalized with a proof,
    rather than assuming the remaining lets absent or dropping their effects. -/
def leading (nativeEnv : Lean.Environment) (env : VEnv) (U : Nat)
    (context : List VExpr) (conversion : Conversion env) (exposure : Exposure env) :
    Nat → (source : Lean.Expr) → Option (Result nativeEnv env U context source)
  | 0, source => unchangedOrArithmetic nativeEnv env U context conversion exposure source
  | fuel+1, source => do
      if let some first := normalize nativeEnv env U context conversion exposure source then
        let second ← leading nativeEnv env U context conversion exposure fuel first.expression
        if registered : env.constants ``Standard.intTrans = some ⟨0, transType⟩ then
          return first.compose second registered
        else none
      else unchangedOrArithmetic nativeEnv env U context conversion exposure source

theorem Result.compilers_agree (r : Result nativeEnv env U context source)
    (before : LeanScalar.Artifact layout source)
    (after : LeanScalar.Artifact layout r.expression) (i x y : Int) (s : State) :
    before.code.expr.eval i x y s = after.code.expr.eval i x y s := by
  have same := NativeRHL.ExprAnalysis.denotes_unique
    (r.preserves _ _ (before.denotes i x y s)) (after.denotes i x y s)
  rw [before.code.correct, after.code.correct, same]

end IRComparison.LeanLetNormalization
