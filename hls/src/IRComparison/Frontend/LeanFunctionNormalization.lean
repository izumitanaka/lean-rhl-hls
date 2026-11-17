import IRComparison.Frontend.LeanLetNormalization

namespace IRComparison.LeanFunctionNormalization
open Lean4Lean LeanTyped
variable {env : VEnv} {U : Nat} {context : List VExpr}

theorem instantiate_typed (ordered : env.Ordered) (args : List VExpr)
    (body : env.HasType U (List.replicate args.length intType ++ context) proof type)
    (typed : ∀ a ∈ args, env.HasType U context a intType) :
    env.HasType U context (instantiateArgs proof args) (instantiateArgs type args) := by
  induction args generalizing proof type with
  | nil => exact body
  | cons a args ih =>
      have next := VEnv.HasType.instN ordered (int_context_inst args.length a context)
        body (typed a (by simp))
      exact ih next (fun b hb => typed b (by simp [hb]))

theorem instantiate_equality (args : List VExpr) (a b : VExpr) :
    instantiateArgs (eqInt a b) args =
      eqInt (instantiateArgs a args) (instantiateArgs b args) := by
  induction args generalizing a b with
  | nil => rfl
  | cons x args ih =>
      simpa only [instantiateArgs, eqInt, intType, VExpr.inst] using ih (a.inst x args.length) (b.inst x args.length)

/-- The normalized open-body proof applies uniformly to all typed arguments.
    It is not regenerated or checked separately for each argument tuple. -/
theorem apply_normalization
    (ordered : env.Ordered)
    (r : LeanLetNormalization.Result nativeEnv env U
      (List.replicate args.length intType ++ context) source)
    (typed : ∀ a ∈ args, env.HasType U context a intType) :
    env.HasType U context (instantiateArgs r.proof args)
      (eqInt (instantiateArgs r.sourceCore.val args) (instantiateArgs r.targetCore.val args)) := by
  simpa only [instantiate_equality] using instantiate_typed ordered args r.correct typed

variable {base : VEnv}

/-- Named ordinary Lean definition to the normalized function application.
    The remaining environment well-formedness premise is explicit. This is
    source normalization, not yet the missing primitive-evaluation/IR bridge. -/
theorem named_application
    (a : LeanDefinition.Artifact nativeEnv name) (view : DefinitionView a)
    (r : LeanLetNormalization.Result nativeEnv base 0 (List.replicate 3 intType) a.function.body)
    (ordered : base.Ordered)
    (registered : base.constants a.declaration.name = some ⟨0, view.type.val⟩)
    (intDeclared : base.constants ``Int = some ⟨0, .sort (.succ .zero)⟩)
    (eqDeclared : base.constants ``Eq = some ⟨1, LeanLetNormalization.equalityType⟩)
    (args : List VExpr) (arity : args.length = 3)
    (typed : ∀ arg ∈ args, base.HasType 0 [] arg intType) :
    (view.extend base).HasType 0 [] (instantiateArgs r.proof args)
      (eqInt (applications (.const a.declaration.name []) args)
        (applications (intLambdas 3 r.targetCore.val) args)) := by
  have extension : base ≤ view.extend base := VEnv.addDefEq_le
  have well := view.extend_ordered_from_body base ordered intDeclared registered
    r.sourceCore.property r.sourceTyped
  have sourceTyped := VEnv.HasType.mono extension r.sourceTyped
  have targetTyped := VEnv.HasType.mono extension r.targetTyped
  have argumentTyped := fun arg h => VEnv.HasType.mono extension (typed arg h)
  have sourceBeta := view.apply_and_instantiate base well intDeclared r.sourceCore.property
    sourceTyped args arity argumentTyped
  have targetForArgs : (view.extend base).HasType 0
      (List.replicate args.length intType ++ []) r.targetCore.val intType := by
    simpa only [arity, List.append_nil] using targetTyped
  have targetBeta := applications_beta well intDeclared args r.targetCore.val targetForArgs argumentTyped
  rw [arity] at targetBeta
  have proofForArgs : (view.extend base).HasType 0 (List.replicate args.length intType ++ [])
      r.proof (eqInt r.sourceCore.val r.targetCore.val) := by
    simpa only [arity, List.append_nil] using VEnv.HasType.mono extension r.correct
  have proof := instantiate_typed well args proofForArgs argumentTyped
  rw [instantiate_equality] at proof
  exact .defeq (LeanLetNormalization.equality_congr eqDeclared intDeclared sourceBeta.symm targetBeta.symm) proof

end IRComparison.LeanFunctionNormalization
