import IRComparison.Frontend.WordStructuralBody

/-! The actual administrative-function environment used by the structural
frontend. These lemmas describe parameter/capture scopes and the compositional
call step; they do not assert completeness of the whole source grammar. -/
namespace IRComparison.WordFrontend.StructuralBody
open Lean4Lean LeanTyped LeanTypeInference

theorem closureReference_parameter (found : args.reverse[n]? = some value) :
    closureReference captureDepth targetDepth σ args n = value := by
  simp only [closureReference,found]

theorem closureReference_captured (k : Nat) :
    closureReference captureDepth targetDepth σ args (args.length+k) =
      LeanBindings.rename (· + (targetDepth-captureDepth)) (σ.reference k) := by
  have missing : args.reverse[args.length+k]? = none := by
    apply List.getElem?_eq_none
    simp only [List.length_reverse]
    omega
  simp only [closureReference,missing,Nat.add_sub_cancel_left]

theorem closureFunctions_parameter (inside : n < arity) :
    closureFunctions fs arity n = none := by simp only [closureFunctions,if_pos inside]

theorem closureFunctions_captured (k : Nat) :
    closureFunctions fs arity (arity+k) = fs k := by
  simp only [closureFunctions,Nat.not_lt.mpr (Nat.le_add_right _ _),if_false,Nat.add_sub_cancel_left]

/-- The parsed child comes from the induction hypothesis on the original
lambda body. No normalized body is reparsed by this call step. -/
theorem capture_apply_complete
    (rec : Recursor env raw) (body : Child raw)
    (arityMatches : args.length = arity)
    {piece : Piece env ctx p ((closureSubstitution captureDepth ctx.length σ args).apply body.val) mode.expected}
    (parsed : rec ctx p mode (closureSubstitution captureDepth ctx.length σ args)
      (closureFunctions fs args.length) body = some piece) :
    (captureContinuation rec captureDepth σ fs arity body).apply ctx p mode args =
      some ⟨(closureSubstitution captureDepth ctx.length σ args).apply body.val,piece⟩ := by
  have arityOK : (args.length != arity) = false := by simp [arityMatches]
  simp only [captureContinuation,arityOK,Bool.false_eq_true,if_false,parsed,
    bind,Option.bind,pure,Option.pure_def]

theorem makeContinuation_captured {body : Child raw}
    (parts : continuationParts value = some (types,body)) :
    makeContinuation rec captureDepth σ fs value =
      some (captureContinuation rec captureDepth σ fs types.length body) := by
  unfold makeContinuation
  split
  · rename_i n shape
    simp [continuationParts,shape,lambdaChain] at parts
  · simp only [parts,bind,Option.bind,pure,Option.pure_def]

theorem makeContinuation_cached
    (shape : value.val = .bvar n) (found : fs n = some continuation) :
    makeContinuation rec captureDepth σ fs value = some continuation := by
  simp only [makeContinuation,shape,found,pure,Option.pure_def]

/-- Capture scope and argument scope are independent source conditions. The
length of the argument vector is derived from the source lambda chain. -/
theorem closureReference_scoped
    (depth : captureDepth ≤ targetDepth)
    (captures : ∀ n < capturedSize,
      LeanScalar.wellScoped captureDepth (σ.reference n) = true)
    (arguments : ∀ value ∈ args, LeanScalar.wellScoped targetDepth value = true)
    (inside : n < args.length+capturedSize) :
    LeanScalar.wellScoped targetDepth (closureReference captureDepth targetDepth σ args n) = true := by
  cases found : args.reverse[n]? with
  | some value =>
    rw [closureReference_parameter found]
    exact arguments value (List.mem_reverse.mp (List.mem_of_getElem? found))
  | none =>
    have outside : args.length ≤ n := by
      simpa only [List.length_reverse] using (List.getElem?_eq_none_iff.mp found)
    simp only [closureReference,found]
    apply LeanBindings.rename_wellScoped _ captureDepth targetDepth
      (captures (n-args.length) (by omega))
    intro k hk
    omega

/-- Scope of an instantiated helper body follows from its original source
scope. This is used before certificate checking, not assumed from its result. -/
theorem closureBody_scoped
    (depth : captureDepth ≤ targetDepth)
    (captures : ∀ n < capturedSize,
      LeanScalar.wellScoped captureDepth (σ.reference n) = true)
    (arguments : ∀ value ∈ args, LeanScalar.wellScoped targetDepth value = true)
    (body : LeanScalar.wellScoped (args.length+capturedSize) source = true) :
    LeanScalar.wellScoped targetDepth
      ((closureSubstitution captureDepth targetDepth σ args).apply source) = true := by
  exact LeanBindings.substitute_wellScoped source _ _ body _
    (fun n hn => closureReference_scoped depth captures arguments hn)

/-- The lambda-chain view derives the body scope and arity from the original
ordinary Lean term. The caller need not supply a second body-scope proof. -/
theorem lambdaChain_scoped {source : Lean.Expr} {body : Child source}
    (inScope : LeanScalar.wellScoped depth source = true)
    (chain : lambdaChain source = some (types,body)) :
    LeanScalar.wellScoped (depth+types.length) body.val = true := by
  induction source generalizing depth types with
  | lam name ty value info iht ihv =>
    have valueScoped : LeanScalar.wellScoped (depth+1) value = true :=
      (Bool.and_eq_true_iff.mp inScope).2
    cases next : lambdaChain value with
    | none =>
      simp only [lambdaChain,next,Option.some.injEq,Prod.mk.injEq] at chain
      rcases chain with ⟨rfl,rfl⟩
      exact valueScoped
    | some pair =>
      obtain ⟨tail,child⟩ := pair
      simp only [lambdaChain,next,Option.some.injEq,Prod.mk.injEq] at chain
      rcases chain with ⟨rfl,rfl⟩
      simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm 1] using ihv valueScoped next
  | _ => simp [lambdaChain] at chain

/-- Every application has its original head as a strict child. This derives
the helper-view success from syntax, without invoking the body parser. -/
theorem applicationHead_app (fn argument : Lean.Expr) :
    ∃ head, applicationHead (.app fn argument) = some head ∧ head.val = fn.getAppFn := by
  induction fn generalizing argument with
  | app f a ihf iha =>
    obtain ⟨head,found,same⟩ := ihf a
    rw [applicationHead]
    simp only [found]
    exact ⟨_,rfl,same⟩
  | _ => exact ⟨_,rfl,rfl⟩

/-- A source-side lambda chain. Its constructors mention only ordinary Lean
syntax, not the continuation parser or a successful compilation. `last` stops
at a non-lambda because all leading binders belong to the same helper. -/
inductive LambdaSource : Lean.Expr → List Lean.Expr → Lean.Expr → Prop where
  | last {name : Lean.Name} {ty body : Lean.Expr} {info : Lean.BinderInfo}
      (notLambda : ∀ name ty value info, body ≠ .lam name ty value info) :
      LambdaSource (.lam name ty body info) [ty] body
  | next {name : Lean.Name} {ty body : Lean.Expr} {info : Lean.BinderInfo}
      {types : List Lean.Expr} {result : Lean.Expr} (tail : LambdaSource body types result) :
      LambdaSource (.lam name ty body info) (ty::types) result

theorem LambdaSource.parts (source : LambdaSource value types result) :
    ∃ body : Child value, lambdaChain value = some (types,body) ∧ body.val = result := by
  induction source with
  | @last name ty body info notLambda =>
    have stopped : lambdaChain body = none := by
      cases body <;> first | rfl | exact False.elim (notLambda _ _ _ _ rfl)
    refine ⟨⟨body,by simp only [syntaxSize]; omega⟩,?_,rfl⟩
    simp only [lambdaChain,stopped]
  | @next name ty body info types result tail ih =>
    obtain ⟨child,found,rfl⟩ := ih
    refine ⟨⟨child.val,by have := child.property; simp only [syntaxSize]; omega⟩,?_,rfl⟩
    simp only [lambdaChain,found]

/-- Construct the actual continuation directly from source syntax. The
callback still receives a strict child of the original source expression. -/
theorem LambdaSource.capture (source : LambdaSource value.val types result)
    (rec : Recursor env raw) :
    ∃ body : Child raw,
      body.val = result ∧
      makeContinuation rec captureDepth σ fs value =
        some (captureContinuation rec captureDepth σ fs types.length body) := by
  obtain ⟨child,found,same⟩ := source.parts
  have parts : continuationParts value =
      some (types,ScalarEnvironment.below value child) := by
    simp only [continuationParts,found,bind,Option.bind,pure,Option.pure_def]
  exact ⟨_,same,makeContinuation_captured parts⟩

/-- Source scope plus the actual argument count implies scope of the body
passed to the recursive parser. This discharges that condition at call sites;
it is not inferred from the result of parsing the body. -/
theorem LambdaSource.call_scoped (source : LambdaSource value types result)
    (inScope : LeanScalar.wellScoped capturedSize value = true)
    (arity : args.length = types.length)
    (depth : captureDepth ≤ targetDepth)
    (captures : ∀ n < capturedSize,
      LeanScalar.wellScoped captureDepth (σ.reference n) = true)
    (arguments : ∀ v ∈ args, LeanScalar.wellScoped targetDepth v = true) :
    LeanScalar.wellScoped targetDepth
      ((closureSubstitution captureDepth targetDepth σ args).apply result) = true := by
  obtain ⟨child,found,same⟩ := source.parts
  have bodyScope := lambdaChain_scoped inScope found
  rw [same] at bodyScope
  apply closureBody_scoped depth captures arguments
  simpa only [arity,Nat.add_comm] using bodyScope

end IRComparison.WordFrontend.StructuralBody
