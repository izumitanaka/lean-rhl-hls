import IRComparison.Frontend.WordGeneratedCode
import IRComparison.Frontend.WordFunctionState
import IRComparison.Frontend.WordFixedScalarCompleteness
namespace IRComparison.WordFrontend.StructuralBody
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic
set_option maxHeartbeats 2400000
/-- This invariant reuses the existing ordinary/loop body certificate types.
It is an invariant of a generated piece, not a definition of input syntax. -/
def RetainedCasts (setup : AliasSetup env) (inputs : InputsTyped env ctx p)
    (mode : Mode) (source : Lean.Expr) (piece : Piece env ctx p source mode.expected) : Prop :=
  match mode with
  | .body => ∃ typed : BodyCasts inputs piece (SourceCasts env) (For.Casts setup),
      ValueForm setup ctx typed.sourceCore.val (optionType stateType)
  | .step => ∃ typed : StructuralLoop.StepCasts inputs piece (SourceCasts env) (For.Casts setup),
      ValueForm setup ctx typed.sourceCore.val (optionType Step.stepState)
  | .value => False

/-- Ordinary bodies and loop continuations differ only in their equality
prefix. Extract it once for call transport, reusing the two existing
certificate representations and their common command typing. -/
theorem RetainedCasts.equalityPrefix
    (library : ScopedSyntax.Library env) (inputs : InputsTyped env ctx p)
    {piece : Piece env ctx p previous mode.expected}
    (typed : RetainedCasts setup inputs mode previous piece) :
    ∃ core head,
      Represents previous core ∧
      CastTyping env 0 (SourceCasts env) ctx head
        (.forallE (optionType (if mode == .step then Step.stepState else stateType)) (.sort .zero)) ∧
      ∀ source sourceCore, Represents source sourceCore →
        Represents (mode.expected p piece.code source) (.app head sourceCore) := by
  cases mode with
  | value => exact False.elim typed
  | body =>
    obtain ⟨child,form⟩ := typed
    have evaluation := eval_cast_typed inputs library.eval child.target
    have prefixTyped := CastTyping.application
      ((equality_head_typed library.steps.state library.steps.option library.eq).withCasts (SourceCasts env)) evaluation
    simp only [WordFrontend.optionState,stateType,VExpr.inst] at prefixTyped
    exact ⟨child.sourceCore.val,_,child.sourceCore.property,prefixTyped,
      fun _ _ represented => bodyExpected_represents inputs piece.represented.property represented⟩
  | step =>
    obtain ⟨child,form⟩ := typed
    have evaluation := eval_cast_typed inputs library.eval child.target
    exact ⟨child.sourceCore.val,_,child.sourceCore.property,
      Step.equalityPrefix_typed library.steps library.eq evaluation,
      fun _ _ represented => Step.expected_represents (evalCmd_represents inputs piece.represented.property) represented⟩

/-- The actual argument-binding operation uses the established let rule in
both execution modes. The continuation is arbitrary, including State
updates, reads, nested control flow and further calls. -/
theorem bindArgument_complete (setup : AliasSetup env) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (fresh : ScopedSyntax.Fresh setup)
    (exposure : Exposure env) (inputs : InputsTyped env ctx p) (mode : Mode)
    (annotation : WordBinder.Annotation)
    {initial : Piece env ctx p value scalarExpected}
    (left : ScalarCasts inputs initial (SourceCasts env) (For.Casts setup))
    {next : Piece env (annotation.core::ctx) {p.lift with locals := .bvar 0::p.lift.locals} nextSource mode.expected}
    (right : RetainedCasts setup
      (annotation.nextInputs inputs closed library.scalars.toSignatures library.cons)
      mode nextSource next) :
    ∃ piece, bindArgument env setup.conversion exposure ctx p mode annotation value initial ⟨nextSource,next⟩ =
        some ⟨Lean.Expr.letE `_argument annotation.native value nextSource false,piece⟩ ∧
      RetainedCasts setup inputs mode _ piece ∧
      piece.code = app ``HybridWord.Cmd.letValue [initial.code,next.code] := by
  have coverage := For.Casts.covered setup library.scalars.toSignatures library.steps closed
    library.cons library.eq library.eval fresh.state fresh.eq fresh.lift
  cases mode with
  | value => exact False.elim right
  | body =>
    have fact : (Mode.body == Mode.step) = false := rfl
    obtain ⟨typed,form⟩ := right
    obtain ⟨artifact,checked,resultTyped,resultForm⟩ := WordBinder.let_certificate annotation setup
      library.scalars.toSignatures inputs closed library.cons library.returns.state library.returns.option
      library.eq library.eval library.letValue library.letValueConstructor fresh.option coverage exposure
      left typed form `_argument false
    let code := ClosedTerm.app ``HybridWord.Cmd.letValue [initial.closedTerm,next.closedTerm]
    let piece : Piece env ctx p (.letE `_argument annotation.native value nextSource false) Mode.body.expected :=
      ⟨code.val,artifact,code.closed,code.represented⟩
    refine ⟨piece,?_,⟨resultTyped,resultForm⟩,rfl⟩
    simp [bindArgument, finishBody, fact]
    exact ⟨artifact, checked, rfl⟩
  | step =>
    have fact : (Mode.step == Mode.step) = true := rfl
    obtain ⟨typed,form⟩ := right
    obtain ⟨artifact,checked,resultTyped,resultForm⟩ := WordBinder.step_let_certificate annotation setup
      library.scalars.toSignatures inputs closed library.cons library.steps library.eq library.eval
      library.stepLetValue library.letValueConstructor fresh.option coverage exposure left typed form `_argument false
    let code := ClosedTerm.app ``HybridWord.Cmd.letValue [initial.closedTerm,next.closedTerm]
    let piece : Piece env ctx p (.letE `_argument annotation.native value nextSource false) Mode.step.expected :=
      ⟨code.val,artifact,code.closed,code.represented⟩
    refine ⟨piece,?_,⟨resultTyped,resultForm⟩,rfl⟩
    simp [bindArgument, finishBody, fact]
    exact ⟨artifact, checked, rfl⟩
/-- Compositional success for the actual recursive argument traversal.
The two parsing premises are induction hypotheses, not the definition of a
supported source language. No premise restricts the continuation's commands. -/
theorem retainArguments_bind_complete
    (setup : AliasSetup env) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (fresh : ScopedSyntax.Fresh setup)
    (exposure : Exposure env) (inputs : InputsTyped env ctx p)
    (continuation : Continuation env) (mode : Mode) (annotation : WordBinder.Annotation) (rest saved : List Lean.Expr)
    (scalar : (sameTerm value p.s || unitArgument env setup.conversion exposure ctx value) = false)
    (selected : argumentAnnotation env setup.conversion exposure ctx value = annotation)
    {initial : Piece env ctx p value scalarExpected}
    (firstParsed : ScalarEnvironment.parse env setup.conversion exposure ctx p value = some initial)
    (left : ScalarCasts inputs initial (SourceCasts env) (For.Casts setup))
    {next : Piece env (annotation.core::ctx) {p.lift with locals := .bvar 0::p.lift.locals} nextSource mode.expected}
    (nextParsed : retainArguments env setup.conversion exposure continuation (annotation.core::ctx)
      {p.lift with locals := .bvar 0::p.lift.locals} mode
      (rest.map (LeanBindings.rename Nat.succ))
      ((saved.map (LeanBindings.rename Nat.succ)) ++ [.bvar 0]) = some ⟨nextSource,next⟩)
    (right : RetainedCasts setup
      (annotation.nextInputs inputs closed library.scalars.toSignatures library.cons)
      mode nextSource next) :
    ∃ piece, retainArguments env setup.conversion exposure continuation ctx p mode (value::rest) saved =
        some ⟨Lean.Expr.letE `_argument annotation.native value nextSource false,piece⟩ ∧
      RetainedCasts setup inputs mode _ piece ∧
      piece.code = app ``HybridWord.Cmd.letValue [initial.code,next.code] := by
  obtain ⟨piece,bound,typed,code⟩ := bindArgument_complete setup library closed fresh exposure
    inputs mode annotation left right
  refine ⟨piece,?_,typed,code⟩
  have ordinary : (mode == Mode.value) = false := by
    cases mode with
    | body | step => rfl
    | value => exact False.elim right
  rw [retainArguments]
  simp only [scalar,ordinary,Bool.false_eq_true,ite_false,firstParsed,bind,Option.bind]
  rw [selected]
  simpa only [nextParsed,bind,Option.bind,pure,Option.pure_def] using bound


/-- Classification of an argument comes from its independent source type;
it does not assume success of `unitArgument` or of the compiler. -/
theorem unitArgument_of_type (represented : Represents value core)
    (typed : CastTyping env 0 casts ctx core ty)
    (coverage : Conversion.Covers conv 0 casts) (exposure : Exposure env) :
    unitArgument env conv exposure ctx value = (ty == UnitStep.unitType) := by
  obtain ⟨⟨translated,rep⟩,translatedEq,same⟩ := represented.translate_complete
  dsimp only at same
  subst translated
  obtain ⟨⟨inferred,proof⟩,inferredEq,same⟩ := typed.infer_complete
    (known := noKnownTypes env 0) (by intro e actual result he; cases he) coverage exposure
  dsimp only at same
  subst inferred
  simp only [unitArgument,translatedEq,inferredEq,bind,Option.bind]
  change (if ty == UnitStep.unitType then some () else none).isSome = _
  split <;> simp_all

/-- The administrative binder uses the scalar's independently inferred type.
No parser or type-checker success is required as an input condition. -/
theorem argumentAnnotation_of_type (annotation : WordBinder.Annotation)
    (represented : Represents value core)
    (typed : CastTyping env 0 casts ctx core annotation.core)
    (coverage : Conversion.Covers conv 0 casts) (exposure : Exposure env) :
    argumentAnnotation env conv exposure ctx value = annotation := by
  obtain ⟨⟨translated,rep⟩,translatedEq,same⟩ := represented.translate_complete
  dsimp only at same
  subst translated
  obtain ⟨⟨inferred,proof⟩,inferredEq,same⟩ := typed.infer_complete
    (known := noKnownTypes env 0) (by intro e actual result he; cases he) coverage exposure
  dsimp only at same
  subst inferred
  simp only [argumentAnnotation,translatedEq,inferredEq,bind,Option.bind,pure,Option.pure_def]
  cases annotation with
  | word => rfl
  | bitvec => simp only [WordBinder.Annotation.core,BEq.rfl,ite_true]

/-- A source-level argument telescope. It only records which actual values
are retained and the resulting lexical context. The sole body is supplied
at the endpoint by the existing Source judgment. It is not another input
language and contains no successful parser/checker premise. -/
inductive ArgumentBindings {env : VEnv} :
    List VExpr → Inputs → List Lean.Expr → List Lean.Expr →
    List VExpr → Inputs → List Lean.Expr →
    (Lean.Expr → Lean.Expr) →
    ((HybridWord.Word → HybridWord.Word → HybridWord.Word → List HybridWord.Word → HybridWord.State → Option HybridWord.State) →
      (HybridWord.Word → HybridWord.Word → HybridWord.Word → List HybridWord.Word → HybridWord.State → Option HybridWord.State)) →
    (HybridWord.Cmd → HybridWord.Cmd) → (Lean.Expr → Lean.Expr) → Prop where
  | done : ArgumentBindings (env := env) ctx p [] saved ctx p saved id id id id
  | state (current : value = p.s)
      (next : ArgumentBindings (env := env) ctx p rest (saved ++ [value])
        finalCtx finalInputs finalArgs sourceWrap nativeWrap codeWrap quoteWrap) :
      ArgumentBindings (env := env) ctx p (value::rest) saved
        finalCtx finalInputs finalArgs sourceWrap nativeWrap codeWrap quoteWrap
  | unit (represented : Represents value core)
      (typed : CastTyping env 0 (SourceCasts env) ctx core UnitStep.unitType)
      (next : ArgumentBindings (env := env) ctx p rest (saved ++ [value])
        finalCtx finalInputs finalArgs sourceWrap nativeWrap codeWrap quoteWrap) :
      ArgumentBindings (env := env) ctx p (value::rest) saved
        finalCtx finalInputs finalArgs sourceWrap nativeWrap codeWrap quoteWrap
  | scalar (valueSource : FixedScalarCompleteness.Scoped env ctx p value f vc vq)
      (annotation : WordBinder.Annotation) (represented : Represents value core)
      (typed : CastTyping env 0 (SourceCasts env) ctx core annotation.core)
      (notState : sameTerm value p.s = false)
      (next : ArgumentBindings (env := env) (annotation.core::ctx)
        {p.lift with locals := .bvar 0::p.lift.locals}
        (rest.map (LeanBindings.rename Nat.succ))
        ((saved.map (LeanBindings.rename Nat.succ)) ++ [.bvar 0])
        finalCtx finalInputs finalArgs sourceWrap nativeWrap codeWrap quoteWrap) :
      ArgumentBindings (env := env) ctx p (value::rest) saved finalCtx finalInputs finalArgs
        (fun body => .letE `_argument annotation.native value (sourceWrap body) false)
        (fun body i x y ls s => (f i x y s ls).bind (fun v => nativeWrap body i x y (v::ls) s))
        (fun body => .letValue vc (codeWrap body))
        (fun body => app ``HybridWord.Cmd.letValue [vq,quoteWrap body])

/-- Extend the existing lexical input invariants along the argument bindings.
The endpoint body does not need independently supplied environment evidence. -/
theorem ArgumentBindings.endpointInputs
    (arguments : ArgumentBindings (env := env) ctx p actuals saved
      finalCtx finalInputs finalArgs sourceWrap nativeWrap codeWrap quoteWrap)
    (library : ScopedSyntax.Library env) (closed : ClosedConstantTypes env)
    (inputs : InputsTyped env ctx p) (locals : ScalarSyntax.Locals env ctx p) :
    Nonempty (InputsTyped env finalCtx finalInputs) ∧ Nonempty (ScalarSyntax.Locals env finalCtx finalInputs) := by
  induction arguments with
  | done => exact ⟨⟨inputs⟩,⟨locals⟩⟩
  | state _ _ ih | unit _ _ _ ih => exact ih inputs locals
  | scalar _ annotation _ _ _ _ ih =>
    exact ih (annotation.nextInputs inputs closed library.scalars.toSignatures library.cons)
      (annotation.nextLocals locals closed)

/-- Each retained scalar adds one lexical slot. State and PUnit actuals
add none, so the source argument count bounds the inserted let prefix. -/
theorem ArgumentBindings.context_growth
    (arguments : ArgumentBindings (env := env) ctx p actuals saved
      finalCtx finalInputs finalArgs sourceWrap nativeWrap codeWrap quoteWrap) :
    ctx.length ≤ finalCtx.length ∧ finalCtx.length ≤ ctx.length + actuals.length := by
  induction arguments with
  | done => simp
  | state _ _ ih | unit _ _ _ ih =>
    simp only [List.length_cons]
    omega
  | scalar _ _ _ _ _ _ ih =>
    simp only [List.length_cons,List.length_map] at ih ⊢
    omega

/-- Keeping a scalar in a fresh slot changes its representation, not the
number or order of actual arguments. Users only need the source arity. -/
theorem ArgumentBindings.argument_count
    (arguments : ArgumentBindings (env := env) ctx p actuals saved
      finalCtx finalInputs finalArgs sourceWrap nativeWrap codeWrap quoteWrap) :
    finalArgs.length = saved.length + actuals.length := by
  induction arguments with
  | done => simp
  | state _ _ ih | unit _ _ _ ih =>
    simp only [List.length_append,List.length_nil,List.length_cons] at ih ⊢
    omega
  | scalar _ _ _ _ _ _ ih =>
    simp only [List.length_append,List.length_nil,List.length_cons,
      List.length_map] at ih ⊢
    omega

/-- Contracting exactly the inserted scalar slots yields the original
closure substitution, for every body and captured scope. The induction does
not traverse or restrict the helper body, nor assume compiler success. -/
theorem ArgumentBindings.contract
    (arguments : ArgumentBindings (env := env) ctx p actuals saved
      finalCtx finalInputs finalArgs sourceWrap nativeWrap codeWrap quoteWrap)
    (bound : capture ≤ ctx.length) (captured : Substitution) (body : Lean.Expr) :
    RetainedConversion.contractLets (finalCtx.length - ctx.length)
      (sourceWrap ((closureSubstitution capture finalCtx.length captured finalArgs).apply body)) =
      some ((closureSubstitution capture ctx.length captured (saved ++ actuals)).apply body) := by
  induction arguments with
  | done => simp only [Nat.sub_self,RetainedConversion.contractLets,id_eq,List.append_nil]
  | state _ next ih | unit _ _ next ih =>
    simpa only [List.append_assoc,List.singleton_append] using ih bound
  | @scalar ctx p value f vc vq core finalCtx finalInputs finalArgs sw nw cw qw rest saved
      valueSource annotation represented typed notState next ih =>
    have growth := next.context_growth.1
    have difference : finalCtx.length - ctx.length =
        (finalCtx.length - (annotation.core::ctx).length)+1 := by
      simp only [List.length_cons] at growth ⊢
      omega
    have tail := ih (by simp only [List.length_cons]; omega)
    have substituted := RetainedConversion.contractLets_substitute tail
      (fun | 0 => value | n+1 => .bvar n)
    rw [difference,RetainedConversion.contractLets]
    change RetainedConversion.contractLets _ (LeanBindings.instantiate value _) =
      some (LeanBindings.instantiate value _) at substituted
    simpa only [List.length_cons,FunctionSyntax.closureSubstitution_retain_actual bound]
      using substituted

/-- Derive the whole typed administrative prefix from the argument telescope
and the single endpoint body's typing. This is uniform in the body: State
updates, reads and nested control flow require no second derivation here. -/
theorem ArgumentBindings.prefix
    (arguments : ArgumentBindings (env := env) ctx p actuals saved
      finalCtx finalInputs finalArgs sourceWrap nativeWrap codeWrap quoteWrap)
    (library : Signatures env) (bound : capture ≤ ctx.length)
    (captured : Substitution) (body : Lean.Expr)
    (bodyRep : Represents
      ((closureSubstitution capture finalCtx.length captured finalArgs).apply body) bodyCore)
    (bodyTyped : CastTyping env 0 (SourceCasts env) finalCtx bodyCore ty) :
    ∃ source target,
      Represents (sourceWrap ((closureSubstitution capture finalCtx.length captured finalArgs).apply body)) source ∧
      Represents ((closureSubstitution capture ctx.length captured (saved ++ actuals)).apply body) target ∧
      RetainedConversion.Prefix env 0 (SourceCasts env) ty ctx source target
        (finalCtx.length - ctx.length) := by
  induction arguments with
  | done =>
    exact ⟨bodyCore,bodyCore,bodyRep,by simpa using bodyRep,by simpa using RetainedConversion.Prefix.done bodyTyped⟩
  | state _ next ih | unit _ _ next ih =>
    simpa only [List.append_assoc,List.singleton_append] using ih bound bodyRep bodyTyped
  | @scalar ctx p value f vc vq core finalCtx finalInputs finalArgs sw nw cw qw rest saved
      valueSource annotation represented typed notState next ih =>
    obtain ⟨source,target,sourceRep,targetRep,chain⟩ := ih
      (by simp only [List.length_cons]; omega) bodyRep bodyTyped
    have growth := next.context_growth.1
    have difference : finalCtx.length - ctx.length =
        (finalCtx.length - (annotation.core::ctx).length)+1 := by
      simp only [List.length_cons] at growth ⊢
      omega
    refine ⟨.app (.lam annotation.core source) core,target.inst core,
      .letE annotation.represented represented sourceRep,?_,?_⟩
    · simpa only [List.length_cons,FunctionSyntax.closureSubstitution_retain_actual bound]
        using targetRep.instantiate represented
    · rw [difference]
      exact .bind annotation.closed ((annotation.type_typed library).withCasts _) typed chain

/-- The actual retained-prefix converter succeeds from one body typing and
the argument telescope. Its allowance is the ordinary source argument count,
including State and unit arguments, rather than a separately supplied budget. -/
theorem ArgumentBindings.prefix_complete
    (arguments : ArgumentBindings (env := env) ctx p actuals saved
      finalCtx finalInputs finalArgs sourceWrap nativeWrap codeWrap quoteWrap)
    (library : Signatures env) (bound : capture ≤ ctx.length)
    (captured : Substitution) (body : Lean.Expr)
    (bodyRep : Represents
      ((closureSubstitution capture finalCtx.length captured finalArgs).apply body) bodyCore)
    (bodyTyped : CastTyping env 0 (SourceCasts env) finalCtx bodyCore ty)
    (retainedRep : Represents
      (sourceWrap ((closureSubstitution capture finalCtx.length captured finalArgs).apply body)) retainedCore)
    (originalRep : Represents
      ((closureSubstitution capture ctx.length captured (saved ++ actuals)).apply body) originalCore)
    (closed : ClosedConstantTypes env) (resultClosed : ty.ClosedN 0)
    (coverage : Conversion.Covers conv 0 (SourceCasts env)) (exposure : Exposure env)
    (targetTyped : env.HasType 0 ctx originalCore ty) :
    ∃ result, RetainedConversion.reducePrefix conv exposure 0 ctx originalCore ty targetTyped
      actuals.length retainedCore = some result := by
  obtain ⟨source,target,sourceRep,targetRep,chain⟩ :=
    arguments.prefix library bound captured body bodyRep bodyTyped
  have sourceEq := sourceRep.unique retainedRep
  have targetEq := targetRep.unique originalRep
  subst source; subst target
  obtain ⟨result,success⟩ := chain.complete closed SourceCasts.closed resultClosed coverage exposure targetTyped
  exact RetainedConversion.reducePrefix_mono targetTyped success (by
    have growth := arguments.context_growth
    omega)

/-- Transport the source-level prefix equation to the calculus used by the
actual converter. Representation of the original body determines the unique
endpoint; callers do not provide a separate reduced-body equality. -/
theorem ArgumentBindings.contract_represents
    (arguments : ArgumentBindings (env := env) ctx p actuals saved
      finalCtx finalInputs finalArgs sourceWrap nativeWrap codeWrap quoteWrap)
    (bound : capture ≤ ctx.length) (captured : Substitution) (body : Lean.Expr)
    (retainedRep : Represents
      (sourceWrap ((closureSubstitution capture finalCtx.length captured finalArgs).apply body)) core)
    (originalRep : Represents
      ((closureSubstitution capture ctx.length captured (saved ++ actuals)).apply body) target) :
    RetainedConversion.contractCoreLets (finalCtx.length - ctx.length) core = some target := by
  obtain ⟨result,contracted,represented⟩ := RetainedConversion.contractLets_represents retainedRep
    (arguments.contract bound captured body)
  exact represented.unique originalRep ▸ contracted

/-- The endpoint body is arbitrary. The same induction binds every scalar
argument before parsing that body, including when it updates State or reads
arrays. The successful endpoint is the Source induction hypothesis. -/
theorem ArgumentBindings.complete {body : Lean.Expr}
    (arguments : ArgumentBindings (env := env) ctx p actuals saved
      finalCtx finalInputs finalArgs sourceWrap nativeWrap codeWrap quoteWrap)
    (setup : AliasSetup env) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (fresh : ScopedSyntax.Fresh setup)
    (exposure : Exposure env) (inputs : InputsTyped env ctx p) (locals : ScalarSyntax.Locals env ctx p)
    (continuation : Continuation env) (mode : Mode)
    (endpoint : ∀ finalTyped : InputsTyped env finalCtx finalInputs, ScalarSyntax.Locals env finalCtx finalInputs →
      ∃ piece, continuation.apply finalCtx finalInputs mode finalArgs = some ⟨body,piece⟩ ∧
        RetainedCasts setup finalTyped mode body piece ∧ piece.code = quotation) :
    ∃ piece, retainArguments env setup.conversion exposure continuation ctx p mode actuals saved =
        some ⟨sourceWrap body,piece⟩ ∧
      RetainedCasts setup inputs mode (sourceWrap body) piece ∧ piece.code = quoteWrap quotation := by
  have coverage := setup.covers_source library.scalars.toSignatures closed
  induction arguments with
  | done => simpa only [retainArguments,id_eq] using endpoint inputs locals
  | state current next ih =>
    simpa only [retainArguments,current,sameTerm_complete inputs.s.property inputs.s.property,
      Bool.true_or,ite_true] using ih inputs locals endpoint
  | unit represented typed next ih =>
    have selected := unitArgument_of_type represented typed coverage exposure
    simp only [BEq.rfl] at selected
    simpa only [retainArguments,selected,Bool.or_true,ite_true] using ih inputs locals endpoint
  | scalar valueSource annotation represented typed notState next ih =>
    have unit := unitArgument_of_type represented typed coverage exposure
    have notUnit : (annotation.core == UnitStep.unitType) = false := by cases annotation <;> rfl
    rw [notUnit] at unit
    obtain ⟨initial,firstParsed,⟨left⟩,firstCode⟩ := valueSource.complete setup library closed fresh exposure inputs locals
    obtain ⟨child,childParsed,right,childCode⟩ := ih
      (annotation.nextInputs inputs closed library.scalars.toSignatures library.cons)
      (annotation.nextLocals locals closed) endpoint
    obtain ⟨piece,parsed,typed,code⟩ := retainArguments_bind_complete setup library closed fresh exposure inputs
      continuation mode annotation _ _ (by simp only [notState,unit,Bool.false_or])
      (argumentAnnotation_of_type annotation represented typed coverage exposure) firstParsed left childParsed right
    exact ⟨piece,parsed,typed,by rw [code,firstCode,childCode]⟩


/-- The same argument telescope preserves declaration checking and composes
its native meaning with the arbitrary endpoint body's meaning. -/
theorem ArgumentBindings.facts
    (arguments : ArgumentBindings (env := env) ctx p actuals saved
      finalCtx finalInputs finalArgs sourceWrap nativeWrap codeWrap quoteWrap)
    (declared : FixedMemory.declared ds code = true)
    (computation : ∀ i x y s ls, code.eval i x y s ls = native i x y ls s) :
    FixedMemory.declared ds (codeWrap code) = true ∧
      ∀ i x y s ls, (codeWrap code).eval i x y s ls = nativeWrap native i x y ls s := by
  induction arguments with
  | done => exact ⟨declared,computation⟩
  | state _ _ ih | unit _ _ _ ih => exact ih
  | scalar valueSource _ _ _ _ _ ih =>
    exact ⟨by simp [FixedMemory.declared,valueSource.declared,ih.1],
      by intros; simp only [HybridWord.Cmd.eval,valueSource.computation,ih.2,bind,Option.bind]⟩

/-- Retaining actuals preserves the source-scope independence needed by the
fixed-array backend. Scope is derived from the original function and actuals,
not from the generated command or a successful compiler run. -/
theorem ArgumentBindings.independent {functionValue body : Lean.Expr}
    (arguments : ArgumentBindings (env := env) ctx p actuals saved
      finalCtx finalInputs finalArgs sourceWrap nativeWrap codeWrap quoteWrap)
    (shape : LambdaSource functionValue domains body)
    (captureBound : capture ≤ ctx.length)
    (arity : saved.length + actuals.length = domains.length)
    (external : LexicalScalarCode.ExternalAt bound p)
    (functionScope : LeanScalar.wellScoped bound
      ((closureSubstitution capture ctx.length captured []).apply functionValue) = true)
    (savedScope : ∀ a ∈ saved, LeanScalar.wellScoped bound a = true)
    (actualScope : ∀ a ∈ actuals, LeanScalar.wellScoped bound a = true)
    (bodyIndependent : ∀ bound, LexicalScalarCode.ExternalAt bound finalInputs →
      LeanScalar.wellScoped bound
        ((closureSubstitution capture finalCtx.length captured finalArgs).apply body) = true →
      ∀ i x y ls s, native i x y ls s = native 0 0 0 ls s) :
    ∀ i x y ls s, nativeWrap native i x y ls s = nativeWrap native 0 0 0 ls s := by
  induction arguments generalizing bound with
  | done =>
    apply bodyIndependent bound external
    simpa only [List.nil_append] using FunctionSyntax.lambdaSource_apply_scoped shape functionScope savedScope
      (by simpa using arity)
  | state current next ih
  | unit represented typed next ih =>
    apply ih captureBound (by simp only [List.length_append,List.length_cons,List.length_nil] at arity ⊢; omega)
      external functionScope ?_ ?_ bodyIndependent
    · intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact savedScope a ha
      · rcases List.mem_singleton.mp ha with rfl
        exact actualScope _ (by simp)
    · exact fun a ha => actualScope a (by simp [ha])
  | @scalar ctx p value f vc vq core finalCtx finalInputs finalArgs sw nw cw qw rest saved
      valueSource annotation represented typed notState next ih =>
    have shifted (e : Lean.Expr) (scope_ok : LeanScalar.wellScoped bound e = true) :
        LeanScalar.wellScoped (bound+1) (LeanBindings.rename Nat.succ e) = true :=
      LeanBindings.rename_wellScoped e bound (bound+1) scope_ok Nat.succ (by intros; omega)
    have headScope : LeanScalar.wellScoped (bound+1)
        ((closureSubstitution capture (annotation.core::ctx).length captured []).apply functionValue) = true := by
      simp only [List.length_cons,FunctionSyntax.closureSubstitution_shift_empty captureBound 1]
      exact shifted _ functionScope
    have tail := ih (bound := bound+1) (by simp only [List.length_cons]; omega)
      (by simp only [List.length_append,List.length_map,List.length_cons,List.length_nil] at arity ⊢; omega)
      external.lift headScope
      (by
        intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · obtain ⟨original,member,rfl⟩ := List.mem_map.mp ha
          exact shifted _ (savedScope _ member)
        · have same : a = .bvar 0 := by simpa using ha
          subst a
          simp [LeanScalar.wellScoped])
      (by
        intro a ha
        obtain ⟨original,member,rfl⟩ := List.mem_map.mp ha
        exact shifted _ (actualScope _ (by simp [member]))) bodyIndependent
    have scalar := valueSource.independent external (actualScope value (by simp))
    intro i x y ls s
    simp only [scalar,tail]

theorem ArgumentBindings.install
    (arguments : ArgumentBindings (env := before) ctx p actuals saved
      finalCtx finalInputs finalArgs sourceWrap nativeWrap codeWrap quoteWrap)
    (installed : SignatureExtension before after) :
    ArgumentBindings (env := after) ctx p actuals saved
      finalCtx finalInputs finalArgs sourceWrap nativeWrap codeWrap quoteWrap := by
  induction arguments with
  | done => exact .done
  | state current next ih => exact .state current ih
  | unit represented typed next ih =>
    exact .unit represented (typed.install installed (fun _ _ _ h => SourceCasts.install h installed)) ih
  | scalar valueSource annotation represented typed notState next ih =>
    exact .scalar (valueSource.install installed) annotation represented
      (typed.install installed (fun _ _ _ h => SourceCasts.install h installed)) notState ih


/-- Construct one retained scalar binding from the existing source-only
scalar syntax. The value's code, native meaning, annotation and type evidence
are derived together, including Word/BitVec 32 aliasing. -/
theorem ArgumentBindings.scalarFromSyntax
    (library : ScalarSyntax.Library env) (decisions : Branch.BooleanLibrary env)
    (inputs : InputsTyped env ctx p) (typing : LexicalScalarCode.ScopeTyped env ctx p)
    (value : LexicalScalarSyntax.Form env ctx p [] actual)
    (static : LexicalScalarSyntax.StaticRegisters actual)
    (notState : sameTerm actual p.s = false)
    (next : ∀ annotation : WordBinder.Annotation,
      ∃ finalCtx finalInputs finalArgs sourceWrap nativeWrap codeWrap quoteWrap,
        ArgumentBindings (env := env) (annotation.core::ctx)
          {p.lift with locals := .bvar 0::p.lift.locals}
          (rest.map (LeanBindings.rename Nat.succ))
          ((saved.map (LeanBindings.rename Nat.succ)) ++ [.bvar 0])
          finalCtx finalInputs finalArgs sourceWrap nativeWrap codeWrap quoteWrap) :
    ∃ finalCtx finalInputs finalArgs sourceWrap nativeWrap codeWrap quoteWrap,
      ArgumentBindings (env := env) ctx p (actual::rest) saved
        finalCtx finalInputs finalArgs sourceWrap nativeWrap codeWrap quoteWrap := by
  obtain ⟨native,code,quotation,source⟩ := FixedScalarCompleteness.Scoped.fromSyntax value static
  obtain ⟨core,annotation,represented,typed,form⟩ := source.evidence library decisions inputs typing
  obtain ⟨finalCtx,finalInputs,finalArgs,sw,nw,cw,qw,tail⟩ := next annotation
  exact ⟨finalCtx,finalInputs,finalArgs,_,_,_,_,.scalar source annotation represented typed notState tail⟩

/-- Erase generated values from the existing argument telescope. This is an
existential projection, not a second grammar or a parser-success condition. -/
def ArgumentBindings.Syntax (env : VEnv) (ctx : List VExpr) (p : Inputs)
    (actuals saved : List Lean.Expr) (finalCtx : List VExpr) (finalInputs : Inputs)
    (finalArgs : List Lean.Expr) : Prop :=
  ∃ sourceWrap nativeWrap codeWrap quoteWrap,
    ArgumentBindings (env := env) ctx p actuals saved finalCtx finalInputs finalArgs
      sourceWrap nativeWrap codeWrap quoteWrap

theorem ArgumentBindings.syntax
    (arguments : ArgumentBindings (env := env) ctx p actuals saved
      finalCtx finalInputs finalArgs sourceWrap nativeWrap codeWrap quoteWrap) :
    ArgumentBindings.Syntax env ctx p actuals saved finalCtx finalInputs finalArgs :=
  ⟨_,_,_,_,arguments⟩

theorem ArgumentBindings.Syntax.install
    (arguments : ArgumentBindings.Syntax before ctx p actuals saved finalCtx finalInputs finalArgs)
    (installed : SignatureExtension before after) :
    ArgumentBindings.Syntax after ctx p actuals saved finalCtx finalInputs finalArgs := by
  obtain ⟨sw,nw,cw,qw,arguments⟩ := arguments
  exact (arguments.install installed).syntax

/-- One artifact-transport proof serves both the ordinary and retained
conversion branches. The conversion result is a local induction conclusion,
not an input-syntax or final generation-success premise. -/
theorem retargetRetainedPiece_of_conversion
    {piece : Piece env ctx p previous mode.expected}
    (expectedRep : Represents (mode.expected p piece.code source) expectedCore)
    (converted : ∃ cast, RetainedConversion.conversion conv exposure limit 0 ctx
      piece.checked.core.val expectedCore = some cast) :
    ∃ result, retargetRetainedPiece conv exposure limit mode source piece = some result ∧
      result.code = piece.code := by
  cases ordinary : retargetPiece conv mode source piece with
  | some result => exact ⟨result,retargetRetainedPiece_of_retarget piece ordinary,retargetPiece_code ordinary⟩
  | none =>
    obtain ⟨cast,converted⟩ := converted
    obtain ⟨⟨expected,represented⟩,translated,same⟩ := expectedRep.translate_complete
    dsimp only at same
    subst expected
    have checked : ∃ artifact, piece.checked.retarget
        (RetainedConversion.conversion conv exposure limit) (mode.expected p piece.code source) = some artifact := by
      unfold Artifact.retarget
      simp only [translated,bind,Option.bind]
      by_cases sameCore : piece.checked.core.val = expectedCore
      · simp only [dif_pos sameCore,pure,Option.pure_def]
        exact ⟨_,rfl⟩
      · simp only [dif_neg sameCore,converted,bind,Option.bind,pure,Option.pure_def]
        exact ⟨_,rfl⟩
    obtain ⟨artifact,checked⟩ := checked
    have fallback : ∃ result,
        retargetPiece (RetainedConversion.conversion conv exposure limit) mode source piece = some result := by
      simp only [retargetPiece,checked,bind,Option.bind,pure,Option.pure_def]
      exact ⟨_,rfl⟩
    obtain ⟨result,success⟩ := fallback
    exact ⟨result,by simp only [retargetRetainedPiece,ordinary,Option.orElse_none,success],
      retargetPiece_code success⟩

/-- Independently typed retained prefixes discharge the local conversion
obligation and transport the child's certificate without changing its code. -/
theorem retargetRetainedPiece_of_prefix {level : VLevel}
    {piece : Piece env ctx p previous mode.expected}
    (actualRep : Represents (mode.expected p piece.code previous) (.app head left))
    (expectedRep : Represents (mode.expected p piece.code source) (.app head right))
    {reduced : LeanTypeReduction.Result env 0 ctx right}
    (rightStep : LeanTypeReduction.step [] conv 0 ctx exposure right = some reduced)
    (chain : RetainedConversion.Prefix env 0 casts reduced.val.2 ctx left reduced.val.1 count)
    (closed : ClosedConstantTypes env) (stable : ClosedCasts casts)
    (resultClosed : reduced.val.2.ClosedN 0)
    (headTyped : CastTyping env 0 casts ctx head (.forallE reduced.val.2 codomain))
    (resultSort : codomain.inst left = .sort level)
    (coverage : Conversion.Covers conv 0 casts) (enough : count ≤ limit) :
    ∃ result, retargetRetainedPiece conv exposure limit mode source piece = some result ∧
      result.code = piece.code := by
  apply retargetRetainedPiece_of_conversion expectedRep
  rw [piece.checked.core.property.unique actualRep]
  exact RetainedConversion.conversion_of_prefix rightStep chain closed stable
    resultClosed headTyped resultSort coverage enough

/-- Checked source argument types and the retained-prefix derivation suffice
for the real call transport. In particular, neither reduction success nor
retarget success is a premise. The child piece comes from body induction. -/
theorem retargetRetainedPiece_checked_call {level : VLevel} {body : VExpr}
    {piece : Piece env ctx p previous mode.expected}
    (actualRep : Represents (mode.expected p piece.code previous) (.app head left))
    (expectedRep : Represents (mode.expected p piece.code source)
      (.app head (applications (.app (.lam domain body) first) args)))
    (bodyTyped : CastTyping env 0 casts (domain::ctx) body (domains.foldr VExpr.forallE resultType))
    (firstTyped : CheckedTyping env 0 casts ctx first domain)
    (arguments : List.Forall₂ (fun domain arg => CheckedTyping env 0 casts ctx arg domain) domains args)
    (typesClosed : ∀ n, ((domains.drop n).foldr VExpr.forallE resultType).ClosedN 0)
    (prefixTyped : ∀ before after, args = before ++ after → after ≠ [] →
      CastTyping env 0 casts ctx (before.foldl LeanTypeReduction.applyReduced (body.inst first))
        ((domains.drop before.length).foldr VExpr.forallE resultType))
    (chain : RetainedConversion.Prefix env 0 casts resultType ctx left
      (args.foldl LeanTypeReduction.applyReduced (body.inst first)) count)
    (closed : ClosedConstantTypes env) (stable : ClosedCasts casts)
    (resultClosed : resultType.ClosedN 0)
    (headTyped : CastTyping env 0 casts ctx head (.forallE resultType codomain))
    (resultSort : codomain.inst left = .sort level)
    (coverage : Conversion.Covers conv 0 casts) (exposure : Exposure env) (enough : count ≤ limit) :
    ∃ result, retargetRetainedPiece conv exposure limit mode source piece = some result ∧
      result.code = piece.code := by
  apply retargetRetainedPiece_of_conversion expectedRep
  rw [piece.checked.core.property.unique actualRep]
  exact RetainedConversion.conversion_checked_call bodyTyped firstTyped arguments typesClosed prefixTyped
    chain closed stable resultClosed headTyped resultSort coverage exposure enough

/-- Retained-call transport preserves the full certificate invariant, so its
result can be consumed by the existing enclosing binder/branch/loop rules. -/
theorem retargetRetainedPiece_typed_call {bodyCore domain first : VExpr} {rest domains : List VExpr}
    (setup : AliasSetup env) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (fresh : ScopedSyntax.Fresh setup)
    (exposure : Exposure env) (inputs : InputsTyped env ctx p)
    {piece : Piece env ctx p previous mode.expected}
    (child : RetainedCasts setup inputs mode previous piece)
    (domainTyped : CastTyping env 0 (SourceCasts env) ctx domain (.sort u))
    (bodyTyped : CastTyping env 0 (SourceCasts env) (domain::ctx) bodyCore
      (domains.foldr VExpr.forallE (optionType (if mode == .step then Step.stepState else stateType))))
    (firstTyped : CheckedTyping env 0 (SourceCasts env) ctx first domain)
    (arguments : List.Forall₂ (fun domain arg => CheckedTyping env 0 (SourceCasts env) ctx arg domain) domains rest)
    (typesClosed : ∀ n, ((domains.drop n).foldr VExpr.forallE
      (optionType (if mode == .step then Step.stepState else stateType))).ClosedN 0)
    (prefixTypes : ∀ before after, rest = before ++ after → after ≠ [] →
      CastTyping env 0 (SourceCasts env) ctx (before.foldl LeanTypeReduction.applyReduced (bodyCore.inst first))
        ((domains.drop before.length).foldr VExpr.forallE
          (optionType (if mode == .step then Step.stepState else stateType))))
    (sourceRep : Represents source (applications (.app (.lam domain bodyCore) first) rest))
    (retainedRep : Represents previous retained)
    (chain : RetainedConversion.Prefix env 0 (SourceCasts env)
      (optionType (if mode == .step then Step.stepState else stateType))
      ctx retained (rest.foldl LeanTypeReduction.applyReduced (bodyCore.inst first)) count) :
    ∃ result, retargetRetainedPiece setup.conversion exposure limit mode source piece = some result ∧
      RetainedCasts setup inputs mode source result ∧ result.code = piece.code := by
  have coverage := For.Casts.covered setup library.scalars.toSignatures library.steps closed
    library.cons library.eq library.eval fresh.state fresh.eq fresh.lift
  have initialClosed := typesClosed 0
  simp only [List.drop_zero] at initialClosed
  have sourceForm : ValueForm setup ctx (applications (.app (.lam domain bodyCore) first) rest)
      (optionType (if mode == .step then Step.stepState else stateType)) := by
    have initialForm : ValueForm setup ctx (.app (.lam domain bodyCore) first)
        (domains.foldr VExpr.forallE (optionType (if mode == .step then Step.stepState else stateType))) := by
      simpa only [initialClosed.instN_eq (Nat.zero_le _)] using
        (ValueForm.beta (setup := setup) bodyTyped (arg := first))
    exact initialForm.checkedArguments arguments typesClosed
  cases mode with
  | value => exact False.elim child
  | body =>
    obtain ⟨typed,form⟩ := child
    have same := retainedRep.unique typed.sourceCore.property
    subst retained
    obtain ⟨result,success,codeSame,⟨resultTyped⟩⟩ := StructuralSyntax.helper_retained_retarget_complete
      setup library.steps.state library.steps.option library.eq library.eval coverage inputs typed
      domainTyped bodyTyped firstTyped arguments typesClosed prefixTypes sourceRep chain
    refine ⟨result,retargetRetainedPiece_of_retarget piece success,⟨resultTyped,?_⟩,codeSame⟩
    exact (resultTyped.sourceCore.property.unique sourceRep).symm ▸ sourceForm
  | step =>
    obtain ⟨typed,form⟩ := child
    have same := retainedRep.unique typed.sourceCore.property
    subst retained
    obtain ⟨result,success,codeSame,⟨resultTyped⟩⟩ := FunctionSyntax.step_helper_retained_retarget_complete
      setup library.steps library.eq library.eval coverage inputs typed
      domainTyped bodyTyped firstTyped arguments typesClosed prefixTypes sourceRep chain
    refine ⟨result,retargetRetainedPiece_of_retarget piece success,⟨resultTyped,?_⟩,codeSame⟩
    exact (resultTyped.sourceCore.property.unique sourceRep).symm ▸ sourceForm

/-- Every successful retained-argument compilation still certifies the
original named Lean definition, rather than only an administrative rewrite.
This is meaning preservation after success; grammar-wide generation success
is a separate theorem and is not asserted here. -/
theorem compileRetained_correct (_success : compileRetained native name = some result) :
    LeanEnvironmentProvenance.Faithful native result.library.model ∧
    Represents (specification name result.code) result.proof.core.val ∧
    result.library.model.HasType 0 [] result.proof.proofCore.val result.proof.core.val := by
  exact result.correct

end IRComparison.WordFrontend.StructuralBody

namespace IRComparison.WordFrontend.FunctionSyntax
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic StructuralBody

/-- Retained lets and the original captured application have the same
structural endpoint, for arbitrary argument count and an arbitrary body.
The bound comes from the telescope, not from a successful conversion. -/
theorem BindingValue.retained_call_representations {body : Lean.Expr} {actuals : List Lean.Expr}
    (binding : BindingValue scope ctx.length σ head (.captured capture captured arity body functions))
    (coherent : scope.Coherent ctx.length σ)
    (spine : raw = actuals.foldl Lean.Expr.app head)
    (argumentsRep : List.Forall₂ Represents (actuals.map σ.apply) cores)
    (arityMatches : actuals.length = arity)
    (headRep : Represents (σ.apply head) functionCore)
    (arguments : ArgumentBindings (env := env) ctx p (actuals.map σ.apply) []
      finalCtx finalInputs finalArgs sourceWrap nativeWrap codeWrap quoteWrap)
    (retainedRep : Represents
      (sourceWrap ((closureSubstitution capture finalCtx.length captured finalArgs).apply body)) retainedCore) :
    RetainedConversion.contractCoreLets (finalCtx.length - ctx.length) retainedCore =
        some (cores.foldl LeanTypeReduction.applyReduced functionCore) ∧
      Represents (σ.apply raw) (applications functionCore cores) ∧
      finalCtx.length - ctx.length ≤ actuals.length := by
  obtain ⟨bound,rest⟩ := binding.sourceAt coherent
  obtain ⟨originalRep,callRep⟩ := binding.call_representations coherent spine argumentsRep arityMatches headRep
  have contracted := arguments.contract_represents bound captured body retainedRep
    (by simpa only [List.nil_append] using originalRep)
  refine ⟨contracted,callRep,?_⟩
  have growth := arguments.context_growth.2
  simp only [List.length_map] at growth
  omega

/-- The retained call is connected to the actual original-subterm traversal.
The argument and retarget premises are compositional obligations; callers
must discharge them from source syntax, not assume whole-parser success. -/
theorem BindingValue.retained_call_complete_with_transport
    (binding : BindingValue scope ctx.length σ fn.getAppFn closure)
    (modeAllowed : (mode == Mode.value) = false)
    {piece : Piece env ctx p retainedSource mode.expected}
    {result : Piece env ctx p (σ.apply (.app fn argument)) mode.expected}
    (arguments : retainArguments env conv exposure (closure.runtime env conv exposure)
      ctx p mode ((Lean.Expr.app fn argument).getAppArgs.toList.map σ.apply) [] =
        some ⟨retainedSource,piece⟩)
    (retargeted : retargetRetainedPiece conv exposure (Lean.Expr.app fn argument).getAppArgs.size
      mode (σ.apply (.app fn argument)) piece = some result) :
    visit env conv exposure (.app fn argument) ctx p mode σ
      (scope.runtime env conv exposure) = some result := by
  obtain ⟨function,found,functionValue⟩ := applicationHead_app fn argument
  have made := (functionValue.symm ▸ binding).construct function
    (env := env) (conv := conv) (exposure := exposure)
  rw [visit]
  simp only [node,modeAllowed,Bool.false_eq_true,ite_false,ite_true,letParts,found,made,arguments,
    bind,Option.bind,retargeted,pure,Option.pure_def]

/-- Compatibility wrapper for calls already handled by the ordinary converter. -/
theorem BindingValue.retained_call_complete
    (binding : BindingValue scope ctx.length σ fn.getAppFn closure)
    (modeAllowed : (mode == Mode.value) = false)
    {piece : Piece env ctx p retainedSource mode.expected}
    {result : Piece env ctx p (σ.apply (.app fn argument)) mode.expected}
    (arguments : retainArguments env conv exposure (closure.runtime env conv exposure)
      ctx p mode ((Lean.Expr.app fn argument).getAppArgs.toList.map σ.apply) [] =
        some ⟨retainedSource,piece⟩)
    (retargeted : retargetPiece conv mode (σ.apply (.app fn argument)) piece = some result) :
    visit env conv exposure (.app fn argument) ctx p mode σ
      (scope.runtime env conv exposure) = some result := by
  exact binding.retained_call_complete_with_transport modeAllowed arguments
    (retargetRetainedPiece_of_retarget piece retargeted)

/-- One compositional call rule for the Source induction. Its endpoint is the
induction hypothesis for the helper body; the argument telescope derives all
intermediate input environments and retained-prefix conditions. -/
theorem BindingValue.retained_call_from_body {body : Lean.Expr} {bodyCore domain first : VExpr}
    {rest domains : List VExpr}
    (fn argument : Lean.Expr) (modeAllowed : mode ≠ .value)
    (binding : BindingValue scope ctx.length σ fn.getAppFn (.captured depth bindings arity body functions))
    (coherent : scope.Coherent ctx.length σ)
    (arguments : ArgumentBindings (env := env) ctx p
      ((Lean.Expr.app fn argument).getAppArgs.toList.map σ.apply) []
      finalCtx finalInputs finalArgs sourceWrap nativeWrap codeWrap quoteWrap)
    (arityMatches : (Lean.Expr.app fn argument).getAppArgs.size = arity)
    (domainTyped : CastTyping env 0 (SourceCasts env) ctx domain (.sort u))
    (bodyTyped : CastTyping env 0 (SourceCasts env) (domain::ctx) bodyCore
      (domains.foldr VExpr.forallE (optionType (if mode == .step then Step.stepState else stateType))))
    (firstTyped : CheckedTyping env 0 (SourceCasts env) ctx first domain)
    (argumentTypes : List.Forall₂ (fun domain arg => CheckedTyping env 0 (SourceCasts env) ctx arg domain) domains rest)
    (typesClosed : ∀ n, ((domains.drop n).foldr VExpr.forallE
      (optionType (if mode == .step then Step.stepState else stateType))).ClosedN 0)
    (prefixTypes : ∀ before after, rest = before ++ after → after ≠ [] →
      CastTyping env 0 (SourceCasts env) ctx (before.foldl LeanTypeReduction.applyReduced (bodyCore.inst first))
        ((domains.drop before.length).foldr VExpr.forallE
          (optionType (if mode == .step then Step.stepState else stateType))))
    (reducedRep : Represents
      ((closureSubstitution depth ctx.length bindings
        ((Lean.Expr.app fn argument).getAppArgs.toList.map σ.apply)).apply body)
      (rest.foldl LeanTypeReduction.applyReduced (bodyCore.inst first)))
    (sourceRep : Represents (σ.apply (.app fn argument))
      (applications (.app (.lam domain bodyCore) first) rest))
    (setup : AliasSetup env) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (fresh : ScopedSyntax.Fresh setup)
    (exposure : Exposure env) (inputs : InputsTyped env ctx p) (locals : ScalarSyntax.Locals env ctx p)
    (endpoint : ∀ finalTyped : InputsTyped env finalCtx finalInputs,
      ScalarSyntax.Locals env finalCtx finalInputs →
      ∃ piece, visit env setup.conversion exposure body finalCtx finalInputs mode
        (closureSubstitution depth finalCtx.length bindings finalArgs)
        ((functions.parameters finalArgs.length).runtime env setup.conversion exposure) = some piece ∧
        RetainedCasts setup finalTyped mode
          ((closureSubstitution depth finalCtx.length bindings finalArgs).apply body) piece ∧
        piece.code = quotation) :
    ∃ piece, visit env setup.conversion exposure (.app fn argument) ctx p mode σ
        (scope.runtime env setup.conversion exposure) = some piece ∧
      RetainedCasts setup inputs mode (σ.apply (.app fn argument)) piece ∧ piece.code = quoteWrap quotation := by
  have arityFinal : finalArgs.length = arity := by
    have count := arguments.argument_count
    simpa only [List.length_nil,Nat.zero_add,List.length_map,Array.length_toList,arityMatches] using count
  obtain ⟨child,parsed,childCasts,childCode⟩ := arguments.complete setup library closed fresh exposure inputs locals
    ((Closure.captured depth bindings arity body functions).runtime env setup.conversion exposure) mode (by
      intro finalTyped finalLocals
      obtain ⟨piece,success,typed,codeSame⟩ := endpoint finalTyped finalLocals
      refine ⟨piece,?_,typed,codeSame⟩
      simp only [Scope.runtime_parameters,arityFinal] at success
      simp only [Closure.runtime,arityFinal,bne_self_eq_false,Bool.false_eq_true,ite_false,
        success,bind,Option.bind,pure,Option.pure_def])
  obtain ⟨⟨finalTyped⟩,⟨finalLocals⟩⟩ := arguments.endpointInputs library closed inputs locals
  obtain ⟨last,_,lastCasts,_⟩ := endpoint finalTyped finalLocals
  have endpointType : ∃ core,
      Represents ((closureSubstitution depth finalCtx.length bindings finalArgs).apply body) core ∧
      CastTyping env 0 (SourceCasts env) finalCtx core
        (optionType (if mode == .step then Step.stepState else stateType)) := by
    cases mode with
    | value => exact False.elim (modeAllowed rfl)
    | body | step =>
      obtain ⟨typed,form⟩ := lastCasts
      exact ⟨typed.sourceCore.val,typed.sourceCore.property,typed.value⟩
  obtain ⟨core,bodyRep,typed⟩ := endpointType
  obtain ⟨retained,original,retainedRep,originalRep,chain⟩ := arguments.prefix
    library.scalars.toSignatures (binding.sourceAt coherent).1 bindings body bodyRep typed
  have originalSame := originalRep.unique (by simpa only [List.nil_append] using reducedRep)
  subst original
  obtain ⟨result,retargeted,resultCasts,codeSame⟩ := retargetRetainedPiece_typed_call
    setup library closed fresh exposure inputs childCasts domainTyped bodyTyped firstTyped argumentTypes
    typesClosed prefixTypes sourceRep retainedRep chain
    (limit := (Lean.Expr.app fn argument).getAppArgs.size)
  exact ⟨result,binding.retained_call_complete_with_transport
    (by cases mode <;> first | rfl | exact False.elim (modeAllowed rfl)) parsed retargeted,
    resultCasts,codeSame.trans childCode⟩


end IRComparison.WordFrontend.FunctionSyntax

namespace IRComparison.WordFrontend.StructuralBody
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic
set_option maxHeartbeats 2400000

/-- Build the entire retained argument telescope from ordinary source
arguments. Argument count is arbitrary; State and Unit are passed through,
scalars are saved in source order. Later scalar expressions are weakened by
one shared syntax induction, not proved again at each call site. -/
theorem ArgumentBindings.fromSyntax
    (library : ScopedSyntax.Library env) (closed : ClosedConstantTypes env)
    (inputs : InputsTyped env ctx p) (typing : LexicalScalarCode.ScopeTyped env ctx p)
    (references : ScalarSyntax.ReferenceScope p)
    (arguments : ∀ raw ∈ actuals,
      raw = p.s ∨
      (∃ core, Represents raw core ∧ CastTyping env 0 (SourceCasts env) ctx core UnitStep.unitType) ∨
      (LexicalScalarSyntax.Form env ctx p [] raw ∧ LexicalScalarSyntax.StaticRegisters raw ∧ sameTerm raw p.s = false))
    (saved : List Lean.Expr) :
    ∃ finalCtx finalInputs finalArgs,
      ArgumentBindings.Syntax env ctx p actuals saved finalCtx finalInputs finalArgs := by
  cases actuals with
  | nil => exact ⟨ctx,p,saved,ArgumentBindings.done.syntax⟩
  | cons raw rest =>
    have tail := fun r hr => arguments r (List.mem_cons_of_mem _ hr)
    rcases arguments raw (by simp) with current | ⟨core,rep,typed⟩ | ⟨form,static,notState⟩
    · obtain ⟨fc,fp,fa,sw,nw,cw,qw,next⟩ := ArgumentBindings.fromSyntax library closed inputs typing references tail (saved ++ [raw])
      exact ⟨fc,fp,fa,(ArgumentBindings.state current next).syntax⟩
    · obtain ⟨fc,fp,fa,sw,nw,cw,qw,next⟩ := ArgumentBindings.fromSyntax library closed inputs typing references tail (saved ++ [raw])
      exact ⟨fc,fp,fa,(ArgumentBindings.unit rep typed next).syntax⟩
    · obtain ⟨f,c,q,source⟩ := FixedScalarCompleteness.Scoped.fromSyntax form static
      obtain ⟨core,a,rep,typed,shape⟩ := source.evidence library.scalars library.decisions inputs typing
      have nextInputs := a.nextInputs inputs closed library.scalars.toSignatures library.cons
      have lifted : ∀ r ∈ rest.map (LeanBindings.rename Nat.succ),
          r = ({p.lift with locals := .bvar 0::p.lift.locals} : Inputs).s ∨
          (∃ core, Represents r core ∧ CastTyping env 0 (SourceCasts env) (a.core::ctx) core UnitStep.unitType) ∨
          (LexicalScalarSyntax.Form env (a.core::ctx) {p.lift with locals := .bvar 0::p.lift.locals} [] r ∧
            LexicalScalarSyntax.StaticRegisters r ∧ sameTerm r p.lift.s = false) := by
        intro r hr
        obtain ⟨original,member,rfl⟩ := List.mem_map.mp hr
        rcases tail original member with rfl | ⟨oc,orr,ott⟩ | ⟨ofm,ost,ons⟩
        · exact Or.inl rfl
        · exact Or.inr (Or.inl ⟨oc.lift,orr.lift,by
            simpa only [UnitStep.unitType,VExpr.lift,VExpr.liftN] using ott.lift closed SourceCasts.closed a.core⟩)
        · have liftedForm := ofm.liftScalar closed inputs typing references a.core
          have liftedSource : LexicalScalarSyntax.Form env (a.core::ctx)
              {p.lift with locals := .bvar 0::p.lift.locals} [] (LeanBindings.rename Nat.succ original) := by
            simpa only [List.map_nil,List.length_nil,liftVar,Nat.not_lt_zero,ite_false,Nat.one_add] using liftedForm
          obtain ⟨oc,oa,orr,ott,osh⟩ := ofm.evidence ost library.scalars library.decisions inputs typing (by simp)
          simp only [LexicalScalarSyntax.expand_nil] at orr
          exact Or.inr (Or.inr ⟨liftedSource,ost.rename Nat.succ,by
            simpa only [Inputs.lift,LexicalScalarSyntax.expand_nil,
              LexicalScalarSyntax.sameTerm_lift orr inputs.s.property] using ons⟩)
      obtain ⟨fc,fp,fa,sw,nw,cw,qw,next⟩ := ArgumentBindings.fromSyntax library closed
        nextInputs (typing.nextWord closed a) references.scalar lifted
        (saved.map (LeanBindings.rename Nat.succ) ++ [.bvar 0])
      exact ⟨fc,fp,fa,(ArgumentBindings.scalar source a rep typed notState next).syntax⟩
termination_by actuals.length

end IRComparison.WordFrontend.StructuralBody

namespace IRComparison.WordFrontend.StructuralBody
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic

/-- The source reference/type invariants follow the same argument telescope
as the generated input context. No call site must reconstruct them. -/
theorem ArgumentBindings.endpointScope
    (arguments : ArgumentBindings (env := env) ctx p actuals saved
      finalCtx finalInputs finalArgs sw nw cw qw)
    (closed : ClosedConstantTypes env) (typing : LexicalScalarCode.ScopeTyped env ctx p)
    (references : ScalarSyntax.ReferenceScope p) :
    LexicalScalarCode.ScopeTyped env finalCtx finalInputs ∧ ScalarSyntax.ReferenceScope finalInputs := by
  induction arguments with
  | done => exact ⟨typing,references⟩
  | state _ _ ih | unit _ _ _ ih => exact ih typing references
  | scalar _ a _ _ _ _ ih => exact ih (typing.nextWord closed a) references.scalar

end IRComparison.WordFrontend.StructuralBody
