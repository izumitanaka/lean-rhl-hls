import IRComparison.Frontend.WordOrdinarySourceArguments

/-! Internal interpretation of lexical helper bindings. These specifications
are constructed by the original-source induction; they are not premises of
the public source grammar. A captured helper can be called after later value,
read, State or iterator binders without re-supplying its original body. -/
namespace IRComparison.WordFrontend.OrdinarySource
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic StructuralBody ScalarSyntax
set_option maxHeartbeats 2400000

/-- All actuals retain their independently inferred types. This is internal
proof data obtained from Arguments.evidenceMapped, not a type-check success. -/
def ActualTypes (env : VEnv) (ctx : List VExpr) (actual : List Parameter)
    (operands : List Lean.Expr) : Prop :=
  List.Forall₂ (fun parameter raw => ∃ core, Represents raw core ∧
    CastTyping env 0 (SourceCasts env) ctx core parameter.core) actual operands

def closureArity : FunctionSyntax.Closure → Nat
  | .captured _ _ arity _ _ => arity

/-- The common payload used by the existing retained-call rule. It contains
only derived internal evidence; the one original helper body supplies its
front types and its retained continuation. -/
def PreparedCall (env : VEnv) (ds : FixedMemory.Declarations)
    (closure : FunctionSyntax.Closure) (signature : Signature)
    (ctx : List VExpr) (functionValue : Lean.Expr) (actual : List Parameter)
    (finalCtx : List VExpr) (finalInputs : Inputs) (finalArgs : List Lean.Expr) : Prop :=
  match closure with
  | .captured depth captured _ body functions =>
    ∃ coreBody,
      Represents functionValue ((signature.domains.map Parameter.core).foldr VExpr.lam coreBody) ∧
      (∀ n, CastTyping env 0 (SourceCasts env)
        (((actual.take n ++ signature.domains.drop n).map Parameter.core).reverse ++ ctx)
        coreBody (optionType signature.result.core)) ∧
      FunctionSyntax.Syntax env (mode := signature.result.mode)
        finalCtx finalInputs (closureSubstitution depth finalCtx.length captured finalArgs)
        (functions.parameters finalArgs.length) body (FixedSequenceCompleteness.InputConditions ds)

/-- A helper's meaning persists under later target binders. Demands are
captured State references, not scalar expressions to be evaluated later.
Only an actual invocation requires those State references to be current. -/
structure FunctionMeaning (env : VEnv) (ds : FixedMemory.Declarations)
    (ctx : List VExpr) (p : Inputs) (closure : FunctionSyntax.Closure)
    (signature : Signature) (native : Lean.Expr) (demands : List Lean.Expr) : Prop where
  nonempty : signature.domains ≠ []
  arity : closureArity closure = signature.domains.length
  prepare : ∀ (path : List Parameter) {operands actual finalCtx finalInputs finalArgs},
    List.Forall₂ Parameter.Related signature.domains actual →
    ActualTypes env (targetContext path ctx) actual operands →
    List.Forall₂ (fun parameter raw => parameter = .unit →
      LexicalScalarSyntax.StaticRegisters raw ∧ raw.getAppFn.constName? ≠ some ``HybridWord.State.regs) actual operands →
    ArgumentBindings.Syntax env (targetContext path ctx) (targetInputs path p)
      operands [] finalCtx finalInputs finalArgs →
    (∀ value ∈ demands, LeanBindings.rename (·+path.length) value = (targetInputs path p).s) →
    PreparedCall env ds closure signature (targetContext path ctx)
      (LeanBindings.rename (·+path.length) native) actual finalCtx finalInputs finalArgs

/-- Extending the target stack composes the existing binder lists. It does
not inspect the helper body again or construct another source derivation. -/
theorem FunctionMeaning.extend
    (meaning : FunctionMeaning env ds ctx p closure signature native demands)
    (front : List Parameter) :
    FunctionMeaning env ds (targetContext front ctx) (targetInputs front p) closure signature
      (LeanBindings.rename (·+front.length) native)
      (demands.map (LeanBindings.rename (·+front.length))) := by
  refine ⟨meaning.nonempty,meaning.arity,?_⟩
  intro path operands actual finalCtx finalInputs finalArgs relation types unitSafe bindings current
  have joinedTypes : ActualTypes env (targetContext (front++path) ctx) actual operands := by
    simpa only [targetContext_append] using types
  have joinedBindings : ArgumentBindings.Syntax env (targetContext (front++path) ctx)
      (targetInputs (front++path) p) operands [] finalCtx finalInputs finalArgs := by
    simpa only [targetContext_append,targetInputs_append] using bindings
  have renamed (value : Lean.Expr) :
      LeanBindings.rename (·+path.length) (LeanBindings.rename (·+front.length) value) =
      LeanBindings.rename (·+(front++path).length) value := by
    rw [LeanBindings.rename_comp]
    congr 1
    funext n
    simp only [Function.comp_apply,List.length_append,Nat.add_assoc]
  have demand : ∀ value ∈ demands,
      LeanBindings.rename (·+(front++path).length) value = (targetInputs (front++path) p).s := by
    intro value member
    simpa only [renamed,targetInputs_append] using current _ (List.mem_map.mpr ⟨value,member,rfl⟩)
  simpa only [targetContext_append,← renamed] using
    meaning.prepare (front++path) relation joinedTypes unitSafe joinedBindings demand

/-- The lexical environment associates each original function slot with its
captured meaning. Its State demands are those computed by original Flow. -/
def FunctionEnvironment (env : VEnv) (ds : FixedMemory.Declarations)
    (Γ : Context) (effects : EffectScope) (ctx : List VExpr) (p : Inputs)
    (σ : Substitution) (scope : FunctionSyntax.Scope) : Prop :=
  ∀ index signature requires, Γ[index]? = some (.function signature) →
    effects[index]? = some (some requires) →
    ∃ closure, scope.lookup index = some closure ∧
      FunctionMeaning env ds ctx p closure signature (σ.reference index) (requires.map σ.reference)

/-- A target extension keeps the original lexical scope and shifts its stored
references. Repeated calls share the same interpretation proof. -/
theorem FunctionEnvironment.extendTarget
    (functions : FunctionEnvironment env ds Γ effects ctx p σ scope) (path : List Parameter) :
    FunctionEnvironment env ds Γ effects (targetContext path ctx) (targetInputs path p)
      (.bindings (fun n => LeanBindings.rename (·+path.length) (σ.reference n))) scope := by
  intro index signature requires found effectsFound
  obtain ⟨closure,lookup,meaning⟩ := functions index signature requires found effectsFound
  refine ⟨closure,lookup,?_⟩
  simpa only [Substitution.reference,List.map_map,Function.comp_def] using meaning.extend path

/-- Adding an original value slot only shifts lexical helper lookup. The
physical target extension is handled once by extendTarget. -/
theorem FunctionEnvironment.pushValue
    (functions : FunctionEnvironment env ds Γ effects ctx p σ scope)
    (parameter : Parameter) (same : ∀ n, next.reference (n+1) = σ.reference n) :
    FunctionEnvironment env ds (.value parameter::Γ) (bindEffects effects) ctx p next (.push none scope) := by
  intro index signature requires found effectsFound
  cases index with
  | zero => cases found
  | succ index =>
    cases present : effects[index]? with
    | none => simp [bindEffects,liftEffects,List.getElem?_map,present] at effectsFound
    | some entry =>
      cases entry with
      | none => simp [bindEffects,liftEffects,List.getElem?_map,present] at effectsFound
      | some original =>
        have equal : original.map (fun i => i+1) = requires := by
          simpa [bindEffects,liftEffects,List.getElem?_map,present] using effectsFound
        subst requires
        obtain ⟨closure,lookup,meaning⟩ := functions index signature original found present
        refine ⟨closure,lookup,?_⟩
        simpa only [same,List.map_map,Function.comp_def] using meaning

/-- Every ordinary value/State/read/loop binder follows this same extension
rule. The callable promise moves with its captured values. -/
theorem FunctionEnvironment.under
    (functions : FunctionEnvironment env ds Γ effects ctx p σ scope) (parameter : Parameter) :
    FunctionEnvironment env ds (.value parameter::Γ) (bindEffects effects)
      (parameter.core::ctx) (parameter.extendInputs p) (under σ) (.push none scope) := by
  apply (functions.extendTarget [parameter]).pushValue parameter
  intro n
  rw [under_reference]
  rfl

/-- Function declarations and aliases install the already constructed helper
meaning. The old slots need no new body derivations. -/
theorem FunctionEnvironment.bindFunction
    (functions : FunctionEnvironment env ds Γ effects ctx p σ scope)
    (meaning : FunctionMeaning env ds ctx p closure signature (σ.apply value) (requires.map σ.reference)) :
    FunctionEnvironment env ds (.function signature::Γ) (bindFunctionEffects requires effects)
      ctx p (letSubstitution σ value) (.push (some closure) scope) := by
  intro index sig demands found effectsFound
  cases index with
  | zero =>
    have eqSig : signature = sig := by simpa using found
    subst sig
    have eqDemands : requires.map Nat.succ = demands := by simpa [bindFunctionEffects] using effectsFound
    subst demands
    refine ⟨closure,rfl,?_⟩
    simpa only [List.map_map,Function.comp_def,Substitution.reference,letSubstitution] using meaning
  | succ index =>
    cases present : effects[index]? with
    | none => simp [bindFunctionEffects,liftEffects,List.getElem?_map,present] at effectsFound
    | some entry =>
      cases entry with
      | none => simp [bindFunctionEffects,liftEffects,List.getElem?_map,present] at effectsFound
      | some original =>
        have equal : original.map (fun i => i+1) = demands := by
          simpa [bindFunctionEffects,liftEffects,List.getElem?_map,present] using effectsFound
        subst demands
        obtain ⟨c,lookup,old⟩ := functions index sig original found present
        refine ⟨c,lookup,?_⟩
        simpa only [List.map_map,Function.comp_def,Substitution.reference,letSubstitution] using old

/-- Formal parameters shadow function slots without changing the captured
helpers. This is also used after retaining a mixed State/scalar argument list. -/
theorem FunctionEnvironment.parameters
    (functions : FunctionEnvironment env ds Γ effects ctx p σ scope)
    (parameters : List Parameter)
    (outer : ∀ n, next.reference (n+parameters.length) = σ.reference n) :
    FunctionEnvironment env ds (parameters.reverse.map Slot.value ++ Γ)
      (parameterEffects parameters.length effects) ctx p next (scope.parameters parameters.length) := by
  intro index signature requires found effectsFound
  by_cases inside : index < parameters.length
  · simp only [List.getElem?_append,List.length_map,List.length_reverse,inside,ite_true,List.getElem?_map] at found
    cases selected : parameters.reverse[index]? with
    | none => simp [selected] at found
    | some parameter => simp [selected] at found
  · have sourceSlot : Γ[index-parameters.length]? = some (.function signature) := by
      simpa only [List.getElem?_append,List.length_map,List.length_reverse,inside,ite_false] using found
    cases present : effects[index-parameters.length]? with
    | none => simp [parameterEffects,liftEffects,List.getElem?_append,inside,List.getElem?_map,present] at effectsFound
    | some entry =>
      cases entry with
      | none => simp [parameterEffects,liftEffects,List.getElem?_append,inside,List.getElem?_map,present] at effectsFound
      | some original =>
        have equal : original.map (fun i => i+parameters.length) = requires := by
          simpa [parameterEffects,liftEffects,List.getElem?_append,inside,List.getElem?_map,present] using effectsFound
        subst requires
        obtain ⟨closure,lookup,meaning⟩ := functions _ signature original sourceSlot present
        refine ⟨closure,?_,?_⟩
        · simpa only [FunctionSyntax.Scope.lookup_parameters,inside,ite_false] using lookup
        · have ref : next.reference index = σ.reference (index-parameters.length) := by
            simpa only [Nat.sub_add_cancel (Nat.le_of_not_gt inside)] using outer (index-parameters.length)
          simpa only [List.map_map,Function.comp_def,outer,ref] using meaning

/-- Captures at a later target stack are the same source lexical values,
shifted by the number of introduced binders. -/
theorem FunctionEnvironment.captureExtension
    (functions : FunctionEnvironment env ds Γ effects ctx p σ scope) (path : List Parameter) :
    FunctionEnvironment env ds Γ effects (targetContext path ctx) (targetInputs path p)
      (closureSubstitution ctx.length (targetContext path ctx).length σ []) scope := by
  have same : closureSubstitution ctx.length (targetContext path ctx).length σ [] =
      .bindings (fun n => LeanBindings.rename (·+path.length) (σ.reference n)) := by
    apply congrArg Substitution.bindings
    funext n
    simp only [closureReference,List.reverse_nil,List.getElem?_nil,List.length_nil,
      Nat.sub_zero,targetContext_length,Nat.add_sub_cancel_left]
  rw [same]
  exact functions.extendTarget path

/-- Invoke a constructed helper meaning through the existing certified call
rule. All body and front-type evidence comes from prepare; the call site
supplies only its independently derived operand types and representations. -/
theorem FunctionMeaning.invoke {arity : Nat} {body : Lean.Expr}
    (meaning : FunctionMeaning env ds ctx p (.captured depth captured arity body functions)
      ⟨head::tail,result⟩ native demands)
    (library : ScopedSyntax.Library env) (closed : ClosedConstantTypes env)
    (fn argument : Lean.Expr) (coherent : scope.Coherent ctx.length σ)
    (binding : FunctionSyntax.BindingValue scope ctx.length σ fn.getAppFn
      (.captured depth captured arity body functions))
    (nativeSame : σ.apply fn.getAppFn = native)
    (relation : List.Forall₂ Parameter.Related (head::tail) actual)
    (types : List.Forall₂ (fun (parameter : Parameter) core =>
      CastTyping env 0 (SourceCasts env) ctx core parameter.core) actual cores)
    (checks : List.Forall₂ (fun (parameter : Parameter) core =>
      CheckedTyping env 0 (SourceCasts env) ctx core parameter.core) (head::tail) cores)
    (represented : List.Forall₂ Represents
      ((Lean.Expr.app fn argument).getAppArgs.toList.map σ.apply) cores)
    (unitSafe : List.Forall₂ (fun parameter raw => parameter = .unit →
      LexicalScalarSyntax.StaticRegisters raw ∧ raw.getAppFn.constName? ≠ some ``HybridWord.State.regs)
      actual ((Lean.Expr.app fn argument).getAppArgs.toList.map σ.apply))
    (retained : ArgumentBindings.Syntax env ctx p
      ((Lean.Expr.app fn argument).getAppArgs.toList.map σ.apply) [] finalCtx finalInputs finalArgs)
    (current : ∀ value ∈ demands, value = p.s) :
    FunctionSyntax.Syntax env (mode := result.mode) ctx p σ scope
      (.app fn argument) (FixedSequenceCompleteness.InputConditions ds) := by
  have count := checks.length_eq
  cases cores with
  | nil => simp at count
  | cons first rest =>
    have actualTypes : ActualTypes env ctx actual
        ((Lean.Expr.app fn argument).getAppArgs.toList.map σ.apply) := by
      have combine {ps : List Parameter} {rs : List Lean.Expr} {cs : List VExpr}
          (typed : List.Forall₂ (fun parameter core => CastTyping env 0 (SourceCasts env) ctx core parameter.core) ps cs)
          (reps : List.Forall₂ Represents rs cs) : ActualTypes env ctx ps rs := by
        induction typed generalizing rs with
        | nil => cases reps; exact .nil
        | cons ht tt ih =>
          cases reps with
          | cons hr tr => exact .cons ⟨_,hr,ht⟩ (ih tr)
      exact combine types represented
    have ready := meaning.prepare [] relation actualTypes unitSafe retained
      (by change ∀ value ∈ demands, LeanBindings.rename id value = p.s
          simpa only [LeanBindings.rename_id] using current)
    obtain ⟨bodyCore,fnRep,bodyTypes,next⟩ := ready
    change Represents (LeanBindings.rename id native) _ at fnRep
    rw [LeanBindings.rename_id] at fnRep
    simp only [targetContext] at bodyTypes
    have length : ((Lean.Expr.app fn argument).getAppArgs.toList.map σ.apply).length = arity :=
      represented.length_eq.trans (count.symm.trans meaning.arity.symm)
    have declaredChecks : List.Forall₂ (fun ty arg => CheckedTyping env 0 (SourceCasts env) ctx arg ty)
        ((head::tail).map Parameter.core) (first::rest) := List.forall₂_map_left_iff.mpr checks
    refine FunctionSyntax.Syntax.retainedCallFromBodyTypes (coreBody := bodyCore) (domain := head.core)
      (tailDomains := tail.map Parameter.core) (actual := actual.map Parameter.core) library closed fn argument
      (by cases result <;> simp [Result.mode]) coherent binding length retained next
      (List.forall₂_map_left_iff.mpr types) declaredChecks
      (by simpa only [List.length_cons,List.length_map] using count) ?_ ?_ represented ?_
    · intro domain member
      have params (ps : List Parameter) : ∀ d ∈ ps.map Parameter.core,
          ∃ u, CastTyping env 0 (SourceCasts env) [] d (.sort u) := by
        intro d member
        obtain ⟨parameter,_,rfl⟩ := List.mem_map.mp member
        exact ⟨_,(parameter.typed library).withCasts _⟩
      rcases List.mem_append.mp member with declared | inferred
      · exact params (head::tail) domain declared
      · exact params actual domain inferred
    · intro n hn
      have eq : FunctionSyntax.sourceResultType result.mode = optionType result.core := by cases result <;> rfl
      rw [eq]
      simpa only [List.map_append,List.map_take,List.map_drop,List.map_cons] using bodyTypes n
    · rw [nativeSame]
      exact fnRep

/-- Induction conclusion for an original body, not an additional source
judgment. All compiler environments below are internal interpretations of its
original lexical context and are constructed by the enclosing binding rule. -/
def BodyMeaning (env : VEnv) (ds : FixedMemory.Declarations) (Γ : Context)
    (result : Result) (raw : Lean.Expr) (effects : EffectScope) (requires : List Nat) : Prop :=
  ∀ {Δ ctx p σ τ scope}, Context.Related Γ Δ → ScalarFrame env Δ ctx p σ τ →
    (library : ScopedSyntax.Library env) → ClosedConstantTypes env →
    InputsTyped env ctx p → LexicalScalarCode.ScopeTyped env ctx p → ReferenceScope p →
    (∃ index, p.s = .bvar index) → RegisterMapping σ → scope.Coherent ctx.length σ →
    FunctionEnvironment env ds Γ effects ctx p σ scope → CurrentMapping σ p requires →
    FunctionSyntax.Syntax env (mode := result.mode) ctx p σ scope raw
      (FixedSequenceCompleteness.InputConditions ds)

private theorem parameterContexts (relation : List.Forall₂ Parameter.Related declared actual) :
    Context.Related (declared.reverse.map Slot.value) (actual.reverse.map Slot.value) := by
  have mapped : Context.Related (declared.map Slot.value) (actual.map Slot.value) := by
    induction relation with
    | nil => exact .nil
    | cons head tail ih => exact .cons head ih
  simpa only [List.map_reverse] using List.Forall₂.reverse.mpr mapped

private theorem capture_apply (depth amount : Nat) (σ : Substitution) (raw : Lean.Expr) :
    (closureSubstitution depth (depth+amount) σ []).apply raw =
      LeanBindings.rename (·+amount) (σ.apply raw) := by
  rw [FunctionSyntax.closureSubstitution_shift_empty (Nat.le_refl depth),
    FunctionSyntax.closureSubstitution_at_capture]

/-- A helper declaration constructs its callable meaning from the induction
hypothesis for its one original body. Retained-body syntax, prefix types,
current-State correspondence and closure environments are all derived here. -/
theorem FunctionMeaning.ofLambda {body : Lean.Expr}
    (source : Body ds ((head::tail).reverse.map Slot.value ++ Γ) result body)
    (shape : LambdaSource native ((head::tail).map Parameter.native) body)
    (bodyMeaning : BodyMeaning env ds ((head::tail).reverse.map Slot.value ++ Γ) result body
      (parameterEffects (head::tail).length effects) requires)
    (demandsTyped : DemandsTyped ((head::tail).reverse.map Slot.value ++ Γ) requires)
    (related : Context.Related Γ Δ) (frame : ScalarFrame env Δ ctx p σ τ)
    (library : ScopedSyntax.Library env) (closed : ClosedConstantTypes env)
    (inputs : InputsTyped env ctx p) (typing : LexicalScalarCode.ScopeTyped env ctx p)
    (references : ReferenceScope p) (stateReference : ∃ index, p.s = .bvar index)
    (registers : RegisterMapping σ) (coherent : scope.Coherent ctx.length σ)
    (functions : FunctionEnvironment env ds Γ effects ctx p σ scope) :
    FunctionMeaning env ds ctx p (.captured ctx.length σ (head::tail).length body scope)
      ⟨head::tail,result⟩ (σ.apply native)
      ((outerDemands (head::tail).length requires).map σ.reference) := by
  refine ⟨by simp,rfl,?_⟩
  intro path operands actual finalCtx finalInputs finalArgs relation types unitSafe bindings current
  obtain ⟨⟨pathInputs⟩,pathTyping,pathReferences,pathState⟩ := targetTyped path library closed inputs typing references stateReference
  obtain ⟨pathTypes,pathFrame⟩ := frame.atCapture.captureExtension path (Nat.le_refl _) library closed inputs typing references
  have bound : ctx.length ≤ (targetContext path ctx).length := by rw [targetContext_length]; omega
  obtain ⟨sw,nw,cw,qw,args⟩ := bindings
  obtain ⟨finalTypes,finalFrame,links,retainedPath,finalContext,finalParameters,finalSafe⟩ :=
    ArgumentBindings.heldEnvironment args library closed pathInputs pathTyping pathReferences pathState
      types bound pathFrame unitSafe (by simp)
  obtain ⟨⟨finalTyped⟩,finalScopeTyped,finalReferences,finalState⟩ :=
    targetTyped retainedPath library closed pathInputs pathTyping pathReferences pathState
  rw [← finalContext] at finalTyped finalScopeTyped
  rw [← finalParameters] at finalTyped finalScopeTyped finalReferences finalState
  have count : finalArgs.length = (head::tail).length := by
    have n := args.argument_count
    have actualLength := types.length_eq
    have declaredLength := relation.length_eq
    simpa only [List.length_nil,Nat.zero_add,← actualLength,← declaredLength] using n
  have bodyRelated : Context.Related ((head::tail).reverse.map Slot.value ++ Γ)
      (actual.reverse.map Slot.value ++ Δ) := (parameterContexts relation).append related
  have currentCaptures : CurrentMapping (closureSubstitution ctx.length (targetContext path ctx).length σ [])
      (targetInputs path p) (outerDemands actual.length requires) := by
    intro n member
    have present : σ.reference n ∈ (outerDemands (head::tail).length requires).map σ.reference :=
      List.mem_map.mpr ⟨n,by simpa only [relation.length_eq] using member,rfl⟩
    simpa only [Substitution.reference,closureSubstitution,closureReference,List.reverse_nil,
      List.getElem?_nil,List.length_nil,Nat.sub_zero,targetContext_length,Nat.add_sub_cancel_left]
      using current _ present
  have finalCurrent := links.current (demandsTyped.retag bodyRelated) currentCaptures
  have finalFunctions : FunctionEnvironment env ds Γ effects finalCtx finalInputs
      (closureSubstitution ctx.length finalCtx.length σ []) scope := by
    simpa only [targetContext_append,targetInputs_append,← finalContext,← finalParameters] using
      functions.captureExtension (path++retainedPath)
  have helpers : FunctionEnvironment env ds ((head::tail).reverse.map Slot.value ++ Γ)
      (parameterEffects (head::tail).length effects) finalCtx finalInputs
      (closureSubstitution ctx.length finalCtx.length σ finalArgs) (scope.parameters finalArgs.length) := by
    rw [count]
    apply finalFunctions.parameters (head::tail)
    intro n
    have absent : finalArgs.reverse[n+(head::tail).length]? = none :=
      List.getElem?_eq_none_iff.mpr (by simp only [List.length_reverse,count]; omega)
    simp only [Substitution.reference,closureSubstitution,closureReference,absent,List.reverse_nil,
      List.getElem?_nil,List.length_nil,Nat.sub_zero,count,Nat.add_sub_cancel_right]
  have finalBound : ctx.length ≤ finalCtx.length := Nat.le_trans bound args.context_growth.1
  have next := bodyMeaning bodyRelated finalFrame library closed finalTyped finalScopeTyped finalReferences finalState
    (registers.closure (fun r h => (finalSafe r h).1) (fun r h => (finalSafe r h).2))
    (coherent.applyArguments finalBound finalArgs) helpers finalCurrent
  obtain ⟨core,represented,typedBodies⟩ := (source.retag (Context.Related.prepend related _)).typingPrefixesMapped relation library closed
    pathFrame.typed pathFrame.represented
  obtain ⟨originalCore,originalRep,_⟩ := (source.retag (Context.Related.prepend related _)).typing library closed
  have rep := lambdaSourceMapped_represents shape originalRep pathFrame.represented
  have same := (originalRep.substitute _ _
    (openMapping_represented pathFrame.represented (head::tail).length)).unique represented
  rw [same] at rep
  refine ⟨core,?_,typedBodies,next⟩
  have mapped : LeanBindings.substitute (closureSubstitution ctx.length (targetContext path ctx).length σ []).reference native =
      LeanBindings.rename (·+path.length) (σ.apply native) := by
    rw [← Substitution.apply_eq,targetContext_length]
    exact capture_apply _ _ _ _
  rw [mapped] at rep
  exact rep

end IRComparison.WordFrontend.OrdinarySource
