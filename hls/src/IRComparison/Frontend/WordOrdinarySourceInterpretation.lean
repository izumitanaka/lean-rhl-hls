import IRComparison.Frontend.WordOrdinarySourceFunctions

/-! Interpret the original syntax and State-use conditions into the existing
retained Syntax. The environment judgments used here are induction invariants,
not additional conditions imposed on ordinary Lean input programs. -/
namespace IRComparison.WordFrontend.OrdinarySource
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic StructuralBody ScalarSyntax
set_option maxHeartbeats 3200000

private theorem staticParts (static : LexicalScalarSyntax.StaticRegisters (.app f a)) :
    LexicalScalarSyntax.StaticRegisters f ∧ LexicalScalarSyntax.StaticRegisters a := by
  cases f with
  | app g st =>
    cases g with
    | const name levels =>
      by_cases nameEq : name = ``HybridWord.State.regs
      · subst name
        cases levels with
        | nil =>
          obtain ⟨⟨view⟩,child⟩ := static
          refine ⟨⟨by trivial,child⟩,?_⟩
          rw [view.shape]
          cases view.form <;> trivial
        | cons l ls => exact static
      · simpa [LexicalScalarSyntax.StaticRegisters,nameEq] using static
    | _ => exact static
  | _ => exact static

private theorem lambdaStatic {body : Lean.Expr} (shape : LambdaSource raw domains body)
    (static : LexicalScalarSyntax.StaticRegisters raw) : LexicalScalarSyntax.StaticRegisters body := by
  induction shape with
  | last => exact static
  | next tail ih => exact ih static

private theorem callStatic (args : List Lean.Expr) (f : Lean.Expr)
    (static : LexicalScalarSyntax.StaticRegisters (args.foldl Lean.Expr.app f)) :
    LexicalScalarSyntax.StaticRegisters f := by
  induction args generalizing f with
  | nil => exact static
  | cons a rest ih => exact (staticParts (ih (.app f a) static)).1

/-- The original function occurrence denotes one closure whose callable
meaning has already been constructed by the source induction. -/
def FunctionInterpretation (env : VEnv) (ds : FixedMemory.Declarations) (Γ : Context)
    (raw : Lean.Expr) (signature : Signature) (effects : EffectScope) (requires : List Nat) : Prop :=
  ∀ {Δ ctx p σ τ scope}, Context.Related Γ Δ → ScalarFrame env Δ ctx p σ τ →
    (library : ScopedSyntax.Library env) → ClosedConstantTypes env →
    InputsTyped env ctx p → LexicalScalarCode.ScopeTyped env ctx p → ReferenceScope p →
    (∃ index, p.s = .bvar index) → RegisterMapping σ → scope.Coherent ctx.length σ →
    FunctionEnvironment env ds Γ effects ctx p σ scope →
    ∃ closure, FunctionSyntax.BindingValue scope ctx.length σ raw closure ∧
      FunctionMeaning env ds ctx p closure signature (σ.apply raw) (requires.map σ.reference)

private theorem bindEffects_twice (effects : EffectScope) :
    bindEffects (bindEffects effects) = parameterEffects 2 effects := by
  simp [bindEffects,liftEffects,parameterEffects,List.map_map,Option.map_map,Function.comp_def,Nat.add_assoc]

/-- Applications of a lexical function have the original argument spine.
This removes call-site getAppFn/getAppArgs equalities from source premises. -/
private theorem callParts (binding : FunctionSyntax.BindingValue scope depth σ f closure)
    (first : Lean.Expr) (rest : List Lean.Expr) :
    ∃ fn argument, rest.foldl Lean.Expr.app (.app f first) = .app fn argument ∧
      fn.getAppFn = f ∧ (Lean.Expr.app fn argument).getAppArgs.toList = first::rest := by
  have appArgs (f a : Lean.Expr) : (Lean.Expr.app f a).getAppArgs.toList = f.getAppArgs.toList ++ [a] := by
    simp only [Lean.Expr.getAppArgs_toList,← Lean.Expr.getAppArgsRevList_reverse,
      Lean.Expr.getAppArgsRevList,List.reverse_cons]
  have parts (fn argument : Lean.Expr) (rest : List Lean.Expr) :
      ∃ lastFn lastArg, rest.foldl Lean.Expr.app (.app fn argument) = .app lastFn lastArg ∧
        lastFn.getAppFn = fn.getAppFn ∧
        (Lean.Expr.app lastFn lastArg).getAppArgs.toList = (Lean.Expr.app fn argument).getAppArgs.toList ++ rest := by
    induction rest generalizing fn argument with
    | nil => exact ⟨fn,argument,rfl,rfl,by simp⟩
    | cons value rest ih =>
      obtain ⟨lastFn,lastArg,same,head,args⟩ := ih (.app fn argument) value
      exact ⟨lastFn,lastArg,same,head,by simpa only [appArgs,List.append_assoc,List.singleton_append] using args⟩
  obtain ⟨fn,argument,same,head,args⟩ := parts f first rest
  have ⟨originalHead,originalArgs⟩ := binding.application_parts first
  exact ⟨fn,argument,same,head.trans originalHead,by simpa only [originalArgs,List.singleton_append] using args⟩

private theorem sourceInterpretation :
    (∀ {Γ raw signature} {source : Function ds Γ raw signature} {effects requires},
      Function.Flow ds source effects requires → LexicalScalarSyntax.StaticRegisters raw →
      EffectsTyped Γ effects → FunctionInterpretation env ds Γ raw signature effects requires) ∧
    (∀ {Γ result raw} {source : Body ds Γ result raw} {effects requires},
      Body.Flow ds source effects requires → LexicalScalarSyntax.StaticRegisters raw →
      EffectsTyped Γ effects → BodyMeaning env ds Γ result raw effects requires) := by
  refine ⟨@Function.Flow.rec ds
    (fun {Γ raw signature} _ effects requires _ => LexicalScalarSyntax.StaticRegisters raw → EffectsTyped Γ effects → FunctionInterpretation env ds Γ raw signature effects requires)
    (fun {Γ result raw} _ effects requires _ => LexicalScalarSyntax.StaticRegisters raw → EffectsTyped Γ effects → BodyMeaning env ds Γ result raw effects requires)
    ?«variable» ?lambda ?returns ?yield ?write ?copy ?letScalar ?letState ?bindState ?bindRead ?branch ?staticRange ?naturalRange ?unitSequence ?call ?letFunction,
    @Body.Flow.rec ds
    (fun {Γ raw signature} _ effects requires _ => LexicalScalarSyntax.StaticRegisters raw → EffectsTyped Γ effects → FunctionInterpretation env ds Γ raw signature effects requires)
    (fun {Γ result raw} _ effects requires _ => LexicalScalarSyntax.StaticRegisters raw → EffectsTyped Γ effects → BodyMeaning env ds Γ result raw effects requires)
    ?«variable» ?lambda ?returns ?yield ?write ?copy ?letScalar ?letState ?bindState ?bindRead ?branch ?staticRange ?naturalRange ?unitSequence ?call ?letFunction⟩
  case «variable» =>
    intro signature effects requires Γ index source found static effectsTyped
    intro Δ ctx p σ τ scope related frame library closed inputs typing references stateReference registers coherent functions
    obtain ⟨closure,lookup,meaning⟩ := functions index signature requires source found
    refine ⟨closure,.reuse lookup,?_⟩
    simpa only [Substitution.apply_eq,LeanBindings.substitute] using meaning
  case lambda =>
    intro raw Γ effects requires b head tail result shape source flow ih static effectsTyped
    intro Δ ctx p σ τ scope related frame library closed inputs typing references stateReference registers coherent functions
    have typed := effectsTyped.parameters ((head::tail).reverse.map Slot.value)
    simp only [List.length_map,List.length_reverse] at typed
    refine ⟨_,.lambda shape,?_⟩
    simpa only [List.length_map] using FunctionMeaning.ofLambda source shape
      (ih (lambdaStatic shape static) typed) (flow.demandsTyped typed)
      related frame library closed inputs typing references stateReference registers coherent functions
  case returns =>
    intro Γ st effects tag value static effectsTyped
    intro Δ ctx p σ τ scope related frame library closed inputs typing references stateReference registers coherent functions current
    exact value.returnSyntax tag related frame library closed inputs typing references current
  case yield =>
    intro Γ st effects value static effectsTyped
    intro Δ ctx p σ τ scope related frame library closed inputs typing references stateReference registers coherent functions current
    exact .yield (value.forms related frame library closed inputs typing references current).1
  case write =>
    intro Γ st k ka v va effects state array an declared index value static effectsTyped
    intro Δ ctx p σ τ scope related frame library closed inputs typing references stateReference registers coherent functions current
    exact writeSyntax state array an declared index value related frame library closed inputs typing references current
  case copy =>
    intro Γ st effects state d o n dn sn cn target source static effectsTyped
    intro Δ ctx p σ τ scope related frame library closed inputs typing references stateReference registers coherent functions current
    exact copySyntax state d o n dn sn cn target source related frame library current
  case letScalar =>
    intro Γ v actual b effects requires result annotation value next binder flag flow ih static effectsTyped
    intro Δ ctx p σ τ scope related frame library closed inputs typing references stateReference registers coherent functions current
    obtain ⟨⟨ni⟩,nt,nr,ns⟩ := targetTyped [.scalar annotation] library closed inputs typing references stateReference
    apply scalarLetSyntax value result annotation related frame library closed inputs typing references current.left registers static.2
    · apply ih static.2 (effectsTyped.bind (.value (.scalar annotation))) (.cons (.scalar annotation annotation) related)
        (frame.underScalar closed inputs typing references annotation) library closed ni nt nr ns registers.under
        (by simpa only [List.length_cons] using coherent.under) (functions.under (.scalar annotation))
      exact CurrentMapping.underValue current.right (flow.demandsTyped (effectsTyped.bind _)) (by simp)
  case letState =>
    intro Γ v b effects requires result value next binder flag flow latest ih static effectsTyped
    intro Δ ctx p σ τ scope related frame library closed inputs typing references stateReference registers coherent functions current
    apply stateLetSyntax value result related frame library closed inputs typing references current
    · exact ih static.2 (effectsTyped.bind (.value .state)) (.cons .state related) (frame.underState closed inputs typing) library closed
        (inputs.nextState closed) (typing.nextState closed) references.state ⟨0,rfl⟩ registers.under
        (by simpa only [List.length_cons] using coherent.under) (functions.under .state) (currentMapping_state p latest)
  case bindState =>
    intro Γ a b effects before after result first next binder info ff nf latest ihf ihn static effectsTyped
    intro Δ ctx p σ τ scope related frame library closed inputs typing references stateReference registers coherent functions current
    have firstStatic : LexicalScalarSyntax.StaticRegisters a := by cases result <;> exact (staticParts (staticParts static).1).2
    have nextStatic : LexicalScalarSyntax.StaticRegisters b := by cases result <;> exact (staticParts static).2
    apply stateBindSyntax result
    · exact ihf firstStatic effectsTyped related frame library closed inputs typing references stateReference registers coherent functions current
    · exact ihn nextStatic (effectsTyped.bind (.value .state)) (.cons .state related)
        (frame.underState closed inputs typing) library closed (inputs.nextState closed) (typing.nextState closed)
        references.state ⟨0,rfl⟩ registers.under (by simpa only [List.length_cons] using coherent.under)
        (functions.under .state) (currentMapping_state p latest)
  case bindRead =>
    intro Γ v actual b effects requires result annotation read next binder info flow ih static effectsTyped
    intro Δ ctx p σ τ scope related frame library closed inputs typing references stateReference registers coherent functions current
    have nextStatic : LexicalScalarSyntax.StaticRegisters b := by cases result <;> cases annotation <;> exact (staticParts static).2
    obtain ⟨⟨ni⟩,nt,nr,ns⟩ := targetTyped [.scalar annotation] library closed inputs typing references stateReference
    apply readBindSyntax read result annotation related frame library closed inputs typing references current.left registers nextStatic
    · apply ih nextStatic (effectsTyped.bind (.value (.scalar annotation))) (.cons (.scalar annotation annotation) related)
        (frame.underScalar closed inputs typing references annotation) library closed ni nt nr ns registers.under
        (by simpa only [List.length_cons] using coherent.under) (functions.under (.scalar annotation))
      exact CurrentMapping.underValue current.right (flow.demandsTyped (effectsTyped.bind _)) (by simp)
  case branch =>
    intro Γ v actual a b effects yr nr result annotation guard yes no yf nf iy ino static effectsTyped
    intro Δ ctx p σ τ scope related frame library closed inputs typing references stateReference registers coherent functions current
    have yesStatic : LexicalScalarSyntax.StaticRegisters a := by cases result <;> exact (staticParts (staticParts static).1).2
    have noStatic : LexicalScalarSyntax.StaticRegisters b := by cases result <;> exact (staticParts static).2
    exact branchSyntax guard result annotation related frame library closed inputs typing references current.left.left registers static
      (iy yesStatic effectsTyped related frame library closed inputs typing references stateReference registers coherent functions current.left.right)
      (ino noStatic effectsTyped related frame library closed inputs typing references stateReference registers coherent functions current.right)
  case staticRange =>
    intro Γ st a av b bv c cv raw effects requires state start stop stride body kn tn ki ti flow latest ih static effectsTyped
    intro Δ ctx p σ τ scope related frame library closed inputs typing references stateReference registers coherent functions current
    have nextStatic : LexicalScalarSyntax.StaticRegisters raw := (staticParts static).2
    have nextEffects : EffectsTyped (.value .state::.value (.scalar .word)::Γ) (parameterEffects 2 effects) :=
      effectsTyped.parameters [.value .state,.value (.scalar .word)]
    have eqInputs : targetInputs [.scalar .word,.state] p = For.parameters p := by
      simp only [targetInputs,Parameter.extendInputs,For.parameters,Inputs.lift,List.map_cons,LeanBindings.rename]
    obtain ⟨⟨ni⟩,nt,nr,ns⟩ := targetTyped [.scalar .word,.state] library closed inputs typing references stateReference
    rw [eqInputs] at ni nt nr ns
    have helpers : FunctionEnvironment env ds (.value .state::.value (.scalar .word)::Γ)
        (parameterEffects 2 effects) (stateType::wordType::ctx) (For.parameters p)
        (under (under σ)) (.push none (.push none scope)) := by
      simpa only [bindEffects_twice,← eqInputs,targetInputs,targetContext] using
        (functions.under (.scalar .word)).under .state
    apply staticRangeSyntax state start stop stride library current registers static
    exact ih nextStatic nextEffects (.cons .state (.cons (.scalar .word .word) related))
      (frame.underStaticRange library closed inputs typing references) library closed ni nt nr ns
      registers.under.under (by simpa only [List.length_cons,Nat.add_assoc] using coherent.under.under)
      helpers (currentMapping_staticRange latest)
  case naturalRange =>
    intro Γ st n actual raw effects requires kind state count body kn tn ki ti flow latest ih static effectsTyped
    intro Δ ctx p σ τ scope related frame library closed inputs typing references stateReference registers coherent functions current
    have nextStatic : LexicalScalarSyntax.StaticRegisters raw := by
      cases kind with
      | forIn => exact (staticParts static).2
      | fold => exact (staticParts (staticParts (staticParts static).1).1).2
    have nextEffects : EffectsTyped (rangeContext kind Γ) (parameterEffects 2 effects) := by
      cases kind with
      | forIn => exact effectsTyped.parameters [.value .state,.value .natural]
      | fold => exact effectsTyped.parameters [.value .natural,.value .state]
    have nextRelated : Context.Related (rangeContext kind Γ) (rangeContext kind Δ) := by
      cases kind with
      | forIn => exact .cons .state (.cons .natural related)
      | fold => exact .cons .natural (.cons .state related)
    have nextBody : FunctionSyntax.Syntax env (mode := (rangeResult kind).mode)
        (kind.context ctx) (kind.parameters p) (under (under σ)) (.push none (.push none scope)) raw
        (FixedSequenceCompleteness.InputConditions ds) := by
      apply ih nextStatic nextEffects nextRelated (frame.underNaturalRange library closed inputs typing references kind) library closed
      all_goals cases kind <;>
        first
        | exact NaturalScope.forInInputs inputs closed library.scalars.toSignatures library.naturalLoops.ofNat library.cons
        | exact NaturalScope.foldInputs inputs closed library.scalars.toSignatures library.naturalLoops.ofNat library.cons
        | exact typing.naturalLoop closed library.scalars.toSignatures library.naturalLoops .forIn
        | exact typing.naturalLoop closed library.scalars.toSignatures library.naturalLoops .fold
        | exact references.forIn
        | exact references.fold
        | exact ⟨0,rfl⟩
        | exact ⟨1,rfl⟩
        | exact registers.under.under
        | exact (by simpa only [NaturalLoop.Kind.context,NaturalLoop.Kind.first,NaturalLoop.Kind.second,List.length_cons,Nat.add_assoc] using coherent.under.under)
        | exact (by simpa only [bindEffects_twice,NaturalLoop.Kind.context,NaturalLoop.Kind.first,NaturalLoop.Kind.second,
            NaturalLoop.Kind.parameters,NaturalScope.forInParameters,Parameter.extendInputs,Inputs.lift,List.map_cons,
            LeanBindings.rename,NaturalScope.nativeIndex,app,List.foldl_cons,List.foldl_nil] using
            (functions.under .natural).under .state)
        | exact (by simpa only [bindEffects_twice,NaturalLoop.Kind.context,NaturalLoop.Kind.first,NaturalLoop.Kind.second,
            NaturalLoop.Kind.parameters,NaturalScope.foldParameters,Parameter.extendInputs,Inputs.lift] using
            (functions.under .state).under .natural)
        | exact currentMapping_range _ latest
    apply naturalRangeSyntax state count kind related frame library closed inputs typing references current.left current.right registers static
    cases kind <;> exact nextBody
  case unitSequence =>
    intro Γ b effects requires result next binder info flow ih static effectsTyped
    intro Δ ctx p σ τ scope related frame library closed inputs typing references stateReference registers coherent functions current
    have nextStatic : LexicalScalarSyntax.StaticRegisters b := by cases result <;> exact (staticParts static).2
    obtain ⟨⟨ni⟩,nt,nr,ns⟩ := targetTyped [.unit] library closed inputs typing references stateReference
    apply unitBindSyntax result
    · apply ih nextStatic (effectsTyped.bind (.value .unit)) (.cons .unit related)
        (frame.underUnit closed inputs typing) library closed ni nt nr ns registers.under
        (by simpa only [List.length_cons] using coherent.under) (functions.under .unit)
      exact CurrentMapping.underValue current (flow.demandsTyped (effectsTyped.bind _)) (by simp)
  case call =>
    intro Γ f head tail result first rest effects requires fn arguments flow ih static effectsTyped
    intro Δ ctx p σ τ scope related frame library closed inputs typing references stateReference registers coherent functions current
    obtain ⟨closure,binding,meaning⟩ := ih (callStatic (first::rest) f static) effectsTyped
      related frame library closed inputs typing references stateReference registers coherent functions
    obtain ⟨callFn,callArg,same,fnHead,fnArgs⟩ := callParts binding first rest
    obtain ⟨fc,fp,fa,retained⟩ := arguments.retained related frame library closed inputs typing references current.right
    obtain ⟨actual,cores,relation,reps,types,checks⟩ := (arguments.retag related).evidenceMapped library closed frame.typed frame.represented
    have mapped : (first::rest).map (LeanBindings.substitute σ.reference) = (first::rest).map σ.apply := by
      congr 1
      funext raw
      exact (Substitution.apply_eq σ raw).symm
    rw [mapped] at reps
    have unitSafe := arguments.unitSafe relation registers
    cases closure with
    | captured depth captured arity body funcs =>
      rw [same]
      apply meaning.invoke library closed callFn callArg coherent
        (fnHead.symm ▸ binding) (by rw [fnHead]) relation types checks
      · simpa only [fnArgs] using reps
      · simpa only [fnArgs] using unitSafe
      · simpa only [fnArgs] using retained
      · intro value member
        obtain ⟨n,originalMember,rfl⟩ := List.mem_map.mp member
        exact current.left n originalMember
  case letFunction =>
    intro signature ty Γ v result b effects captureRequires requires spelling value next binder flag vf nf iv ine static effectsTyped
    intro Δ ctx p σ τ scope related frame library closed inputs typing references stateReference registers coherent functions current
    obtain ⟨closure,binding,meaning⟩ := iv static.1 effectsTyped related frame library closed inputs typing references stateReference registers coherent functions
    obtain ⟨nextTypes,nextFrame⟩ := frame.bindFunction value related library closed
    have nextEffects := effectsTyped.bindFunction (vf.demandsTyped effectsTyped) signature
    have nextSyntax := ine static.2 nextEffects (.cons (.function signature) related) nextFrame library closed
      inputs typing references stateReference (registers.functionLet value static.1)
      (coherent.functionLet binding) (functions.bindFunction meaning)
      (CurrentMapping.functionLet current (nf.demandsTyped nextEffects) v)
    cases signature with
    | mk domains helperResult =>
      cases domains with
      | nil => exact False.elim (meaning.nonempty rfl)
      | cons head tail =>
        exact functionLet library closed (value.retag related)
          (next.retag (.cons (.function ⟨head::tail,helperResult⟩) related)) spelling
          frame.typed frame.represented binding nextSyntax binder flag

/-- All original helper constructs share the same mutual source induction. -/
theorem Function.Flow.interpret {source : Function ds Γ raw signature}
    (flow : Function.Flow ds source effects requires) (static : LexicalScalarSyntax.StaticRegisters raw)
    (typed : EffectsTyped Γ effects) : FunctionInterpretation env ds Γ raw signature effects requires :=
  sourceInterpretation.1 flow static typed

/-- All original command constructs, including arbitrary nesting of helpers,
State/read bindings, branches and both iterator forms, use one induction. -/
theorem Body.Flow.interpret {source : Body ds Γ result raw}
    (flow : Body.Flow ds source effects requires) (static : LexicalScalarSyntax.StaticRegisters raw)
    (typed : EffectsTyped Γ effects) : BodyMeaning env ds Γ result raw effects requires :=
  sourceInterpretation.2 flow static typed

/-- The ordinary source entrance constructs internal Syntax. No expanded or
retained body, internal type derivation, parser result or generated command
is a source premise. The source header contains the one original State slot. -/
theorem Body.syntaxEntry (source : Body ds [.value .state] .body raw)
    (current : source.Current) (static : LexicalScalarSyntax.StaticRegisters raw)
    (library : ScopedSyntax.Library env) (closed : ClosedConstantTypes env) :
    FunctionSyntax.Syntax env context parameters .identity .empty raw
      (FixedSequenceCompleteness.InputConditions ds) := by
  obtain ⟨requires,flow,latest⟩ := current
  have effectsTyped : EffectsTyped [.value .state] [none] := by intro rs member; simp at member
  apply flow.interpret static effectsTyped (Context.Related.refl _) ScalarFrame.initial library closed
    (initialInputs library.connection.word library.connection.nilWords) LexicalScalarCode.ScopeTyped.initial
    ReferenceScope.initial ⟨0,rfl⟩ RegisterMapping.initial (FunctionSyntax.Scope.coherent_empty _ _)
  · intro index signature demands found
    cases index <;> simp at found
  · intro n member
    rw [latest n member]
    rfl

/-- Transport the original State-use evidence along an independently checked
native-syntax equality. This does not inspect generated code. -/
theorem Body.Current.cast {source : Body ds [.value .state] .body raw}
    (current : source.Current) (same : raw = other) : (same ▸ source).Current := by
  cases same
  exact current

/-- Generation success from original ordinary-Lean syntax and independent
source/environment/static conditions, through compileRetained and the existing
fixed-array Entry.compile_total. Parser success and an Entry are conclusions.
This theorem is about compiler generation success; runtime semantic preservation
continues to use the existing source and RTL correctness theorems. -/
theorem generates (input : NativeEnvironment.Input nativeEnvironment name)
    (source : Body ds [.value .state] .body input.header.body)
    (current : source.Current) (static : LexicalScalarSyntax.StaticRegisters input.header.body)
    (unique : FixedMemory.unique ds = true) (outputs : List Nat)
    (outputsDeclared : outputs.all (fun a => (FixedMemory.lookup ds a).isSome) = true)
    (budget : Nat) (strategy : Circuit.Pipelining.LoopStrategy) :
    ∃ result, StructuralBody.compileRetained nativeEnvironment name = some result ∧ result.CodeTyped ∧
      ∃ env : VEnv, ∃ native code,
        FixedFunctionCompleteness.Source ds (env := env) context parameters .identity .empty input.header.body native code result.code ∧
        ∃ entry : FixedHLS.Entry (native 0 0 0 []), entry.program.code = code ∧ entry.declarations = ds ∧
          ∃ compiled, entry.compile outputs budget strategy = .ok compiled := by
  apply FixedFunctionCompleteness.generatesRetainedSyntaxInstalled input
  · intro env setup library installed closed fresh exposure
    exact source.syntaxEntry current static library closed
  · simpa only [List.length_cons,List.length_nil] using source.wellScoped
  · exact unique
  · exact outputsDeclared

end IRComparison.WordFrontend.OrdinarySource
