import IRComparison.Frontend.WordRetainedArguments
import IRComparison.Frontend.WordNaturalLiteral
import IRComparison.Frontend.WordFunctionState
import IRComparison.Frontend.WordAnnotatedBranch

/-! The existing source-only function judgment. It sits after the shared
mapped-constructor lemmas so nested bodies reuse those lemmas, rather than
adding a separate completeness proof for each enclosing function context. -/
namespace IRComparison.WordFrontend.FunctionSyntax
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic StructuralBody StructuralSyntax
set_option maxHeartbeats 2400000

/-- The function environment in the syntax judgment contains source closures,
not successful parser results. Recursive constructors describe the original
source body and its lexical substitution. -/
inductive Syntax (env : VEnv) : List VExpr → Inputs → Substitution → Scope → Lean.Expr →
    (requirements : Lean.Expr → Prop := fun _ => True) → (mode : Mode := .body) → Prop where
  | plain (form : ScopedSyntax.Syntax env mode ctx p raw requirements) :
      Syntax env (requirements := requirements) (mode := mode) ctx p .identity .empty raw
  | base (head : HeadForm σ p raw) (form : ScopedSyntax.Form env ctx p (σ.apply raw) requirements) :
      Syntax env (requirements := requirements) (mode := .body) ctx p σ scope raw
  | valueCurrent (current : σ.apply raw = p.s) :
      Syntax env (requirements := requirements) (mode := .value) ctx p σ scope raw
  | valueAssign (register : Nat) (rn : NatNotation)
      (current : σ.apply st = p.s)
      (value : LexicalScalarSyntax.Form env ctx p [] (σ.apply v))
      (checked : requirements ((σ).apply (app ``HybridWord.State.set [st,rn.native register,v])) := by trivial) :
      Syntax env (requirements := requirements) (mode := .value) ctx p σ scope (app ``HybridWord.State.set [st,rn.native register,v])
  | yield (value : Syntax env (requirements := requirements) (mode := .value) ctx p σ scope raw) :
      Syntax env (requirements := requirements) (mode := .step) ctx p σ scope (Step.yieldSource raw)
  | stepSequence (first : Syntax env (requirements := requirements) (mode := .body) ctx p σ scope a)
      (next : Syntax env (requirements := requirements) (mode := .step) (stateType::ctx) {p.lift with s := .bvar 0} (under σ) (.push none scope) b)
      (binder : Lean.Name) (info : Lean.BinderInfo) :
      Syntax env (requirements := requirements) (mode := .step) ctx p σ scope (StructuralStep.sequenceSource a (.lam binder state b info))
  | forStatic (start : For.Bound env ctx (σ.apply a))
      (stop : For.Bound env ctx (σ.apply b))
      (stride : For.Bound env ctx (σ.apply c))
      (current : σ.apply st = p.s)
      (body : Syntax env (requirements := requirements) (mode := .step) (stateType::wordType::ctx) (For.parameters p) (under (under σ)) (.push none (.push none scope)) original)
      (kn tn : Lean.Name) (ki ti : Lean.BinderInfo)
      (checked : requirements ((σ).apply (For.source a b c st (.lam kn word (.lam tn state original ti) ki))) := by trivial) :
      Syntax env (requirements := requirements) (mode := .body) ctx p σ scope (For.source a b c st (.lam kn word (.lam tn state original ti) ki))
  | unitBody (next : Syntax env (requirements := requirements) (mode := .body) (UnitStep.unitType::ctx) p.lift (under σ) (.push none scope) b) (binder : Lean.Name) (info : Lean.BinderInfo) :
      Syntax env (requirements := requirements) (mode := .body) ctx p σ scope (StructuralUnit.source false binder b info)
  | unitLoop (next : Syntax env (requirements := requirements) (mode := .step) (UnitStep.unitType::ctx) p.lift (under σ) (.push none scope) b) (binder : Lean.Name) (info : Lean.BinderInfo) :
      Syntax env (requirements := requirements) (mode := .step) ctx p σ scope (StructuralUnit.source true binder b info)
  | forRange (kind : NaturalLoop.Kind)
      (count : LexicalScalarSyntax.Form env ctx p [] (σ.apply n))
      (current : σ.apply st = p.s)
      (body : Syntax env (requirements := requirements) (mode := kind.mode) (kind.context ctx) (kind.parameters p) (under (under σ)) (.push none (.push none scope)) original)
      (kn tn : Lean.Name) (ki ti : Lean.BinderInfo)
      (checked : requirements ((σ).apply (kind.source n st (kind.nativeLambda kn tn ki ti original))) := by trivial) :
      Syntax env (requirements := requirements) (mode := .body) ctx p σ scope (kind.source n st (kind.nativeLambda kn tn ki ti original))
  | letValue (annotation : WordBinder.Annotation)
      (value : LexicalScalarSyntax.Form env ctx p [] (σ.apply v))
      (next : Syntax env (requirements := requirements) (mode := .body) (annotation.core::ctx) {p.lift with locals := .bvar 0::p.lift.locals} (under σ) (.push none scope) b)
      (binder : Lean.Name) (flag : Bool)
      (checked : requirements ((σ).apply (WordBinder.letSource annotation binder v b flag)) := by trivial) :
      Syntax env (requirements := requirements) (mode := .body) ctx p σ scope (WordBinder.letSource annotation binder v b flag)
  | bindValue (annotation : WordBinder.Annotation)
      (value : ScopedSyntax.ReadForm env ctx p (σ.apply v))
      (next : Syntax env (requirements := requirements) (mode := .body) (annotation.core::ctx) {p.lift with locals := .bvar 0::p.lift.locals} (under σ) (.push none scope) b)
      (binder : Lean.Name) (info : Lean.BinderInfo)
      (checked : requirements ((σ).apply (WordBinder.readSource annotation v (.lam binder annotation.native b info))) := by trivial) :
      Syntax env (requirements := requirements) (mode := .body) ctx p σ scope (WordBinder.readSource annotation v (.lam binder annotation.native b info))
  | stepBindValue (annotation : WordBinder.Annotation)
      (value : ScopedSyntax.ReadForm env ctx p (σ.apply v))
      (next : Syntax env (requirements := requirements) (mode := .step) (annotation.core::ctx) {p.lift with locals := .bvar 0::p.lift.locals} (under σ) (.push none scope) b)
      (binder : Lean.Name) (info : Lean.BinderInfo)
      (checked : requirements ((σ).apply (WordBinder.stepReadSource annotation v (.lam binder annotation.native b info))) := by trivial) :
      Syntax env (requirements := requirements) (mode := .step) ctx p σ scope (WordBinder.stepReadSource annotation v (.lam binder annotation.native b info))
  | stepLetValue (annotation : WordBinder.Annotation)
      (value : LexicalScalarSyntax.Form env ctx p [] (σ.apply v))
      (next : Syntax env (requirements := requirements) (mode := .step) (annotation.core::ctx) {p.lift with locals := .bvar 0::p.lift.locals} (under σ) (.push none scope) b)
      (binder : Lean.Name) (flag : Bool)
      (checked : requirements ((σ).apply (WordBinder.letSource annotation binder v b flag)) := by trivial) :
      Syntax env (requirements := requirements) (mode := .step) ctx p σ scope (WordBinder.letSource annotation binder v b flag)
  | stateLet (value : Syntax env (requirements := requirements) (mode := .value) ctx p σ scope v)
      (next : Syntax env (requirements := requirements) (mode := .body) (stateType::ctx) {p.lift with s := .bvar 0} (under σ) (.push none scope) b)
      (notAlias : sameTerm (σ.apply v) p.s = false) (binder : Lean.Name) (flag : Bool) :
      Syntax env (requirements := requirements) (mode := .body) ctx p σ scope (StateLet.source binder v b flag)
  | stepStateLet (value : Syntax env (requirements := requirements) (mode := .value) ctx p σ scope v)
      (next : Syntax env (requirements := requirements) (mode := .step) (stateType::ctx) {p.lift with s := .bvar 0} (under σ) (.push none scope) b)
      (notAlias : sameTerm (σ.apply v) p.s = false) (binder : Lean.Name) (flag : Bool) :
      Syntax env (requirements := requirements) (mode := .step) ctx p σ scope (StructuralStateLet.Loop.source binder v b flag)
  | stateAlias (current : σ.apply st = p.s)
      (next : Syntax env (requirements := requirements) (mode := .body) (stateType::ctx) {p.lift with s := .bvar 0} (under σ) (.push none scope) b)
      (binder : Lean.Name) (flag : Bool) :
      Syntax env (requirements := requirements) (mode := .body) ctx p σ scope (.letE binder state st b flag)
  | stepAlias (current : σ.apply st = p.s)
      (next : Syntax env (requirements := requirements) (mode := .step) (stateType::ctx) {p.lift with s := .bvar 0} (under σ) (.push none scope) b)
      (binder : Lean.Name) (flag : Bool) :
      Syntax env (requirements := requirements) (mode := .step) ctx p σ scope (.letE binder state st b flag)
  | sequence (first : Syntax env (requirements := requirements) (mode := .body) ctx p σ scope a)
      (next : Syntax env (requirements := requirements) (mode := .body) (stateType::ctx) {p.lift with s := .bvar 0} (under σ) (.push none scope) b)
      (binder : Lean.Name) (info : Lean.BinderInfo) :
      Syntax env (requirements := requirements) (mode := .body) ctx p σ scope (sequenceSource a (.lam binder state b info))
  | branch (value : LexicalScalarSyntax.Form env ctx p [] (σ.apply v))
      (decision : ScalarSyntax.Decision env ctx (σ.apply v) (σ.apply d))
      (yes : Syntax env (requirements := requirements) (mode := .body) ctx p σ scope a)
      (no : Syntax env (requirements := requirements) (mode := .body) ctx p σ scope b)
      (checked : requirements ((σ).apply (Branch.source v d a b)) := by trivial) :
      Syntax env (requirements := requirements) (mode := .body) ctx p σ scope (Branch.source v d a b)
  | booleanBranch (value : LexicalScalarSyntax.Form env ctx p [] (σ.apply v))
      (yes : Syntax env (requirements := requirements) (mode := .body) ctx p σ scope a)
      (no : Syntax env (requirements := requirements) (mode := .body) ctx p σ scope b)
      (checked : requirements ((σ).apply (Branch.source v (Branch.nativeBooleanDecision v) a b)) := by trivial) :
      Syntax env (requirements := requirements) (mode := .body) ctx p σ scope (Branch.source v (Branch.nativeBooleanDecision v) a b)
  | annotatedBooleanBranch {valueCore : VExpr} (annotation operand : WordBinder.Annotation)
      (value : LexicalScalarSyntax.Form env ctx p [] (σ.apply v))
      (represented : Represents (σ.apply v) valueCore)
      (typed : CastTyping env 0 (SourceCasts env) ctx valueCore operand.core)
      (form : LexicalScalarSyntax.ValueShape env ctx valueCore operand.core)
      (yes : Syntax env (requirements := requirements) (mode := .body) ctx p σ scope a)
      (no : Syntax env (requirements := requirements) (mode := .body) ctx p σ scope b)
      (checked : requirements ((σ).apply (AnnotatedBranch.source annotation v (AnnotatedCondition.nativeDecision annotation v) a b)) := by trivial) :
      Syntax env (requirements := requirements) (mode := .body) ctx p σ scope (AnnotatedBranch.source annotation v (AnnotatedCondition.nativeDecision annotation v) a b)
  | annotatedStepBooleanBranch {valueCore : VExpr} (annotation operand : WordBinder.Annotation)
      (value : LexicalScalarSyntax.Form env ctx p [] (σ.apply v))
      (represented : Represents (σ.apply v) valueCore)
      (typed : CastTyping env 0 (SourceCasts env) ctx valueCore operand.core)
      (form : LexicalScalarSyntax.ValueShape env ctx valueCore operand.core)
      (yes : Syntax env (requirements := requirements) (mode := .step) ctx p σ scope a)
      (no : Syntax env (requirements := requirements) (mode := .step) ctx p σ scope b)
      (checked : requirements ((σ).apply (AnnotatedBranch.Loop.source annotation v (AnnotatedCondition.nativeDecision annotation v) a b)) := by trivial) :
      Syntax env (requirements := requirements) (mode := .step) ctx p σ scope (AnnotatedBranch.Loop.source annotation v (AnnotatedCondition.nativeDecision annotation v) a b)
  | stepBooleanBranch (value : LexicalScalarSyntax.Form env ctx p [] (σ.apply v))
      (yes : Syntax env (requirements := requirements) (mode := .step) ctx p σ scope a)
      (no : Syntax env (requirements := requirements) (mode := .step) ctx p σ scope b)
      (checked : requirements ((σ).apply (StructuralStep.Conditional.source v (Branch.nativeBooleanDecision v) a b)) := by trivial) :
      Syntax env (requirements := requirements) (mode := .step) ctx p σ scope (StructuralStep.Conditional.source v (Branch.nativeBooleanDecision v) a b)
  | retainedCall {body : Lean.Expr} {bodyCore domain first : VExpr}
    {rest domains : List VExpr}
    (fn argument : Lean.Expr) (modeAllowed : mode ≠ .value)
    (binding : BindingValue scope ctx.length σ fn.getAppFn (.captured depth bindings arity body functions))
    (coherent : scope.Coherent ctx.length σ)
    (arguments : ArgumentBindings.Syntax env ctx p
      ((Lean.Expr.app fn argument).getAppArgs.toList.map σ.apply) []
      finalCtx finalInputs finalArgs)
    (next : Syntax env (requirements := requirements) (mode := mode) finalCtx finalInputs
      (closureSubstitution depth finalCtx.length bindings finalArgs)
      (functions.parameters finalArgs.length) body)
    (arityMatches : (Lean.Expr.app fn argument).getAppArgs.size = arity)
    (domainTyped : CastTyping env 0 (SourceCasts env) ctx domain (.sort u))
    (bodyTyped : CastTyping env 0 (SourceCasts env) (domain::ctx) bodyCore
      (domains.foldr VExpr.forallE (optionType (if mode == .step then Step.stepState else stateType))))
    (firstTyped : CheckedTyping env 0 (SourceCasts env) ctx first domain)
    (argumentTypes : List.Forall₂ (fun domain arg => CheckedTyping env 0 (SourceCasts env) ctx arg domain) domains rest)
    (typesClosed : ∀ n, ((domains.drop n).foldr VExpr.forallE (optionType (if mode == .step then Step.stepState else stateType))).ClosedN 0)
    (prefixTypes : ∀ before after, rest = before ++ after → after ≠ [] →
      CastTyping env 0 (SourceCasts env) ctx (before.foldl LeanTypeReduction.applyReduced (bodyCore.inst first))
        ((domains.drop before.length).foldr VExpr.forallE (optionType (if mode == .step then Step.stepState else stateType))))
    (reducedRep : Represents
      ((closureSubstitution depth ctx.length bindings
        ((Lean.Expr.app fn argument).getAppArgs.toList.map σ.apply)).apply body)
      (rest.foldl LeanTypeReduction.applyReduced (bodyCore.inst first)))
    (sourceRep : Represents (σ.apply (.app fn argument))
      (applications (.app (.lam domain bodyCore) first) rest))
    : Syntax env (requirements := requirements) (mode := mode)
        ctx p σ scope (.app fn argument)
  | functionLet {sourceBody functionValue domain codomain : VExpr}
      (binder : Lean.Name) (ty value next : Lean.Expr) (flag : Bool)
      (binding : BindingValue scope ctx.length σ value closure)
      (tail : Syntax env (requirements := requirements) (mode := .body) ctx p (letSubstitution σ value) (.push (some closure) scope) next)
      (typeRep : Represents (σ.apply ty) (.forallE domain codomain))
      (typeTyped : CastTyping env 0 (SourceCasts env) ctx (.forallE domain codomain) (.sort u))
      (bodyTyped : CastTyping env 0 (SourceCasts env) ((.forallE domain codomain)::ctx) sourceBody (optionType stateType))
      (valueTyped : CastTyping env 0 (SourceCasts env) ctx functionValue (.forallE domain codomain))
      (reducedRep : Represents ((letSubstitution σ value).apply next) (sourceBody.inst functionValue))
      (sourceRep : Represents (σ.apply (.letE binder ty value next flag))
        (.app (.lam (.forallE domain codomain) sourceBody) functionValue)) :
      Syntax env (requirements := requirements) (mode := .body) ctx p σ scope (.letE binder ty value next flag)
  | stepFunctionLet {sourceBody functionValue domain codomain : VExpr}
      (binder : Lean.Name) (ty value next : Lean.Expr) (flag : Bool)
      (binding : BindingValue scope ctx.length σ value closure)
      (tail : Syntax env (requirements := requirements) (mode := .step) ctx p (letSubstitution σ value) (.push (some closure) scope) next)
      (typeRep : Represents (σ.apply ty) (.forallE domain codomain))
      (typeTyped : CastTyping env 0 (SourceCasts env) ctx (.forallE domain codomain) (.sort u))
      (bodyTyped : CastTyping env 0 (SourceCasts env) ((.forallE domain codomain)::ctx) sourceBody (optionType Step.stepState))
      (valueTyped : CastTyping env 0 (SourceCasts env) ctx functionValue (.forallE domain codomain))
      (reducedRep : Represents ((letSubstitution σ value).apply next) (sourceBody.inst functionValue))
      (sourceRep : Represents (σ.apply (.letE binder ty value next flag))
        (.app (.lam (.forallE domain codomain) sourceBody) functionValue)) :
      Syntax env (requirements := requirements) (mode := .step) ctx p σ scope (.letE binder ty value next flag)

def Outcome (setup : AliasSetup env) (exposure : Exposure env) (inputs : InputsTyped env ctx p)
    (σ : Substitution) (scope : Scope) (mode : StructuralBody.Mode) (raw : Lean.Expr) : Prop :=
  match mode with
  | .body => ∃ piece, visit env setup.conversion exposure raw ctx p .body σ (scope.runtime env setup.conversion exposure) = some piece ∧
      ∃ typed : BodyCasts inputs piece (SourceCasts env) (For.Casts setup),
        ValueForm setup ctx typed.sourceCore.val (optionType stateType)
  | .value => ∃ piece, StructuralBody.visit env setup.conversion exposure raw ctx p .value σ (scope.runtime env setup.conversion exposure) = some piece ∧
      Nonempty (StructuralLoop.ValueCasts inputs piece (SourceCasts env) (For.Casts setup))
  | .step => ∃ piece, StructuralBody.visit env setup.conversion exposure raw ctx p .step σ (scope.runtime env setup.conversion exposure) = some piece ∧
      ∃ typed : StructuralLoop.StepCasts inputs piece (SourceCasts env) (For.Casts setup),
        ValueForm setup ctx typed.sourceCore.val (optionType Step.stepState)

theorem syntax_complete (source : Syntax env ctx p σ scope raw requirements mode)
    (setup : AliasSetup env) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (fresh : ScopedSyntax.Fresh setup) (exposure : Exposure env)
    (inputs : InputsTyped env ctx p) (locals : ScalarSyntax.Locals env ctx p) :
    Outcome setup exposure inputs σ scope mode raw := by
  have coverage := For.Casts.covered setup library.scalars.toSignatures library.steps closed
    library.cons library.eq library.eval fresh.state fresh.eq fresh.lift
  induction source with
  | @plain mode ctx p raw requirements body =>
    cases mode <;> exact ScopedSyntax.syntax_complete setup library closed fresh exposure body inputs locals

  | @base σ p raw ctx requirements scope head body =>
    unfold Outcome
    rw [eq_of_heq (head.parser_congr (sameTerm_complete inputs.s.property inputs.s.property))]
    exact ScopedSyntax.syntax_complete setup library closed fresh exposure body inputs locals

  | @valueCurrent ctx p σ scope raw requirements current =>
    obtain ⟨piece,success,typed⟩ := ScopedSyntax.syntax_complete setup library closed fresh exposure
      (ScopedSyntax.Syntax.valueCurrent (env := env) (ctx := ctx) (p := p)) inputs locals
    obtain ⟨piece,success,typed,_⟩ := value_outcome_transport inputs current (valueCurrent_congr current inputs)
      ⟨piece,success,typed,rfl⟩
    exact ⟨piece,success,typed⟩

  | @valueAssign ctx p requirements σ scope st v register rn current value checked =>
    have number : σ.apply (rn.native register) = rn.native register := by cases σ <;> cases rn <;> rfl
    have same : σ.apply (app ``HybridWord.State.set [st,rn.native register,v]) =
        app ``HybridWord.State.set [p.s,rn.native register,σ.apply v] := by
      rw [substitute_valueAssign,current,number]
    have congruent := valueAssign_congr (env := env) (conv := setup.conversion) (exposure := exposure)
      (ctx := ctx) (p := p) (fs := scope.runtime env setup.conversion exposure)
      (st := st) (r := rn.native register) (v := v) σ
    have normalized : HEq
        (visit env setup.conversion exposure (app ``HybridWord.State.set [σ.apply st,σ.apply (rn.native register),σ.apply v])
          ctx p .value .identity (fun _ => none))
        (visit env setup.conversion exposure (app ``HybridWord.State.set [p.s,rn.native register,σ.apply v])
          ctx p .value .identity (fun _ => none)) := by
      generalize σ.apply st = t at current ⊢
      generalize σ.apply (rn.native register) = r at number ⊢
      subst t; subst r; rfl
    obtain ⟨piece,success,typed⟩ := ScopedSyntax.syntax_complete setup library closed fresh exposure
      (ScopedSyntax.Syntax.valueAssign (rn.argument library.scalars.toSignatures register) value) inputs locals
    obtain ⟨piece,success,typed,_⟩ := value_outcome_transport inputs same (congruent.trans normalized)
      ⟨piece,success,typed,rfl⟩
    exact ⟨piece,success,typed⟩

  | @yield ctx p σ scope raw requirements value ih =>
    obtain ⟨a,ha,⟨ta⟩⟩ := ih inputs locals
    obtain ⟨result,parsed,typed,form,q⟩ := FunctionSyntax.yield_complete_code setup library closed fresh exposure inputs ta ha
    exact ⟨result,parsed,typed,form⟩
  | @stateLet ctx p σ scope v requirements b value next notAlias binder flag ihValue ihNext =>
    obtain ⟨a,ha,⟨ta⟩⟩ := ihValue inputs locals
    obtain ⟨b,hb,tb,fb⟩ := ihNext (inputs.nextState closed) (locals.nextState closed)
    have underRuntime (scope : Scope) : (Scope.push none scope).runtime env setup.conversion exposure =
        underFunctions (scope.runtime env setup.conversion exposure) := by
      funext n; cases n <;> rfl
    rw [underRuntime] at hb
    obtain ⟨target,_,_⟩ := sequence_next_typed inputs closed Arithmetic.SourceCasts.closed library.returns.state tb
    obtain ⟨piece,parsed,⟨typed⟩,code⟩ := StructuralStateLet.mapped_complete_code inputs closed Arithmetic.SourceCasts.closed
      (fun _ _ _ h => For.Casts.base (.base (.source h))) library.returns.state ta library.returns tb
      (.base (.base (.stateContinuation inputs target tb.value fb))) library.stateLet library.sequenceConstructor
      coverage exposure binder flag notAlias ha hb
    have same : typed.sourceCore.val = .app (.lam stateType tb.sourceCore.val) ta.sourceCore.val :=
      typed.sourceCore.property.unique (by
        simp only [StateLet.source,StructuralStateLet.Loop.source]
        rw [StructuralStep.Alias.substitute_latest_let]
        exact Represents.letE (Represents.constant rfl) ta.sourceCore.property tb.sourceCore.property)
    refine ⟨piece,parsed,typed,?_⟩
    · rw [same]; exact .beta tb.value
  | @stepStateLet ctx p σ scope v requirements b value next notAlias binder flag ihValue ihNext =>
    obtain ⟨a,ha,⟨ta⟩⟩ := ihValue inputs locals
    obtain ⟨b,hb,tb,fb⟩ := ihNext (inputs.nextState closed) (locals.nextState closed)
    have underRuntime (scope : Scope) : (Scope.push none scope).runtime env setup.conversion exposure =
        underFunctions (scope.runtime env setup.conversion exposure) := by
      funext n; cases n <;> rfl
    rw [underRuntime] at hb
    have eval := eval_cast_typed (inputs.nextState closed) library.eval tb.target
    have beta := For.Casts.directContinuation (setup := setup) .state eval tb.value fb
    have codeClosed := b.represented.property.closed 0 b.closed
    have cast : For.Casts setup ctx
        (StructuralStep.sequenceNextActual inputs b.represented.val tb.sourceCore.val)
        (StructuralStep.sequenceContinuationType inputs b.represented.val (.lam stateType tb.sourceCore.val)) := by
      simpa only [StructuralStep.sequenceNextActual,StructuralStep.sequenceContinuationType,
        InputsTyped.nextState,InputsTyped.lift,Step.Binder.core,Arithmetic.continuationValue,
        VExpr.lift,VExpr.liftN,stateType,codeClosed.liftN_eq (Nat.zero_le _)] using beta
    obtain ⟨piece,parsed,⟨typed⟩,code⟩ := StructuralStateLet.Loop.mapped_complete_code inputs closed Arithmetic.SourceCasts.closed
      (fun _ _ _ h => For.Casts.base (.base (.source h))) library.returns.state ta library.returns tb cast library.stepStateLet library.sequenceConstructor
      coverage exposure binder flag notAlias ha hb
    have same : typed.sourceCore.val = .app (.lam stateType tb.sourceCore.val) ta.sourceCore.val :=
      typed.sourceCore.property.unique (by
        simp only [StateLet.source,StructuralStateLet.Loop.source]
        rw [StructuralStep.Alias.substitute_latest_let]
        exact Represents.letE (Represents.constant rfl) ta.sourceCore.property tb.sourceCore.property)
    refine ⟨piece,parsed,typed,?_⟩
    · rw [same]; exact .beta tb.value
  | @stateAlias ctx σ scope b requirements p st current next binder flag ih =>
    obtain ⟨b,hb,tb,fb⟩ := ih (inputs.nextState closed) (locals.nextState closed)
    have underRuntime (scope : Scope) : (Scope.push none scope).runtime env setup.conversion exposure =
        underFunctions (scope.runtime env setup.conversion exposure) := by
      funext n; cases n <;> rfl
    rw [underRuntime] at hb
    obtain ⟨piece,success,typed,form,q⟩ := FunctionSyntax.stateAlias_complete_code setup library closed fresh exposure inputs tb fb current hb binder flag
    exact ⟨piece,success,typed,form⟩
  | @stepAlias ctx σ scope b requirements p st current next binder flag ih =>
    obtain ⟨b,hb,tb,fb⟩ := ih (inputs.nextState closed) (locals.nextState closed)
    have underRuntime (scope : Scope) : (Scope.push none scope).runtime env setup.conversion exposure =
        underFunctions (scope.runtime env setup.conversion exposure) := by
      funext n; cases n <;> rfl
    rw [underRuntime] at hb
    obtain ⟨piece,success,typed,form,q⟩ := FunctionSyntax.stepAlias_complete_code setup library closed fresh exposure inputs tb fb current hb binder flag
    exact ⟨piece,success,typed,form⟩
  | @stepSequence ctx p σ scope a requirements b first next binder info ia ib =>
    obtain ⟨a,ha,ta,fa⟩ := ia inputs locals
    obtain ⟨b,hb,tb,fb⟩ := ib (inputs.nextState closed) (locals.nextState closed)
    have underRuntime (scope : Scope) : (Scope.push none scope).runtime env setup.conversion exposure =
        underFunctions (scope.runtime env setup.conversion exposure) := by
      funext n; cases n <;> rfl
    rw [underRuntime] at hb
    obtain ⟨result,parsed,typed,form,q⟩ := FunctionSyntax.stepSequence_complete_code setup library closed fresh exposure inputs ta tb fb ha hb binder info
    exact ⟨result,parsed,typed,form⟩
  | @forStatic ctx p σ scope original requirements a b c st start stop stride current body kn tn ki ti checked ih =>
    obtain ⟨b,hb,tb,fb⟩ := ih (For.nextInputs inputs closed library.scalars.word library.cons)
      ((locals.nextWord closed).nextState closed)
    have underRuntime (scope : Scope) : (Scope.push none scope).runtime env setup.conversion exposure =
        underFunctions (scope.runtime env setup.conversion exposure) := by
      funext n; cases n <;> rfl
    rw [underRuntime,underRuntime] at hb
    obtain ⟨target,_,_⟩ := StructuralLoop.next_typed inputs closed Arithmetic.SourceCasts.closed
      library.scalars.word library.returns.state library.cons tb
    obtain ⟨piece,parsed,⟨typed⟩,code⟩ := StructuralLoop.mapped_forStatic_complete_code inputs closed Arithmetic.SourceCasts.closed
      (fun _ _ _ h => For.Casts.base (.base (.source h))) start stop stride library.scalars.word library.returns.state library.cons tb
      (.continuation inputs target (b.represented.property.closed 0 b.closed) tb.value fb)
      library.forFact library.forConstructor library.range library.forHeader.header_typed
      coverage exposure kn tn ki ti current hb
    exact ⟨piece,parsed,typed,ScopedSyntax.head_form fresh typed.sourceCore.property (by rw [StructuralLoop.substitute_forStatic]; rfl) (by simp)⟩
  | @unitBody ctx σ scope b requirements p next binder info ih =>
    obtain ⟨b,hb,tb,fb⟩ := ih (inputs.lift closed UnitStep.unitType) (locals.lift closed UnitStep.unitType)
    have underRuntime (scope : Scope) : (Scope.push none scope).runtime env setup.conversion exposure =
        underFunctions (scope.runtime env setup.conversion exposure) := by
      funext n; cases n <;> rfl
    rw [underRuntime] at hb
    have eval := eval_cast_typed (inputs.lift closed UnitStep.unitType) library.eval tb.target
    have beta := For.Casts.unitContinuation (setup := setup) library.units false eval tb.value fb fresh.unit
    have codeClosed := b.represented.property.closed 0 b.closed
    obtain ⟨piece,parsed,⟨typed⟩,code⟩ := StructuralUnit.mapped_complete_code false inputs closed Arithmetic.SourceCasts.closed
      (fun _ _ _ h => For.Casts.base (.base (.source h))) library.units library.steps library.bind
      ⟨tb.sourceCore,tb.value,tb.target,tb.proof⟩
      (by simpa only [StructuralUnit.continuationType,StructuralUnit.lhs,For.unitRequired,
        InputsTyped.lift,Arithmetic.continuationValue,VExpr.lift,VExpr.liftN,UnitStep.unitType,
        codeClosed.liftN_eq (Nat.zero_le _)] using beta)
      (library.unitFact false) coverage exposure binder info hb
    exact ⟨piece,parsed,⟨typed.sourceCore,typed.value,typed.target,typed.proof⟩,
      ScopedSyntax.head_form fresh typed.sourceCore.property (by rw [StructuralUnit.substitute_source]; rfl) (by simp)⟩
  | @unitLoop ctx σ scope b requirements p next binder info ih =>
    obtain ⟨b,hb,tb,fb⟩ := ih (inputs.lift closed UnitStep.unitType) (locals.lift closed UnitStep.unitType)
    have underRuntime (scope : Scope) : (Scope.push none scope).runtime env setup.conversion exposure =
        underFunctions (scope.runtime env setup.conversion exposure) := by
      funext n; cases n <;> rfl
    rw [underRuntime] at hb
    have eval := eval_cast_typed (inputs.lift closed UnitStep.unitType) library.eval tb.target
    have beta := For.Casts.unitContinuation (setup := setup) library.units true eval tb.value fb fresh.unit
    have codeClosed := b.represented.property.closed 0 b.closed
    obtain ⟨piece,parsed,⟨typed⟩,code⟩ := StructuralUnit.mapped_complete_code true inputs closed Arithmetic.SourceCasts.closed
      (fun _ _ _ h => For.Casts.base (.base (.source h))) library.units library.steps library.bind
      ⟨tb.sourceCore,tb.value,tb.target,tb.proof⟩
      (by simpa only [StructuralUnit.continuationType,StructuralUnit.lhs,For.unitRequired,
        InputsTyped.lift,Arithmetic.continuationValue,VExpr.lift,VExpr.liftN,UnitStep.unitType,
        codeClosed.liftN_eq (Nat.zero_le _)] using beta)
      (library.unitFact true) coverage exposure binder info hb
    exact ⟨piece,parsed,⟨typed.sourceCore,typed.value,typed.target,typed.proof⟩,
      ScopedSyntax.head_form fresh typed.sourceCore.property (by rw [StructuralUnit.substitute_source]; rfl) (by simp)⟩
  | @forRange ctx p σ scope original requirements n st kind count current body kn tn ki ti checked ih =>
    obtain ⟨c,hc,⟨tc⟩⟩ := ScopedSyntax.scalar_complete setup library closed fresh exposure inputs locals count
    let nextInputs := kind.nextInputs inputs closed library.scalars.toSignatures library.naturalLoops library.cons
    let nextLocals := kind.nextLocals locals closed library.scalars.toSignatures library.naturalLoops
    have child : ∃ b, StructuralBody.visit env setup.conversion exposure original (kind.context ctx) (kind.parameters p)
        kind.mode (under (under σ)) ((Scope.push none (Scope.push none scope)).runtime env setup.conversion exposure) = some b ∧
        ∃ typed : NaturalLoop.ChildCasts kind nextInputs b (Arithmetic.SourceCasts env) (For.Casts setup),
          Arithmetic.ValueForm setup (kind.context ctx) typed.sourceCore.val (optionType kind.result) := by
      cases kind with
      | forIn => exact ih nextInputs nextLocals
      | fold => exact ih nextInputs nextLocals
    obtain ⟨b,hb,tb,fb⟩ := child
    have underRuntime (scope : Scope) : (Scope.push none scope).runtime env setup.conversion exposure =
        underFunctions (scope.runtime env setup.conversion exposure) := by
      funext n; cases n <;> rfl
    rw [underRuntime,underRuntime] at hb
    have beta := NaturalLoop.continuation_cast setup inputs kind closed library.scalars.toSignatures
      library.naturalLoops library.steps library.cons library.eval fresh.nat fresh.state tb fb
    obtain ⟨piece,parsed,⟨typed⟩,code⟩ := NaturalLoop.mapped_forRange_complete_code inputs kind closed (fun _ _ _ h => For.Casts.base (.base (.source h)))
      library.scalars.toSignatures library.naturalLoops library.forHeader library.reads library.steps.state
      library.cons tc tb beta coverage exposure kn tn ki ti current hc hb
    refine ⟨piece,parsed,typed,?_⟩
    · cases kind <;> exact ScopedSyntax.head_form fresh typed.sourceCore.property
        (by rw [NaturalLoop.Kind.substitute_source]; rfl) (by simp)
  | @letValue ctx p σ scope b requirements v annotation value next binder flag checked ih =>
    obtain ⟨a,ha,⟨ta⟩⟩ := ScopedSyntax.scalar_complete setup library closed fresh exposure inputs locals value
    obtain ⟨b,hb,tb,fb⟩ := ih
      (annotation.nextInputs inputs closed library.scalars.toSignatures library.cons)
      (annotation.nextLocals locals closed)
    have underRuntime (scope : Scope) : (Scope.push none scope).runtime env setup.conversion exposure =
        underFunctions (scope.runtime env setup.conversion exposure) := by
      funext n; cases n <;> rfl
    rw [underRuntime] at hb
    obtain ⟨result,parsed,typed,form,q⟩ := FunctionSyntax.letValue_complete_code annotation setup library closed fresh exposure inputs ta tb fb ha hb binder flag
    exact ⟨result,parsed,typed,form⟩
  | @bindValue ctx p σ scope b requirements v annotation value next binder info checked ih =>
    obtain ⟨a,ha,⟨ta⟩⟩ := ScopedSyntax.read_complete setup library closed fresh exposure inputs locals value
    obtain ⟨b,hb,tb,fb⟩ := ih
      (annotation.nextInputs inputs closed library.scalars.toSignatures library.cons)
      (annotation.nextLocals locals closed)
    have underRuntime (scope : Scope) : (Scope.push none scope).runtime env setup.conversion exposure =
        underFunctions (scope.runtime env setup.conversion exposure) := by
      funext n; cases n <;> rfl
    rw [underRuntime] at hb
    cases annotation with
    | word =>
      obtain ⟨piece,parsed,typed,form,q⟩ := FunctionSyntax.readWord_complete_code setup library closed fresh exposure inputs ta tb fb ha hb binder info
      exact ⟨piece,parsed,typed,form⟩
    | bitvec =>
      obtain ⟨piece,parsed,typed,form,q⟩ := WordBinder.mapped_bind_bits_complete_code setup library.scalars.toSignatures
        library.bind inputs closed library.cons library.returns.state library.eq library.eval
        library.bindValueFact library.letValueConstructor fresh.state (fresh.value _ (by simp))
        coverage exposure ta (value.valueForm fresh ta.sourceCore.property) tb fb ha hb binder info
      exact ⟨piece,parsed,typed,form⟩
  | @stepBindValue ctx p σ scope b requirements v annotation value next binder info checked ih =>
    obtain ⟨a,ha,⟨ta⟩⟩ := ScopedSyntax.read_complete setup library closed fresh exposure inputs locals value
    obtain ⟨b,hb,tb,fb⟩ := ih
      (annotation.nextInputs inputs closed library.scalars.toSignatures library.cons)
      (annotation.nextLocals locals closed)
    have underRuntime (scope : Scope) : (Scope.push none scope).runtime env setup.conversion exposure =
        underFunctions (scope.runtime env setup.conversion exposure) := by
      funext n; cases n <;> rfl
    rw [underRuntime] at hb
    cases annotation with
    | word =>
      obtain ⟨piece,parsed,typed,form,q⟩ := FunctionSyntax.stepReadWord_complete_code setup library closed fresh exposure inputs ta tb fb ha hb binder info
      exact ⟨piece,parsed,typed,form⟩
    | bitvec =>
      obtain ⟨piece,parsed,typed,form,q⟩ := WordBinder.mapped_step_bind_bits_complete_code setup library.scalars.toSignatures
        library.bind inputs closed library.cons library.steps library.eq library.eval
        library.stepBindValue library.letValueConstructor (fresh.readAux _ (by simp)) (fresh.value _ (by simp))
        coverage exposure ta (value.valueForm fresh ta.sourceCore.property) tb fb ha hb binder info
      exact ⟨piece,parsed,typed,form⟩
  | @stepLetValue ctx p σ scope b requirements v annotation value next binder flag checked ih =>
    obtain ⟨a,ha,⟨ta⟩⟩ := ScopedSyntax.scalar_complete setup library closed fresh exposure inputs locals value
    obtain ⟨b,hb,tb,fb⟩ := ih
      (annotation.nextInputs inputs closed library.scalars.toSignatures library.cons)
      (annotation.nextLocals locals closed)
    have underRuntime (scope : Scope) : (Scope.push none scope).runtime env setup.conversion exposure =
        underFunctions (scope.runtime env setup.conversion exposure) := by
      funext n; cases n <;> rfl
    rw [underRuntime] at hb
    obtain ⟨result,parsed,typed,form,q⟩ := FunctionSyntax.stepLetValue_complete_code annotation setup library closed fresh exposure inputs ta tb fb ha hb binder flag
    exact ⟨result,parsed,typed,form⟩
  | @sequence ctx p σ scope a requirements b first next binder info ia ib =>
    obtain ⟨a,ha,ta,fa⟩ := ia inputs locals
    obtain ⟨b,hb,tb,fb⟩ := ib (inputs.nextState closed) (locals.nextState closed)
    have underRuntime (scope : Scope) : (Scope.push none scope).runtime env setup.conversion exposure =
        underFunctions (scope.runtime env setup.conversion exposure) := by
      funext n; cases n <;> rfl
    rw [underRuntime] at hb
    obtain ⟨result,parsed,typed,form,q⟩ := FunctionSyntax.sequence_complete_code setup library closed fresh exposure inputs ta tb fb ha hb binder info
    exact ⟨result,parsed,typed,form⟩
  | @branch ctx p σ scope a requirements b v d value decision yes no checked ia ib =>
    obtain ⟨e,he,⟨te⟩⟩ := ScopedSyntax.scalar_complete setup library closed fresh exposure inputs locals value
    obtain ⟨a,ha,ta,fa⟩ := ia inputs locals
    obtain ⟨b,hb,tb,fb⟩ := ib inputs locals
    obtain ⟨result,parsed,typed,form,q⟩ := FunctionSyntax.branch_complete_code setup library closed fresh exposure inputs te ta tb decision he ha hb
    exact ⟨result,parsed,typed,form⟩
  | @booleanBranch ctx p σ scope a requirements b v value yes no checked ia ib =>
    obtain ⟨e,he,⟨te⟩⟩ := ScopedSyntax.scalar_complete setup library closed fresh exposure inputs locals value
    obtain ⟨a,ha,ta,fa⟩ := ia inputs locals
    obtain ⟨b,hb,tb,fb⟩ := ib inputs locals
    obtain ⟨pt,dt⟩ := library.decisions.condition_typed library.scalars.toSignatures te.value
    have represented : Represents (σ.apply (Branch.nativeBooleanDecision v))
        (Branch.booleanDecision te.sourceCore.val) := by
      have substituted : σ.apply (Branch.nativeBooleanDecision v) = Branch.nativeBooleanDecision (σ.apply v) := by
        cases σ <;> rfl
      rw [substituted]
      exact Branch.booleanDecision_represents te.sourceCore.property
    obtain ⟨result,parsed,typed,form,q⟩ := FunctionSyntax.branch_typed_complete_code setup library closed fresh exposure inputs te ta tb represented pt dt he ha hb
    exact ⟨result,parsed,typed,form⟩
  | @annotatedBooleanBranch ctx p σ scope a requirements b v valueCore annotation operand value represented valueTyped valueShape yes no checked ia ib =>
    obtain ⟨e,he,⟨te⟩⟩ := ScopedSyntax.scalar_complete setup library closed fresh exposure inputs locals value
    obtain ⟨a,ha,ta,fa⟩ := ia inputs locals
    obtain ⟨b,hb,tb,fb⟩ := ib inputs locals
    have same := te.sourceCore.property.unique represented
    rw [← same] at valueTyped valueShape
    have form := valueShape.toValueForm setup fresh.scalar
    obtain ⟨_,dt⟩ := AnnotatedCondition.condition_typed library.decisions library.scalars.toSignatures annotation te.value
    have dr : Represents (σ.apply (AnnotatedCondition.nativeDecision annotation v))
        (AnnotatedCondition.decision annotation te.sourceCore.val) := by
      have sub : σ.apply (AnnotatedCondition.nativeDecision annotation v) =
          AnnotatedCondition.nativeDecision annotation (σ.apply v) := by cases σ <;> cases annotation <;> rfl
      rw [sub]
      exact AnnotatedCondition.decision_represents annotation te.sourceCore.property
    have df : ValueForm setup ctx (AnnotatedCondition.decision annotation te.sourceCore.val)
        (.app (.const ``Decidable []) (AnnotatedCondition.condition annotation te.sourceCore.val)) :=
      .constant rfl (fresh.condition _ (by simp)) (by decide)
    obtain ⟨result,parsed,typed,form,q⟩ := AnnotatedBranch.visit_complete_code setup library closed fresh exposure
      inputs annotation operand te ta tb dr valueTyped form fa fb dt df he ha hb
    exact ⟨result,parsed,typed,form⟩
  | @annotatedStepBooleanBranch ctx p σ scope a requirements b v valueCore annotation operand value represented valueTyped valueShape yes no checked ia ib =>
    obtain ⟨e,he,⟨te⟩⟩ := ScopedSyntax.scalar_complete setup library closed fresh exposure inputs locals value
    obtain ⟨a,ha,ta,fa⟩ := ia inputs locals
    obtain ⟨b,hb,tb,fb⟩ := ib inputs locals
    have same := te.sourceCore.property.unique represented
    rw [← same] at valueTyped valueShape
    have form := valueShape.toValueForm setup fresh.scalar
    obtain ⟨_,dt⟩ := AnnotatedCondition.condition_typed library.decisions library.scalars.toSignatures annotation te.value
    have dr : Represents (σ.apply (AnnotatedCondition.nativeDecision annotation v))
        (AnnotatedCondition.decision annotation te.sourceCore.val) := by
      have sub : σ.apply (AnnotatedCondition.nativeDecision annotation v) =
          AnnotatedCondition.nativeDecision annotation (σ.apply v) := by cases σ <;> cases annotation <;> rfl
      rw [sub]
      exact AnnotatedCondition.decision_represents annotation te.sourceCore.property
    have df : ValueForm setup ctx (AnnotatedCondition.decision annotation te.sourceCore.val)
        (.app (.const ``Decidable []) (AnnotatedCondition.condition annotation te.sourceCore.val)) :=
      .constant rfl (fresh.condition _ (by simp)) (by decide)
    obtain ⟨result,parsed,typed,form,q⟩ := AnnotatedBranch.Loop.visit_complete_code setup library closed fresh exposure
      inputs annotation operand te ta tb dr valueTyped form fa fb dt df he ha hb
    exact ⟨result,parsed,typed,form⟩
  | @stepBooleanBranch ctx p σ scope a requirements b v value yes no checked ia ib =>
    obtain ⟨e,he,⟨te⟩⟩ := ScopedSyntax.scalar_complete setup library closed fresh exposure inputs locals value
    obtain ⟨a,ha,ta,fa⟩ := ia inputs locals
    obtain ⟨b,hb,tb,fb⟩ := ib inputs locals
    obtain ⟨pt,dt⟩ := library.decisions.condition_typed library.scalars.toSignatures te.value
    have represented : Represents (σ.apply (Branch.nativeBooleanDecision v))
        (Branch.booleanDecision te.sourceCore.val) := by
      have substituted : σ.apply (Branch.nativeBooleanDecision v) = Branch.nativeBooleanDecision (σ.apply v) := by
        cases σ <;> rfl
      rw [substituted]
      exact Branch.booleanDecision_represents te.sourceCore.property
    obtain ⟨result,parsed,typed,form,q⟩ := FunctionSyntax.stepBranch_complete_code setup library closed fresh exposure inputs te ta tb represented pt dt he ha hb
    exact ⟨result,parsed,typed,form⟩
  | @retainedCall mode scope σ depth bindings arity functions ctx p finalCtx finalInputs finalArgs requirements u body bodyCore domain first rest domains fn argument allowed binding coherent arguments next count dt bt ft ats tc pt rr sr ih =>
    obtain ⟨sw,nw,cw,qw,arguments⟩ := arguments
    have endpoint : ∀ finalTyped : InputsTyped env finalCtx finalInputs,
        ScalarSyntax.Locals env finalCtx finalInputs →
        ∃ piece, visit env setup.conversion exposure body finalCtx finalInputs mode
          (closureSubstitution depth finalCtx.length bindings finalArgs)
          ((functions.parameters finalArgs.length).runtime env setup.conversion exposure) = some piece ∧
          RetainedCasts setup finalTyped mode
            ((closureSubstitution depth finalCtx.length bindings finalArgs).apply body) piece := by
      intro finalTyped finalLocals
      have result := ih finalTyped finalLocals
      cases mode with
      | value => exact False.elim (allowed rfl)
      | body | step =>
        obtain ⟨piece,success,typed,form⟩ := result
        exact ⟨piece,success,typed,form⟩
    obtain ⟨⟨finalTyped⟩,⟨finalLocals⟩⟩ := arguments.endpointInputs library closed inputs locals
    obtain ⟨last,lastParsed,_⟩ := endpoint finalTyped finalLocals
    obtain ⟨piece,success,typed,_⟩ := binding.retained_call_from_body fn argument allowed coherent
      arguments count dt bt ft ats tc pt rr sr setup library closed fresh exposure inputs locals
      (quotation := last.code) (by
        intro finalTyped finalLocals
        obtain ⟨piece,parsed,typed⟩ := endpoint finalTyped finalLocals
        have same := Option.some.inj (parsed.symm.trans lastParsed)
        exact ⟨piece,parsed,typed,congrArg Piece.code same⟩)
    cases mode with
    | value => exact False.elim (allowed rfl)
    | body | step =>
      obtain ⟨typed,form⟩ := typed
      exact ⟨piece,success,typed,form⟩
  | @functionLet scope σ closure ctx p requirements u sourceBody functionValue domain codomain binder ty value next flag binding tail typeRep typeTyped bodyTyped valueTyped reducedRep sourceRep ih =>
    obtain ⟨piece,parsed,typed,form⟩ := ih inputs locals
    obtain ⟨result,success,codeSame,resultTyped,resultForm⟩ := function_let_step_complete setup
      library.steps.state library.steps.option library.eq library.eval fresh.state coverage exposure binder ty value next flag
      inputs typeRep typeTyped bodyTyped valueTyped reducedRep sourceRep typed form (fs := scope.runtime env setup.conversion exposure) (by
        dsimp only
        rw [binding.construct]
        exact parsed)
    exact ⟨result,success,resultTyped,resultForm⟩
  | @stepFunctionLet scope σ closure ctx p requirements u sourceBody functionValue domain codomain binder ty value next flag binding tail typeRep typeTyped bodyTyped valueTyped reducedRep sourceRep ih =>
    obtain ⟨piece,parsed,typed,form⟩ := ih inputs locals
    obtain ⟨result,success,codeSame,resultTyped,resultForm⟩ := step_functionLet_complete setup
      library.steps library.eq library.eval fresh.state coverage exposure binder ty value next flag
      inputs typeRep typeTyped bodyTyped valueTyped reducedRep sourceRep typed form (fs := scope.runtime env setup.conversion exposure) (by
        dsimp only
        rw [binding.construct]
        exact parsed)
    exact ⟨result,success,resultTyped,resultForm⟩

def sourceResultType (mode : Mode) : VExpr :=
  match mode with | .body => optionType stateType | .step => optionType Step.stepState | .value => stateType

/-- Source typing in all three existing modes, projected from the common
syntax induction. No generated artifact is required by the caller. -/
theorem Syntax.sourceTyping (source : Syntax env ctx p σ scope raw requirements mode)
    (setup : AliasSetup env) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (fresh : ScopedSyntax.Fresh setup) (exposure : Exposure env)
    (inputs : InputsTyped env ctx p) (locals : ScalarSyntax.Locals env ctx p) :
    ∃ core, Represents (σ.apply raw) core ∧
      CastTyping env 0 (SourceCasts env) ctx core
        (sourceResultType mode) := by
  have out := syntax_complete source setup library closed fresh exposure inputs locals
  cases mode with
  | body | step =>
    obtain ⟨piece,parsed,typed,shape⟩ := out
    exact ⟨typed.sourceCore.val,typed.sourceCore.property,typed.value⟩
  | value =>
    obtain ⟨piece,parsed,⟨typed⟩⟩ := out
    exact ⟨typed.sourceCore.val,typed.sourceCore.property,typed.value⟩


/-- Source typing is a projection of the same syntax induction as success;
no separate body derivation or pre-existing compiler result is required. -/
theorem Syntax.bodyTyping (source : Syntax env ctx p σ scope raw requirements)
    (setup : AliasSetup env) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (fresh : ScopedSyntax.Fresh setup) (exposure : Exposure env)
    (inputs : InputsTyped env ctx p) (locals : ScalarSyntax.Locals env ctx p) :
    ∃ core, Represents (σ.apply raw) core ∧
      CastTyping env 0 (SourceCasts env) ctx core (optionType stateType) :=
  source.sourceTyping setup library closed fresh exposure inputs locals

theorem lambdaTypingFromBody {functionBody : Lean.Expr} {functionSubstitution : Substitution}
    (library : ScopedSyntax.Library env) (closed : ClosedConstantTypes env)
    (bodyEvidence : ∃ core, Represents (functionSubstitution.apply functionBody) core ∧
      CastTyping env 0 (SourceCasts env) (domains.reverse ++ ctx) core (optionType stateType))
    (shape : LambdaSource value nativeDomains (functionSubstitution.apply functionBody))
    (represented : List.Forall₂ Represents nativeDomains domains)
    (parameters : ∀ d ∈ domains, ∃ u, CastTyping env 0 (SourceCasts env) [] d (.sort u)) :
    ∃ functionCore u, Represents value functionCore ∧
      CastTyping env 0 (SourceCasts env) ctx functionCore
        (domains.foldr VExpr.forallE (optionType stateType)) ∧
      CastTyping env 0 (SourceCasts env) ctx
        (domains.foldr VExpr.forallE (optionType stateType)) (.sort u) := by
  obtain ⟨core,rep,typed⟩ := bodyEvidence
  obtain ⟨functionRep,functionTyped⟩ := lambdaSource_typed shape represented closed parameters rep typed
  have resultTyped : CastTyping env 0 (SourceCasts env) [] (optionType stateType) (.sort (.succ .zero)) :=
    .application (.constant library.steps.option (by simp; trivial) rfl)
      (.constant library.returns.state (by simp) rfl)
  obtain ⟨level,typeTyped⟩ := functionType_typed domains closed parameters resultTyped (ctx := ctx)
  exact ⟨_,level,functionRep,functionTyped,typeTyped⟩

theorem Syntax.lambdaTyping {functionBody : Lean.Expr}
    (functionSource : Syntax env (domains.reverse ++ ctx) functionInputs
      functionSubstitution functionScope functionBody requirements)
    (setup : AliasSetup env) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (fresh : ScopedSyntax.Fresh setup) (exposure : Exposure env)
    (inputs : InputsTyped env (domains.reverse ++ ctx) functionInputs)
    (locals : ScalarSyntax.Locals env (domains.reverse ++ ctx) functionInputs)
    (shape : LambdaSource value nativeDomains (functionSubstitution.apply functionBody))
    (represented : List.Forall₂ Represents nativeDomains domains)
    (parameters : ∀ d ∈ domains, ∃ u, CastTyping env 0 (SourceCasts env) [] d (.sort u)) :
    ∃ functionCore u, Represents value functionCore ∧
      CastTyping env 0 (SourceCasts env) ctx functionCore
        (domains.foldr VExpr.forallE (optionType stateType)) ∧
      CastTyping env 0 (SourceCasts env) ctx
        (domains.foldr VExpr.forallE (optionType stateType)) (.sort u) :=
  lambdaTypingFromBody library closed
    (functionSource.bodyTyping setup library closed fresh exposure inputs locals) shape represented parameters

/-- A single function-let source construction for ordinary continuations
and loop continuations. The helper value retains its ordinary Option State
type; only the enclosing continuation's result changes. -/
theorem Syntax.functionLetFromLambdaPaired {functionBody : Lean.Expr} {domain : VExpr}
    (mode : Mode) (notValue : mode ≠ .value)
    (setup : AliasSetup env) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (fresh : ScopedSyntax.Fresh setup) (exposure : Exposure env)
    (binder : Lean.Name) (ty value next : Lean.Expr) (flag : Bool)
    (binding : BindingValue scope ctx.length σ value closure)
    (tail : Syntax env (mode := mode) ctx p (letSubstitution σ value) (.push (some closure) scope) next requirements ∧
      ∃ sourceBody, Represents ((under σ).apply next) sourceBody ∧
        CastTyping env 0 (SourceCasts env)
          ((.forallE domain (domains.foldr VExpr.forallE (optionType stateType)))::ctx)
          sourceBody (sourceResultType mode))
    (functionSource : Syntax env ((domain::domains).reverse ++ ctx) functionInputs
      functionSubstitution functionScope functionBody functionRequirements)
    (inputs : InputsTyped env ((domain::domains).reverse ++ ctx) functionInputs)
    (locals : ScalarSyntax.Locals env ((domain::domains).reverse ++ ctx) functionInputs)
    (shape : LambdaSource (σ.apply value) nativeDomains (functionSubstitution.apply functionBody))
    (represented : List.Forall₂ Represents nativeDomains (domain::domains))
    (parameters : ∀ d ∈ domain::domains, ∃ u, CastTyping env 0 (SourceCasts env) [] d (.sort u))
    (typeRep : Represents (σ.apply ty) (.forallE domain (domains.foldr VExpr.forallE (optionType stateType)))) :
    Syntax env (mode := mode) ctx p σ scope (.letE binder ty value next flag) requirements := by
  obtain ⟨tail,sourceBody,bodyRep,bodyTyped⟩ := tail
  obtain ⟨functionCore,level,functionRep,functionTyped,typeTyped⟩ :=
    functionSource.lambdaTyping setup library closed fresh exposure inputs locals shape represented parameters
  obtain ⟨reduced,original⟩ := let_representations (binder := binder) (ty := ty) (flag := flag)
    typeRep functionRep bodyRep
  cases mode with
  | body => exact .functionLet binder ty value next flag binding tail typeRep typeTyped bodyTyped functionTyped reduced original
  | step => exact .stepFunctionLet binder ty value next flag binding tail typeRep typeTyped bodyTyped functionTyped reduced original
  | value => exact False.elim (notValue rfl)


/-- Compatibility interface; source continuation construction uses the paired rule. -/
theorem Syntax.functionLetFromLambdaMode {functionBody : Lean.Expr} {sourceBody domain : VExpr}
    (mode : Mode) (notValue : mode ≠ .value)
    (setup : AliasSetup env) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (fresh : ScopedSyntax.Fresh setup) (exposure : Exposure env)
    (binder : Lean.Name) (ty value next : Lean.Expr) (flag : Bool)
    (binding : BindingValue scope ctx.length σ value closure)
    (tail : Syntax env (mode := mode) ctx p (letSubstitution σ value) (.push (some closure) scope) next requirements)
    (functionSource : Syntax env ((domain::domains).reverse ++ ctx) functionInputs
      functionSubstitution functionScope functionBody functionRequirements)
    (inputs : InputsTyped env ((domain::domains).reverse ++ ctx) functionInputs)
    (locals : ScalarSyntax.Locals env ((domain::domains).reverse ++ ctx) functionInputs)
    (shape : LambdaSource (σ.apply value) nativeDomains (functionSubstitution.apply functionBody))
    (represented : List.Forall₂ Represents nativeDomains (domain::domains))
    (parameters : ∀ d ∈ domain::domains, ∃ u, CastTyping env 0 (SourceCasts env) [] d (.sort u))
    (typeRep : Represents (σ.apply ty) (.forallE domain (domains.foldr VExpr.forallE (optionType stateType))))
    (bodyRep : Represents ((under σ).apply next) sourceBody)
    (bodyTyped : CastTyping env 0 (SourceCasts env)
      ((.forallE domain (domains.foldr VExpr.forallE (optionType stateType)))::ctx)
      sourceBody (sourceResultType mode)) :
    Syntax env (mode := mode) ctx p σ scope (.letE binder ty value next flag) requirements := by
  exact functionLetFromLambdaPaired mode notValue setup library closed fresh exposure
    binder ty value next flag binding ⟨tail,sourceBody,bodyRep,bodyTyped⟩ functionSource
    inputs locals shape represented parameters typeRep

theorem Syntax.functionLetFromLambda {functionBody : Lean.Expr} {sourceBody domain : VExpr}
    (setup : AliasSetup env) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (fresh : ScopedSyntax.Fresh setup) (exposure : Exposure env)
    (binder : Lean.Name) (ty value next : Lean.Expr) (flag : Bool)
    (binding : BindingValue scope ctx.length σ value closure)
    (tail : Syntax env ctx p (letSubstitution σ value) (.push (some closure) scope) next requirements)
    (functionSource : Syntax env ((domain::domains).reverse ++ ctx) functionInputs
      functionSubstitution functionScope functionBody functionRequirements)
    (inputs : InputsTyped env ((domain::domains).reverse ++ ctx) functionInputs)
    (locals : ScalarSyntax.Locals env ((domain::domains).reverse ++ ctx) functionInputs)
    (shape : LambdaSource (σ.apply value) nativeDomains (functionSubstitution.apply functionBody))
    (represented : List.Forall₂ Represents nativeDomains (domain::domains))
    (parameters : ∀ d ∈ domain::domains, ∃ u, CastTyping env 0 (SourceCasts env) [] d (.sort u))
    (typeRep : Represents (σ.apply ty) (.forallE domain (domains.foldr VExpr.forallE (optionType stateType))))
    (bodyRep : Represents ((under σ).apply next) sourceBody)
    (bodyTyped : CastTyping env 0 (SourceCasts env)
      ((.forallE domain (domains.foldr VExpr.forallE (optionType stateType)))::ctx)
      sourceBody (optionType stateType)) :
    Syntax env ctx p σ scope (.letE binder ty value next flag) requirements :=
  functionLetFromLambdaMode .body (by decide) setup library closed fresh exposure
    binder ty value next flag binding tail functionSource inputs locals shape represented parameters typeRep bodyRep bodyTyped

/-- One derivation of intermediate application types for body and loop-body
helpers. The original body syntax is shared with the respective call rule. -/
theorem Syntax.helperPrefixes {functionBody : Lean.Expr} {coreBody : VExpr}
    {domains actual args : List VExpr} {bodyInputs : Nat → Inputs}
    (setup : AliasSetup env) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (fresh : ScopedSyntax.Fresh setup) (exposure : Exposure env)
    (parameterLength : domains.length = args.length)
    (arguments : List.Forall₂ (fun ty arg => CastTyping env 0 (SourceCasts env) ctx arg ty) actual args)
    (parameters : ∀ d ∈ domains ++ actual, ∃ u, CastTyping env 0 (SourceCasts env) [] d (.sort u))
    (bodies : ∀ n, n ≤ args.length → Syntax env ((actual.take n ++ domains.drop n).reverse ++ ctx)
      (bodyInputs n) .identity bodyScope functionBody bodyRequirements mode)
    (inputs : ∀ n, n ≤ args.length → InputsTyped env ((actual.take n ++ domains.drop n).reverse ++ ctx) (bodyInputs n))
    (locals : ∀ n, n ≤ args.length → ScalarSyntax.Locals env ((actual.take n ++ domains.drop n).reverse ++ ctx) (bodyInputs n))
    (bodyRep : Represents functionBody coreBody) :
    let resultType := sourceResultType mode
    CastTyping env 0 (SourceCasts env) (domains.reverse ++ ctx) coreBody resultType ∧
    (∀ before after, args = before ++ after →
      CastTyping env 0 (SourceCasts env) ctx
        (before.foldl LeanTypeReduction.applyReduced (domains.foldr VExpr.lam coreBody))
        ((domains.drop before.length).foldr VExpr.forallE resultType)) := by
  let resultType := sourceResultType mode
  have typedBodies : ∀ n, n ≤ args.length → CastTyping env 0 (SourceCasts env)
      ((actual.take n ++ domains.drop n).reverse ++ ctx) coreBody resultType := by
    intro n hn
    obtain ⟨core,rep,typed⟩ := (bodies n hn).sourceTyping setup library closed fresh exposure (inputs n hn) (locals n hn)
    exact rep.unique bodyRep ▸ typed
  have resultTyped : CastTyping env 0 (SourceCasts env) [] resultType (.sort (.succ .zero)) := by
    cases mode with
    | body => exact .application (.constant library.steps.option (by simp; trivial) rfl) (.constant library.returns.state (by simp) rfl)
    | step =>
      exact .application (.constant library.steps.option (by simp; trivial) rfl)
        (library.steps.step_typed.withCasts _)
    | value => exact .constant library.returns.state (by simp) rfl
  exact ⟨by simpa using typedBodies 0 (Nat.zero_le _),
    lambdaPrefixesFromBody domains actual args parameterLength arguments closed parameters resultTyped typedBodies⟩

/-- Call-time argument retention uses the same source-body typing induction
as ordinary helper calls. The endpoint is arbitrary retained Syntax, so State
updates, reads, branches, loops and nested calls compose without a new proof
of the whole call at each use. -/
theorem Syntax.retainedCallFromBodyTypes
    {body : Lean.Expr} {coreBody domain first : VExpr}
    {rest tailDomains actual : List VExpr}
    (library : ScopedSyntax.Library env) (closed : ClosedConstantTypes env)
    (fn argument : Lean.Expr) (modeAllowed : mode ≠ .value)
    (coherent : scope.Coherent ctx.length σ)
    (binding : BindingValue scope ctx.length σ fn.getAppFn (.captured depth captured arity body functions))
    (length : ((Lean.Expr.app fn argument).getAppArgs.toList.map σ.apply).length = arity)
    (retainedArgs : ArgumentBindings.Syntax env ctx p
      ((Lean.Expr.app fn argument).getAppArgs.toList.map σ.apply) [] finalCtx finalInputs finalArgs)
    (next : Syntax env (mode := mode) finalCtx finalInputs
      (closureSubstitution depth finalCtx.length captured finalArgs)
      (functions.parameters finalArgs.length) body requirements)
    (arguments : List.Forall₂ (fun ty arg => CastTyping env 0 (SourceCasts env) ctx arg ty) actual (first::rest))
    (checks : List.Forall₂ (fun ty arg => CheckedTyping env 0 (SourceCasts env) ctx arg ty) (domain::tailDomains) (first::rest))
    (parameterLength : (domain::tailDomains).length = (first::rest).length)
    (parameters : ∀ d ∈ (domain::tailDomains) ++ actual,
      ∃ u, CastTyping env 0 (SourceCasts env) [] d (.sort u))
    (typedBodies : ∀ n, n ≤ (first::rest).length →
      CastTyping env 0 (SourceCasts env) ((actual.take n ++ (domain::tailDomains).drop n).reverse ++ ctx)
        coreBody (sourceResultType mode))
    (argumentsRep : List.Forall₂ Represents
      ((Lean.Expr.app fn argument).getAppArgs.toList.map σ.apply) (first::rest))
    (functionRep : Represents (σ.apply fn.getAppFn) (.lam domain (tailDomains.foldr VExpr.lam coreBody))) :
    Syntax env (mode := mode) ctx p σ scope (.app fn argument) requirements := by
  have resultEq : sourceResultType mode =
      optionType (if mode == .step then Step.stepState else stateType) := by
    cases mode <;> first | rfl | exact False.elim (modeAllowed rfl)
  have resultTyped : CastTyping env 0 (SourceCasts env) []
      (optionType (if mode == .step then Step.stepState else stateType)) (.sort (.succ .zero)) := by
    cases mode with
    | value => exact False.elim (modeAllowed rfl)
    | body =>
      exact .application (.constant library.steps.option (by simp; trivial) rfl)
        (.constant library.returns.state (by simp) rfl)
    | step =>
      exact .application (.constant library.steps.option (by simp; trivial) rfl)
        (library.steps.step_typed.withCasts _)
  rw [resultEq] at typedBodies
  have typedBody := typedBodies 0 (Nat.zero_le _)
  simp only [List.take_zero,List.drop_zero,List.nil_append] at typedBody
  have prefixes := lambdaPrefixesFromBody (domain::tailDomains) actual (first::rest)
    parameterLength arguments closed parameters resultTyped typedBodies
  obtain ⟨level,domainTyped⟩ := parameters domain (by simp)
  have tailParameters := fun d (hd : d ∈ tailDomains) => parameters d (by simp [hd])
  have originalBody := lambdaTelescope_typed tailDomains closed tailParameters (ctx := domain::ctx)
    (by simpa [List.reverse_cons,List.append_assoc] using typedBody)
  have spine : Lean.Expr.app fn argument =
      (Lean.Expr.app fn argument).getAppArgs.toList.foldl Lean.Expr.app fn.getAppFn :=
    (application_spine (.app fn argument)).symm
  obtain ⟨reduced,source⟩ := binding.call_representations coherent spine argumentsRep
    (by simpa only [List.length_map] using length) functionRep
  cases checks with
  | cons firstCheck remainingChecks =>
    apply Syntax.retainedCall fn argument modeAllowed binding coherent retainedArgs next
      (by simpa only [List.length_map,Array.length_toList] using length)
      (domainTyped.in_context closed SourceCasts.closed (by trivial) ctx) originalBody firstCheck remainingChecks
      (functionType_suffix_closed tailDomains closed tailParameters resultTyped)
    · intro before after split nonempty
      simpa only [List.foldl_cons,List.foldr_cons,LeanTypeReduction.applyReduced,
        List.length_cons,List.drop_succ_cons] using
        prefixes (first::before) after (congrArg (List.cons first) split)
    · exact reduced
    · exact source


/-- Compatibility interface: original-body syntax supplies the common typed-body family. -/
theorem Syntax.retainedCallFromSourceBodies {body functionBody : Lean.Expr} {coreBody domain first : VExpr}
    {rest tailDomains actual : List VExpr} {bodyInputs : Nat → Inputs}
    {bodyScope : Scope} {bodyRequirements : Lean.Expr → Prop}
    (setup : AliasSetup env) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (fresh : ScopedSyntax.Fresh setup) (exposure : Exposure env)
    (fn argument : Lean.Expr) (modeAllowed : mode ≠ .value)
    (coherent : scope.Coherent ctx.length σ)
    (binding : BindingValue scope ctx.length σ fn.getAppFn (.captured depth captured arity body functions))
    (length : ((Lean.Expr.app fn argument).getAppArgs.toList.map σ.apply).length = arity)
    (retainedArgs : ArgumentBindings.Syntax env ctx p
      ((Lean.Expr.app fn argument).getAppArgs.toList.map σ.apply) [] finalCtx finalInputs finalArgs)
    (next : Syntax env (mode := mode) finalCtx finalInputs
      (closureSubstitution depth finalCtx.length captured finalArgs)
      (functions.parameters finalArgs.length) body requirements)
    (arguments : List.Forall₂ (fun ty arg => CastTyping env 0 (SourceCasts env) ctx arg ty) actual (first::rest))
    (checks : List.Forall₂ (fun ty arg => CheckedTyping env 0 (SourceCasts env) ctx arg ty) (domain::tailDomains) (first::rest))
    (parameterLength : (domain::tailDomains).length = (first::rest).length)
    (parameters : ∀ d ∈ (domain::tailDomains) ++ actual,
      ∃ u, CastTyping env 0 (SourceCasts env) [] d (.sort u))
    (bodies : ∀ n, n ≤ (first::rest).length →
      Syntax env ((actual.take n ++ (domain::tailDomains).drop n).reverse ++ ctx)
        (bodyInputs n) .identity bodyScope functionBody bodyRequirements mode)
    (inputs : ∀ n, n ≤ (first::rest).length →
      InputsTyped env ((actual.take n ++ (domain::tailDomains).drop n).reverse ++ ctx) (bodyInputs n))
    (locals : ∀ n, n ≤ (first::rest).length →
      ScalarSyntax.Locals env ((actual.take n ++ (domain::tailDomains).drop n).reverse ++ ctx) (bodyInputs n))
    (bodyRep : Represents functionBody coreBody)
    (argumentsRep : List.Forall₂ Represents
      ((Lean.Expr.app fn argument).getAppArgs.toList.map σ.apply) (first::rest))
    (functionRep : Represents (σ.apply fn.getAppFn) (.lam domain (tailDomains.foldr VExpr.lam coreBody))) :
    Syntax env (mode := mode) ctx p σ scope (.app fn argument) requirements := by
  apply Syntax.retainedCallFromBodyTypes library closed fn argument modeAllowed coherent binding length
    retainedArgs next arguments checks parameterLength parameters ?_ argumentsRep functionRep
  intro n hn
  obtain ⟨core,rep,typed⟩ := (bodies n hn).sourceTyping setup library closed fresh exposure (inputs n hn) (locals n hn)
  exact rep.unique bodyRep ▸ typed

/-- Source lambdas supply their own representation; users do not construct
an internal lambda core or intermediate beta-prefix types for retained calls. -/
theorem Syntax.retainedCallFromLambdaBodies {body functionBody : Lean.Expr} {domain first : VExpr}
    {rest tailDomains actual : List VExpr} {bodyInputs : Nat → Inputs}
    {bodyScope : Scope} {bodyRequirements : Lean.Expr → Prop}
    (setup : AliasSetup env) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (fresh : ScopedSyntax.Fresh setup) (exposure : Exposure env)
    (fn argument : Lean.Expr) (modeAllowed : mode ≠ .value)
    (coherent : scope.Coherent ctx.length σ)
    (binding : BindingValue scope ctx.length σ fn.getAppFn (.captured depth captured arity body functions))
    (length : ((Lean.Expr.app fn argument).getAppArgs.toList.map σ.apply).length = arity)
    (retainedArgs : ArgumentBindings.Syntax env ctx p
      ((Lean.Expr.app fn argument).getAppArgs.toList.map σ.apply) [] finalCtx finalInputs finalArgs)
    (next : Syntax env (mode := mode) finalCtx finalInputs
      (closureSubstitution depth finalCtx.length captured finalArgs)
      (functions.parameters finalArgs.length) body requirements)
    (arguments : List.Forall₂ (fun ty arg => CastTyping env 0 (SourceCasts env) ctx arg ty) actual (first::rest))
    (checks : List.Forall₂ (fun ty arg => CheckedTyping env 0 (SourceCasts env) ctx arg ty) (domain::tailDomains) (first::rest))
    (parameterLength : (domain::tailDomains).length = (first::rest).length)
    (parameters : ∀ d ∈ (domain::tailDomains) ++ actual,
      ∃ u, CastTyping env 0 (SourceCasts env) [] d (.sort u))
    (bodies : ∀ n, n ≤ (first::rest).length →
      Syntax env ((actual.take n ++ (domain::tailDomains).drop n).reverse ++ ctx)
        (bodyInputs n) .identity bodyScope functionBody bodyRequirements mode)
    (inputs : ∀ n, n ≤ (first::rest).length →
      InputsTyped env ((actual.take n ++ (domain::tailDomains).drop n).reverse ++ ctx) (bodyInputs n))
    (locals : ∀ n, n ≤ (first::rest).length →
      ScalarSyntax.Locals env ((actual.take n ++ (domain::tailDomains).drop n).reverse ++ ctx) (bodyInputs n))
    (argumentsRep : List.Forall₂ Represents
      ((Lean.Expr.app fn argument).getAppArgs.toList.map σ.apply) (first::rest))
    (shape : LambdaSource (σ.apply fn.getAppFn) nativeDomains functionBody)
    (domainRep : List.Forall₂ Represents nativeDomains (domain::tailDomains)) :
    Syntax env (mode := mode) ctx p σ scope (.app fn argument) requirements := by
  obtain ⟨core,rep,typed⟩ := (bodies 0 (Nat.zero_le _)).sourceTyping setup library closed fresh exposure (inputs 0 (Nat.zero_le _)) (locals 0 (Nat.zero_le _))
  have initial : CastTyping env 0 (SourceCasts env) ((domain::tailDomains).reverse ++ ctx) core (sourceResultType mode) := by simpa using typed
  obtain ⟨functionRep,_⟩ := lambdaSource_typed shape domainRep closed
    (fun d hd => parameters d (List.mem_append_left _ hd)) rep initial
  exact Syntax.retainedCallFromSourceBodies setup library closed fresh exposure fn argument modeAllowed coherent binding length retainedArgs next
    arguments checks parameterLength parameters bodies inputs locals rep argumentsRep functionRep


theorem complete (setup : Arithmetic.AliasSetup env) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (fresh : ScopedSyntax.Fresh setup) (exposure : Exposure env)
    (source : Syntax env ctx p σ scope raw requirements)
    (inputs : InputsTyped env ctx p) (locals : ScalarSyntax.Locals env ctx p) :
    ∃ piece, visit env setup.conversion exposure raw ctx p .body σ
      (scope.runtime env setup.conversion exposure) = some piece ∧
      ∃ typed : BodyCasts inputs piece (Arithmetic.SourceCasts env) (For.Casts setup),
        Arithmetic.ValueForm setup ctx typed.sourceCore.val (optionType stateType) :=
  syntax_complete source setup library closed fresh exposure inputs locals

end IRComparison.WordFrontend.FunctionSyntax
