import IRComparison.Frontend.WordFixedSequenceCompleteness
import IRComparison.Frontend.WordFunctionState
import IRComparison.Frontend.WordAnnotatedBranch
import IRComparison.Frontend.WordRetainedArguments

/-! Fixed-source generation through ordinary captured helper functions.
The closure environment contains source syntax, not successful parser results.
Its base cases use the existing structured source derivation, so declaration
and computation proofs are shared with the rest of the entry. -/
namespace IRComparison.WordFrontend.FixedFunctionCompleteness
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic StructuralBody StructuralSyntax FunctionSyntax
set_option maxHeartbeats 1800000
abbrev Meaning := FixedSequenceCompleteness.Meaning

inductive Source (ds : FixedMemory.Declarations) {env : VEnv} :
    List VExpr → Inputs → Substitution → Scope → Lean.Expr → Meaning → HybridWord.Cmd → Lean.Expr → (mode : Mode := .body) → Prop where
  | plain (body : FixedSequenceCompleteness.Source ds (env := env) mode ctx p raw native code quotation) :
      Source ds (env := env) ctx p .identity .empty raw native code quotation mode
  | base (head : HeadForm σ p raw)
      (body : FixedSequenceCompleteness.Source ds (env := env) .body ctx p (σ.apply raw) native code quotation) :
      Source ds (env := env) ctx p σ scope raw native code quotation
  | valueCurrent (current : σ.apply raw = p.s) :
      Source ds (env := env) ctx p σ scope raw (fun _ _ _ _ s => some s) .skip (.const ``HybridWord.Cmd.skip []) .value
  | valueAssign (register : Nat) (rn : NatNotation)
      (current : σ.apply st = p.s)
      (value : FixedScalarCompleteness.Scoped env ctx p (σ.apply v) f vc vq) :
      Source ds (env := env) ctx p σ scope (app ``HybridWord.State.set [st,rn.native register,v])
        (fun i x y ls s => (f i x y s ls).bind (fun v => some (s.set register v)))
        (.assign register vc) (app ``HybridWord.Cmd.assign [rn.native register,vq]) .value
  | yield (value : Source ds (env := env) ctx p σ scope raw f code quotation .value) :
      Source ds (env := env) ctx p σ scope (Step.yieldSource raw) f code quotation .step
  | stepSequence (first : Source ds (env := env) ctx p σ scope a f ac aq)
      (next : Source ds (env := env) (stateType::ctx) {p.lift with s := .bvar 0}
        (under σ) (.push none scope) b g bc bq .step)
      (binder : Lean.Name) (info : Lean.BinderInfo) :
      Source ds (env := env) ctx p σ scope (StructuralStep.sequenceSource a (.lam binder state b info))
        (fun i x y ls s => (f i x y ls s).bind (g i x y ls)) (.seq ac bc) (app ``HybridWord.Cmd.seq [aq,bq]) .step
  | forStatic (start : FixedSequenceCompleteness.StaticBound (σ.apply a) startValue)
      (stop : FixedSequenceCompleteness.StaticBound (σ.apply b) stopValue)
      (stride : FixedSequenceCompleteness.StaticBound (σ.apply c) strideValue)
      (current : σ.apply st = p.s)
      (body : Source ds (env := env) (stateType::wordType::ctx) (For.parameters p)
        (under (under σ)) (.push none (.push none scope)) original f bc bq .step)
      (kn tn : Lean.Name) (ki ti : Lean.BinderInfo) :
      Source ds (env := env) ctx p σ scope (For.source a b c st (.lam kn word (.lam tn state original ti) ki))
        (fun i x y ls s => ForIn.forIn (HybridWord.range startValue stopValue strideValue) s
          (fun k t => WordLoopFacts.lift (f i x y (k::ls) t)))
        (.forStatic startValue stopValue strideValue bc)
        (app ``HybridWord.Cmd.forStatic [σ.apply a,σ.apply b,σ.apply c,bq])
  | unitBody (next : Source ds (env := env) (UnitStep.unitType::ctx) p.lift
      (under σ) (.push none scope) b g bc bq) (binder : Lean.Name) (info : Lean.BinderInfo) :
      Source ds (env := env) ctx p σ scope (StructuralUnit.source false binder b info) g bc bq
  | unitLoop (next : Source ds (env := env) (UnitStep.unitType::ctx) p.lift
      (under σ) (.push none scope) b g bc bq .step) (binder : Lean.Name) (info : Lean.BinderInfo) :
      Source ds (env := env) ctx p σ scope (StructuralUnit.source true binder b info) g bc bq .step
  | forRange (kind : NaturalLoop.Kind)
      (count : FixedScalarCompleteness.Scoped env ctx p (σ.apply n) f nc nq)
      (current : σ.apply st = p.s)
      (body : Source ds (env := env) (kind.context ctx) (kind.parameters p)
        (under (under σ)) (.push none (.push none scope)) original g bc bq kind.mode)
      (kn tn : Lean.Name) (ki ti : Lean.BinderInfo) :
      Source ds (env := env) ctx p σ scope (kind.source n st (kind.nativeLambda kn tn ki ti original))
        (fun i x y ls s => (f i x y s ls).bind (fun n =>
          FixedSequenceCompleteness.naturalRange kind n (fun k t => g i x y (BitVec.ofNat 32 k::ls) t) s))
        (.forRange nc bc) (app ``HybridWord.Cmd.forRange [nq,bq])
  | letValue (annotation : WordBinder.Annotation)
      (value : FixedScalarCompleteness.Scoped env ctx p (σ.apply v) f vc vq)
      (next : Source ds (env := env) (annotation.core::ctx) {p.lift with locals := .bvar 0::p.lift.locals}
        (under σ) (.push none scope) b g bc bq)
      (binder : Lean.Name) (flag : Bool) :
      Source ds (env := env) ctx p σ scope (WordBinder.letSource annotation binder v b flag)
        (fun i x y ls s => (f i x y s ls).bind (fun v => g i x y (v::ls) s))
        (.letValue vc bc) (app ``HybridWord.Cmd.letValue [vq,bq])
  | bindValue (annotation : WordBinder.Annotation)
      (value : FixedReadSourceCompleteness.Source ds (env := env) (ctx := ctx) p (σ.apply v) f vc vq)
      (next : Source ds (env := env) (annotation.core::ctx) {p.lift with locals := .bvar 0::p.lift.locals}
        (under σ) (.push none scope) b g bc bq)
      (binder : Lean.Name) (info : Lean.BinderInfo) :
      Source ds (env := env) ctx p σ scope (WordBinder.readSource annotation v (.lam binder annotation.native b info))
        (fun i x y ls s => (f i x y s ls).bind (fun v => g i x y (v::ls) s))
        (.letValue vc bc) (app ``HybridWord.Cmd.letValue [vq,bq])
  | stepBindValue (annotation : WordBinder.Annotation)
      (value : FixedReadSourceCompleteness.Source ds (env := env) (ctx := ctx) p (σ.apply v) f vc vq)
      (next : Source ds (env := env) (annotation.core::ctx) {p.lift with locals := .bvar 0::p.lift.locals}
        (under σ) (.push none scope) b g bc bq .step)
      (binder : Lean.Name) (info : Lean.BinderInfo) :
      Source ds (env := env) ctx p σ scope (WordBinder.stepReadSource annotation v (.lam binder annotation.native b info))
        (fun i x y ls s => (f i x y s ls).bind (fun v => g i x y (v::ls) s))
        (.letValue vc bc) (app ``HybridWord.Cmd.letValue [vq,bq]) .step
  | stepLetValue (annotation : WordBinder.Annotation)
      (value : FixedScalarCompleteness.Scoped env ctx p (σ.apply v) f vc vq)
      (next : Source ds (env := env) (annotation.core::ctx) {p.lift with locals := .bvar 0::p.lift.locals}
        (under σ) (.push none scope) b g bc bq .step)
      (binder : Lean.Name) (flag : Bool) :
      Source ds (env := env) ctx p σ scope (WordBinder.letSource annotation binder v b flag)
        (fun i x y ls s => (f i x y s ls).bind (fun v => g i x y (v::ls) s))
        (.letValue vc bc) (app ``HybridWord.Cmd.letValue [vq,bq]) .step
  | stateLet (value : Source ds (env := env) ctx p σ scope v f vc vq .value)
      (next : Source ds (env := env) (stateType::ctx) {p.lift with s := .bvar 0} (under σ) (.push none scope) b g bc bq)
      (notAlias : sameTerm (σ.apply v) p.s = false) (binder : Lean.Name) (flag : Bool) :
      Source ds (env := env) ctx p σ scope (StateLet.source binder v b flag)
        (fun i x y ls s => (f i x y ls s).bind (g i x y ls))
        (.seq vc bc) (app ``HybridWord.Cmd.seq [vq,bq])
  | stepStateLet (value : Source ds (env := env) ctx p σ scope v f vc vq .value)
      (next : Source ds (env := env) (stateType::ctx) {p.lift with s := .bvar 0} (under σ) (.push none scope) b g bc bq .step)
      (notAlias : sameTerm (σ.apply v) p.s = false) (binder : Lean.Name) (flag : Bool) :
      Source ds (env := env) ctx p σ scope (StructuralStateLet.Loop.source binder v b flag)
        (fun i x y ls s => (f i x y ls s).bind (g i x y ls))
        (.seq vc bc) (app ``HybridWord.Cmd.seq [vq,bq]) .step
  | stateAlias (current : σ.apply st = p.s)
      (next : Source ds (env := env) (stateType::ctx) {p.lift with s := .bvar 0}
        (under σ) (.push none scope) b g bc bq)
      (binder : Lean.Name) (flag : Bool) :
      Source ds (env := env) ctx p σ scope (.letE binder state st b flag) g bc bq
  | stepAlias (current : σ.apply st = p.s)
      (next : Source ds (env := env) (stateType::ctx) {p.lift with s := .bvar 0}
        (under σ) (.push none scope) b g bc bq .step)
      (binder : Lean.Name) (flag : Bool) :
      Source ds (env := env) ctx p σ scope (.letE binder state st b flag) g bc bq .step
  | sequence (first : Source ds (env := env) ctx p σ scope a f ac aq)
      (next : Source ds (env := env) (stateType::ctx) {p.lift with s := .bvar 0} (under σ) (.push none scope) b g bc bq)
      (binder : Lean.Name) (info : Lean.BinderInfo) :
      Source ds (env := env) ctx p σ scope (sequenceSource a (.lam binder state b info))
        (fun i x y ls s => (f i x y ls s).bind (g i x y ls)) (.seq ac bc) (app ``HybridWord.Cmd.seq [aq,bq])
  | branch (value : FixedScalarCompleteness.Scoped env ctx p (σ.apply v) f vc vq)
      (decision : ScalarSyntax.Decision env ctx (σ.apply v) (σ.apply d))
      (yes : Source ds (env := env) ctx p σ scope a g ac aq)
      (no : Source ds (env := env) ctx p σ scope b h bc bq) :
      Source ds (env := env) ctx p σ scope (Branch.source v d a b)
        (fun i x y ls s => (f i x y s ls).bind (fun v => if v != 0 then g i x y ls s else h i x y ls s))
        (.branch vc ac bc) (app ``HybridWord.Cmd.branch [vq,aq,bq])
  | booleanBranch (value : FixedScalarCompleteness.Scoped env ctx p (σ.apply v) f vc vq)
      (yes : Source ds (env := env) ctx p σ scope a g ac aq)
      (no : Source ds (env := env) ctx p σ scope b h bc bq) :
      Source ds (env := env) ctx p σ scope (Branch.source v (Branch.nativeBooleanDecision v) a b)
        (fun i x y ls s => (f i x y s ls).bind (fun v => if v != 0 then g i x y ls s else h i x y ls s))
        (.branch vc ac bc) (app ``HybridWord.Cmd.branch [vq,aq,bq])
  | annotatedBooleanBranch {valueCore : VExpr} (annotation operand : WordBinder.Annotation)
      (value : FixedScalarCompleteness.Scoped env ctx p (σ.apply v) f vc vq)
      (represented : Represents (σ.apply v) valueCore)
      (typed : CastTyping env 0 (SourceCasts env) ctx valueCore operand.core)
      (form : LexicalScalarSyntax.ValueShape env ctx valueCore operand.core)
      (yes : Source ds (env := env) ctx p σ scope a g ac aq)
      (no : Source ds (env := env) ctx p σ scope b h bc bq) :
      Source ds (env := env) ctx p σ scope
        (AnnotatedBranch.source annotation v (AnnotatedCondition.nativeDecision annotation v) a b)
        (fun i x y ls s => (f i x y s ls).bind (fun v => if v != 0 then g i x y ls s else h i x y ls s))
        (.branch vc ac bc) (app ``HybridWord.Cmd.branch [vq,aq,bq])
  | annotatedStepBooleanBranch {valueCore : VExpr} (annotation operand : WordBinder.Annotation)
      (value : FixedScalarCompleteness.Scoped env ctx p (σ.apply v) f vc vq)
      (represented : Represents (σ.apply v) valueCore)
      (typed : CastTyping env 0 (SourceCasts env) ctx valueCore operand.core)
      (form : LexicalScalarSyntax.ValueShape env ctx valueCore operand.core)
      (yes : Source ds (env := env) ctx p σ scope a g ac aq .step)
      (no : Source ds (env := env) ctx p σ scope b h bc bq .step) :
      Source ds (env := env) ctx p σ scope
        (AnnotatedBranch.Loop.source annotation v (AnnotatedCondition.nativeDecision annotation v) a b)
        (fun i x y ls s => (f i x y s ls).bind (fun v => if v != 0 then g i x y ls s else h i x y ls s))
        (.branch vc ac bc) (app ``HybridWord.Cmd.branch [vq,aq,bq]) .step
  | stepBooleanBranch (value : FixedScalarCompleteness.Scoped env ctx p (σ.apply v) f vc vq)
      (yes : Source ds (env := env) ctx p σ scope a g ac aq .step)
      (no : Source ds (env := env) ctx p σ scope b h bc bq .step) :
      Source ds (env := env) ctx p σ scope (StructuralStep.Conditional.source v (Branch.nativeBooleanDecision v) a b)
        (fun i x y ls s => (f i x y s ls).bind (fun v => if v != 0 then g i x y ls s else h i x y ls s))
        (.branch vc ac bc) (app ``HybridWord.Cmd.branch [vq,aq,bq]) .step
  | retainedCall {body : Lean.Expr} {bodyCore domain first : VExpr}
    {rest domains : List VExpr}
    (fn argument : Lean.Expr) (modeAllowed : mode ≠ .value)
    (binding : BindingValue scope ctx.length σ fn.getAppFn (.captured depth bindings arity body functions))
    (coherent : scope.Coherent ctx.length σ)
    (arguments : ArgumentBindings (env := env) ctx p
      ((Lean.Expr.app fn argument).getAppArgs.toList.map σ.apply) []
      finalCtx finalInputs finalArgs sourceWrap nativeWrap codeWrap quoteWrap)
    (next : Source ds (env := env) finalCtx finalInputs
      (closureSubstitution depth finalCtx.length bindings finalArgs)
      (functions.parameters finalArgs.length) body native code quotation mode)
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
    : Source ds (env := env) ctx p σ scope (.app fn argument)
        (nativeWrap native) (codeWrap code) (quoteWrap quotation) mode
  | functionLet {sourceBody functionValue domain codomain : VExpr}
      (binder : Lean.Name) (ty value next : Lean.Expr) (flag : Bool)
      (binding : BindingValue scope ctx.length σ value closure)
      (tail : Source ds (env := env) ctx p (letSubstitution σ value) (.push (some closure) scope) next native code quotation)
      (typeRep : Represents (σ.apply ty) (.forallE domain codomain))
      (typeTyped : CastTyping env 0 (SourceCasts env) ctx (.forallE domain codomain) (.sort u))
      (bodyTyped : CastTyping env 0 (SourceCasts env) ((.forallE domain codomain)::ctx) sourceBody (optionType stateType))
      (valueTyped : CastTyping env 0 (SourceCasts env) ctx functionValue (.forallE domain codomain))
      (reducedRep : Represents ((letSubstitution σ value).apply next) (sourceBody.inst functionValue))
      (sourceRep : Represents (σ.apply (.letE binder ty value next flag))
        (.app (.lam (.forallE domain codomain) sourceBody) functionValue)) :
      Source ds (env := env) ctx p σ scope (.letE binder ty value next flag) native code quotation
  | stepFunctionLet {sourceBody functionValue domain codomain : VExpr}
      (binder : Lean.Name) (ty value next : Lean.Expr) (flag : Bool)
      (binding : BindingValue scope ctx.length σ value closure)
      (tail : Source ds (env := env) ctx p (letSubstitution σ value) (.push (some closure) scope) next native code quotation .step)
      (typeRep : Represents (σ.apply ty) (.forallE domain codomain))
      (typeTyped : CastTyping env 0 (SourceCasts env) ctx (.forallE domain codomain) (.sort u))
      (bodyTyped : CastTyping env 0 (SourceCasts env) ((.forallE domain codomain)::ctx) sourceBody (optionType Step.stepState))
      (valueTyped : CastTyping env 0 (SourceCasts env) ctx functionValue (.forallE domain codomain))
      (reducedRep : Represents ((letSubstitution σ value).apply next) (sourceBody.inst functionValue))
      (sourceRep : Represents (σ.apply (.letE binder ty value next flag))
        (.app (.lam (.forallE domain codomain) sourceBody) functionValue)) :
      Source ds (env := env) ctx p σ scope (.letE binder ty value next flag) native code quotation .step

/-- Derive the comparison operand's type and shape from its source syntax. -/
theorem Source.branchInferred (library : ScalarSyntax.Library env) (decisions : Branch.BooleanLibrary env)
    (inputs : InputsTyped env ctx p) (typing : LexicalScalarCode.ScopeTyped env ctx p)
    (annotation : WordBinder.Annotation)
    (value : FixedScalarCompleteness.Scoped env ctx p (σ.apply v) f vc vq)
    (yes : Source ds (env := env) ctx p σ scope a g ac aq)
    (no : Source ds (env := env) ctx p σ scope b h bc bq) :
    Source ds (env := env) ctx p σ scope
      (AnnotatedBranch.source annotation v (AnnotatedCondition.nativeDecision annotation v) a b)
      (fun i x y ls s => (f i x y s ls).bind (fun v => if v != 0 then g i x y ls s else h i x y ls s))
      (.branch vc ac bc) (app ``HybridWord.Cmd.branch [vq,aq,bq]) := by
  obtain ⟨core,operand,rep,typed,form⟩ := value.evidence library decisions inputs typing
  exact .annotatedBooleanBranch annotation operand value rep typed form yes no

/-- Derive the comparison operand's type and shape from its source syntax. -/
theorem Source.stepBranchInferred (library : ScalarSyntax.Library env) (decisions : Branch.BooleanLibrary env)
    (inputs : InputsTyped env ctx p) (typing : LexicalScalarCode.ScopeTyped env ctx p)
    (annotation : WordBinder.Annotation)
    (value : FixedScalarCompleteness.Scoped env ctx p (σ.apply v) f vc vq)
    (yes : Source ds (env := env) ctx p σ scope a g ac aq .step)
    (no : Source ds (env := env) ctx p σ scope b h bc bq .step) :
    Source ds (env := env) ctx p σ scope
      (AnnotatedBranch.Loop.source annotation v (AnnotatedCondition.nativeDecision annotation v) a b)
      (fun i x y ls s => (f i x y s ls).bind (fun v => if v != 0 then g i x y ls s else h i x y ls s))
      (.branch vc ac bc) (app ``HybridWord.Cmd.branch [vq,aq,bq]) .step := by
  obtain ⟨core,operand,rep,typed,form⟩ := value.evidence library decisions inputs typing
  exact .annotatedStepBooleanBranch annotation operand value rep typed form yes no

/-- The source induction constructs the two facts needed to build Entry
at once. Public projection lemmas below keep their original interfaces. -/
theorem Source.facts (source : Source ds (env := env) ctx p σ scope raw native code quotation mode) :
    FixedMemory.declared ds code = true ∧
      ∀ i x y s ls, code.eval i x y s ls = native i x y ls s := by
  induction source with
  | plain body | base _ body => exact body.facts
  | valueCurrent current => exact ⟨rfl,by intros; rfl⟩
  | valueAssign register rn current value =>
    exact ⟨value.declared,by intros; simp [HybridWord.Cmd.eval,value.computation]⟩
  | yield value ih => exact ih
  | unitBody next binder info ih | unitLoop next binder info ih => exact ih
  | stateAlias current next binder flag ih | stepAlias current next binder flag ih => exact ih
  | stateLet value next notAlias binder flag ia ib
  | stepStateLet value next notAlias binder flag ia ib
  | stepSequence first next binder info ia ib
  | sequence first next binder info ia ib =>
    exact ⟨by simp [FixedMemory.declared,ia.1,ib.1],by intros; simp [HybridWord.Cmd.eval,ia.2,ib.2]⟩
  | forStatic start stop stride current body kn tn ki ti ih =>
    refine ⟨by simpa [FixedMemory.declared] using ih.1,?_⟩
    intro i x y s ls
    exact WordLoopFacts.forStatic _ _ _ _ i x y s ls _ (fun k t => congrArg WordLoopFacts.lift (ih.2 i x y t (k::ls)))
  | forRange kind count current body kn tn ki ti ih =>
    refine ⟨by simp [FixedMemory.declared,count.declared,ih.1],?_⟩
    intro i x y s ls
    cases kind with
    | fold => simp only [HybridWord.Cmd.eval,count.computation,FixedSequenceCompleteness.naturalRange,ih.2,bind,Option.bind]
    | forIn =>
      simp only [HybridWord.Cmd.eval,count.computation,FixedSequenceCompleteness.naturalRange]
      congr 1
      funext n
      rw [WordLoopFacts.forIn_lift _ _ _ _ (fun _ _ => rfl)]
      simp only [ih.2]
  | letValue annotation value next binder flag ih
  | stepLetValue annotation value next binder flag ih
  | bindValue annotation value next binder flag ih
  | stepBindValue annotation value next binder flag ih =>
    exact ⟨by simp [FixedMemory.declared,value.declared,ih.1],by intros; simp [HybridWord.Cmd.eval,value.computation,ih.2]⟩
  | branch value decision yes no ia ib
  | booleanBranch value yes no ia ib
  | stepBooleanBranch value yes no ia ib
  | annotatedBooleanBranch annotation operand value represented typed form yes no ia ib
  | annotatedStepBooleanBranch annotation operand value represented typed form yes no ia ib =>
    exact ⟨by simp [FixedMemory.declared,value.declared,ia.1,ib.1],
      by intros; simp only [HybridWord.Cmd.eval,value.computation,ia.2,ib.2,bind,Option.bind]⟩
  | retainedCall fn argument allowed binding coherent arguments next arity dt bt ft ats tc pt rr sr ih =>
    exact arguments.facts ih.1 ih.2
  | functionLet binder ty value next flag binding tail tr tt bt vt rr sr ih
  | stepFunctionLet binder ty value next flag binding tail tr tt bt vt rr sr ih => exact ih

theorem Source.declared (source : Source ds (env := env) ctx p σ scope raw native code quotation mode) :
    FixedMemory.declared ds code = true := source.facts.1

theorem Source.computation (source : Source ds (env := env) ctx p σ scope raw native code quotation mode) :
    ∀ i x y s ls, code.eval i x y s ls = native i x y ls s := source.facts.2

private theorem scope_app {σ : Substitution} {f a : Lean.Expr}
    (h : LeanScalar.wellScoped bound (σ.apply (.app f a)) = true) :
    LeanScalar.wellScoped bound (σ.apply f) = true ∧ LeanScalar.wellScoped bound (σ.apply a) = true := by
  cases σ <;> exact Bool.and_eq_true_iff.mp h

private theorem scope_lambda {σ : Substitution} {body ty : Lean.Expr}
    (h : LeanScalar.wellScoped bound (σ.apply (.lam binder ty body info)) = true) :
    LeanScalar.wellScoped (bound+1) ((under σ).apply body) = true := by
  cases σ <;> exact (Bool.and_eq_true_iff.mp h).2

private theorem scope_let {σ : Substitution} {body ty value : Lean.Expr}
    (h : LeanScalar.wellScoped bound (σ.apply (.letE binder ty value body flag)) = true) :
    LeanScalar.wellScoped bound (σ.apply value) = true ∧
      LeanScalar.wellScoped (bound+1) ((under σ).apply body) = true := by
  cases σ <;> exact ⟨(Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).2,(Bool.and_eq_true_iff.mp h).2⟩

/-- Ordinary helper lets and applications preserve the same source-scope
invariant as loops and scalar bindings. The exact representation facts used
by type checking also discharge scope after closure substitution. -/
theorem Source.independent (source : Source ds (env := env) ctx p σ scope raw native code quotation mode)
    (external : LexicalScalarCode.ExternalAt bound p)
    (scope_ok : LeanScalar.wellScoped bound (σ.apply raw) = true) :
    ∀ i x y ls s, native i x y ls s = native 0 0 0 ls s := by
  induction source generalizing bound with
  | plain body | base head body => exact body.independent external scope_ok
  | valueCurrent => intros; rfl
  | valueAssign register rn current value =>
    have hv := value.independent external (scope_app scope_ok).2
    intros; simp only [hv]
  | yield value ih => exact ih external (scope_app (scope_app scope_ok).2).2
  | letValue annotation value next binder flag ih
  | stepLetValue annotation value next binder flag ih =>
    have parts := scope_let scope_ok
    have hv := value.independent external parts.1
    have hn := ih (show LexicalScalarCode.ExternalAt (bound+1) _ from external.lift) parts.2
    intros; simp only [hv,hn]
  | bindValue annotation value next binder info ih
  | stepBindValue annotation value next binder info ih =>
    have parts := scope_app scope_ok
    have hv := value.independent external (scope_app parts.1).2
    have hn := ih (show LexicalScalarCode.ExternalAt (bound+1) _ from external.lift) (scope_lambda parts.2)
    intros; simp only [hv,hn]
  | stateAlias current next binder flag ih | stepAlias current next binder flag ih =>
    exact ih (show LexicalScalarCode.ExternalAt (bound+1) _ from external.lift) (scope_let scope_ok).2
  | stateLet value next notAlias binder flag iv ih
  | stepStateLet value next notAlias binder flag iv ih =>
    have parts := scope_let scope_ok
    have hv := iv external parts.1
    have hn := ih (show LexicalScalarCode.ExternalAt (bound+1) _ from external.lift) parts.2
    intro i x y ls s
    simp only [hv]
    congr 1
    exact funext (hn i x y ls)
  | sequence first next binder info iv ih | stepSequence first next binder info iv ih =>
    have parts := scope_app scope_ok
    have hv := iv external (scope_app parts.1).2
    have hn := ih (show LexicalScalarCode.ExternalAt (bound+1) _ from external.lift) (scope_lambda parts.2)
    intro i x y ls s
    simp only [hv]
    congr 1
    exact funext (hn i x y ls)
  | unitBody next binder info ih | unitLoop next binder info ih =>
    exact ih external.lift (scope_lambda (scope_app scope_ok).2)
  | forStatic start stop stride current body kn tn ki ti ih =>
    have hn := ih (show LexicalScalarCode.ExternalAt (bound+1+1) _ from external.lift.lift)
      (scope_lambda (scope_lambda (scope_app scope_ok).2))
    intros; simp only [hn]
  | forRange kind count current body kn tn ki ti ih =>
    have hn := ih (bound := bound+1+1) (by cases kind <;> exact external.lift.lift) (by
      cases kind
      · exact scope_lambda (scope_lambda (scope_app scope_ok).2)
      · exact scope_lambda (scope_lambda (scope_app (scope_app (scope_app scope_ok).1).1).2))
    have hv := count.independent external (by
      cases kind
      · exact (scope_app (scope_app (scope_app (scope_app (scope_app scope_ok).1).1).2).2).2
      · exact (scope_app (scope_app (scope_app scope_ok).2).2).2)
    intros; simp only [hv,hn]
  | branch value decision yes no ia ib | booleanBranch value yes no ia ib
  | stepBooleanBranch value yes no ia ib
  | annotatedBooleanBranch annotation operand value represented typed form yes no ia ib
  | annotatedStepBooleanBranch annotation operand value represented typed form yes no ia ib =>
    have bs := scope_app scope_ok
    have as_ := scope_app bs.1
    have cs := (scope_app (scope_app as_.1).1).2
    have vs_ := (scope_app (scope_app (scope_app cs).1).2).1
    have hv := value.independent external (scope_app vs_).2
    have ha := ia external as_.2
    have hb := ib external bs.2
    intros; simp only [hv,ha,hb]
  | retainedCall fn argument allowed binding coherent arguments next arity dt bt ft ats tc pt rr sr ih =>
    obtain ⟨functionScope,actualScope⟩ := application_spine_scoped (.app fn argument) _ scope_ok
    obtain ⟨captureBound,value,domains,shape,count,headEq⟩ := binding.sourceAt coherent
    apply arguments.independent shape captureBound
      (by simp only [List.length_nil,Nat.zero_add,List.length_map,Array.length_toList]; omega)
      external (headEq ▸ functionScope) (by simp) actualScope
    intro bound
    exact ih
  | functionLet binder ty value next flag binding tail tr tt bt vt rr sr ih
  | stepFunctionLet binder ty value next flag binding tail tr tt bt vt rr sr ih =>
    exact ih external (FixedSequenceCompleteness.reduced_scoped (rest := []) sr rr scope_ok)

theorem Source.install (source : Source ds (env := before) ctx p σ scope raw native code quotation mode)
    (installed : SignatureExtension before after) : Source ds (env := after) ctx p σ scope raw native code quotation mode := by
  induction source with
  | plain body => exact .plain (body.install installed)
  | base head body => exact .base head (body.install installed)
  | valueCurrent current => exact .valueCurrent current
  | valueAssign register rn current value => exact .valueAssign register rn current (value.install installed)
  | yield value ih => exact .yield ih
  | unitBody next binder info ih => exact .unitBody ih binder info
  | unitLoop next binder info ih => exact .unitLoop ih binder info
  | stateAlias current next binder flag ih => exact .stateAlias current ih binder flag
  | stepAlias current next binder flag ih => exact .stepAlias current ih binder flag
  | stateLet value next notAlias binder flag ia ib => exact .stateLet ia ib notAlias binder flag
  | stepStateLet value next notAlias binder flag ia ib => exact .stepStateLet ia ib notAlias binder flag
  | stepSequence first next binder info ia ib => exact .stepSequence ia ib binder info
  | forStatic start stop stride current body kn tn ki ti ih => exact .forStatic start stop stride current ih kn tn ki ti
  | forRange kind count current body kn tn ki ti ih => exact .forRange kind (count.install installed) current ih kn tn ki ti
  | letValue annotation value next binder flag ih => exact .letValue annotation (value.install installed) ih binder flag
  | stepLetValue annotation value next binder flag ih => exact .stepLetValue annotation (value.install installed) ih binder flag
  | bindValue annotation value next binder info ih => exact .bindValue annotation (value.install installed) ih binder info
  | stepBindValue annotation value next binder info ih => exact .stepBindValue annotation (value.install installed) ih binder info
  | sequence first next binder info ia ib => exact .sequence ia ib binder info
  | branch value decision yes no ia ib => exact .branch (value.install installed) (decision.install installed) ia ib
  | booleanBranch value yes no ia ib => exact .booleanBranch (value.install installed) ia ib
  | stepBooleanBranch value yes no ia ib => exact .stepBooleanBranch (value.install installed) ia ib
  | annotatedBooleanBranch annotation operand value represented typed form yes no ia ib =>
    exact .annotatedBooleanBranch annotation operand (value.install installed) represented
      (typed.install installed (fun _ _ _ h => SourceCasts.install h installed)) (form.install installed) ia ib
  | annotatedStepBooleanBranch annotation operand value represented typed form yes no ia ib =>
    exact .annotatedStepBooleanBranch annotation operand (value.install installed) represented
      (typed.install installed (fun _ _ _ h => SourceCasts.install h installed)) (form.install installed) ia ib
  | retainedCall fn argument allowed binding coherent arguments next arity dt bt ft ats tc pt rr sr ih =>
    exact .retainedCall fn argument allowed binding coherent (arguments.install installed) ih arity
      (dt.install installed (fun _ _ _ h => SourceCasts.install h installed))
      (bt.install installed (fun _ _ _ h => SourceCasts.install h installed))
      (ft.install installed (fun _ _ _ h => SourceCasts.install h installed))
      (ats.imp (fun _ _ h => h.install installed (fun _ _ _ h => SourceCasts.install h installed))) tc
      (fun before after same nonempty => (pt before after same nonempty).install installed
        (fun _ _ _ h => SourceCasts.install h installed)) rr sr
  | functionLet binder ty value next flag binding tail tr tt bt vt rr sr ih =>
    exact .functionLet binder ty value next flag binding ih tr
      (tt.install installed (fun _ _ _ h => SourceCasts.install h installed))
      (bt.install installed (fun _ _ _ h => SourceCasts.install h installed))
      (vt.install installed (fun _ _ _ h => SourceCasts.install h installed)) rr sr
  | stepFunctionLet binder ty value next flag binding tail tr tt bt vt rr sr ih =>
    exact .stepFunctionLet binder ty value next flag binding ih tr
      (tt.install installed (fun _ _ _ h => SourceCasts.install h installed))
      (bt.install installed (fun _ _ _ h => SourceCasts.install h installed))
      (vt.install installed (fun _ _ _ h => SourceCasts.install h installed)) rr sr

def Outcome (setup : AliasSetup env) (exposure : Exposure env) (inputs : InputsTyped env ctx p)
    (σ : Substitution) (scope : Scope) (mode : StructuralBody.Mode) (raw quotation : Lean.Expr) : Prop :=
  match mode with
  | .body => ∃ piece, visit env setup.conversion exposure raw ctx p .body σ (scope.runtime env setup.conversion exposure) = some piece ∧
      ∃ typed : BodyCasts inputs piece (SourceCasts env) (For.Casts setup),
        ValueForm setup ctx typed.sourceCore.val (optionType stateType) ∧ piece.code = quotation
  | .value => ∃ piece, StructuralBody.visit env setup.conversion exposure raw ctx p .value σ (scope.runtime env setup.conversion exposure) = some piece ∧
      Nonempty (StructuralLoop.ValueCasts inputs piece (SourceCasts env) (For.Casts setup)) ∧ piece.code = quotation
  | .step => ∃ piece, StructuralBody.visit env setup.conversion exposure raw ctx p .step σ (scope.runtime env setup.conversion exposure) = some piece ∧
      ∃ typed : StructuralLoop.StepCasts inputs piece (SourceCasts env) (For.Casts setup),
        ValueForm setup ctx typed.sourceCore.val (optionType Step.stepState) ∧ piece.code = quotation

theorem Source.complete (source : Source ds (env := env) ctx p σ scope raw native code quotation mode)
    (setup : AliasSetup env) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (fresh : ScopedSyntax.Fresh setup) (exposure : Exposure env)
    (inputs : InputsTyped env ctx p) (locals : ScalarSyntax.Locals env ctx p) :
    Outcome setup exposure inputs σ scope mode raw quotation := by
  have coverage := For.Casts.covered setup library.scalars.toSignatures library.steps closed
    library.cons library.eq library.eval fresh.state fresh.eq fresh.lift
  induction source with
  | @plain mode ctx p raw native code quotation body =>
    cases mode <;> exact body.complete setup library closed fresh exposure inputs locals
  | base head body =>
    unfold Outcome
    rw [eq_of_heq (head.parser_congr (sameTerm_complete inputs.s.property inputs.s.property))]
    exact body.complete setup library closed fresh exposure inputs locals
  | valueCurrent current =>
    exact value_outcome_transport inputs current (valueCurrent_congr current inputs)
      ((FixedSequenceCompleteness.Source.valueCurrent (ds := ds)).complete setup library closed fresh exposure inputs locals)
  | @valueAssign ctx p f vc vq σ scope st v register rn current value =>
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
    exact value_outcome_transport inputs same (congruent.trans normalized)
      ((FixedSequenceCompleteness.Source.valueAssign (ds := ds) register rn value).complete
        setup library closed fresh exposure inputs locals)
  | yield value ih =>
    obtain ⟨a,ha,⟨ta⟩,qa⟩ := ih inputs locals
    obtain ⟨result,parsed,typed,form,q⟩ := FunctionSyntax.yield_complete_code setup library closed fresh exposure inputs ta ha
    exact ⟨result,parsed,typed,form,q.trans qa⟩
  | stateLet value next notAlias binder flag ihValue ihNext =>
    obtain ⟨a,ha,⟨ta⟩,aCode⟩ := ihValue inputs locals
    obtain ⟨b,hb,tb,fb,bCode⟩ := ihNext (inputs.nextState closed) (locals.nextState closed)
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
    refine ⟨piece,parsed,typed,?_,?_⟩
    · rw [same]; exact .beta tb.value
    · rw [code,aCode,bCode]
  | @stepStateLet ctx p σ scope v f vc vq b g bc bq value next notAlias binder flag ihValue ihNext =>
    obtain ⟨a,ha,⟨ta⟩,aCode⟩ := ihValue inputs locals
    obtain ⟨b,hb,tb,fb,bCode⟩ := ihNext (inputs.nextState closed) (locals.nextState closed)
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
    refine ⟨piece,parsed,typed,?_,?_⟩
    · rw [same]; exact .beta tb.value
    · rw [code,aCode,bCode]
  | stateAlias current next binder flag ih =>
    obtain ⟨b,hb,tb,fb,qb⟩ := ih (inputs.nextState closed) (locals.nextState closed)
    have underRuntime (scope : Scope) : (Scope.push none scope).runtime env setup.conversion exposure =
        underFunctions (scope.runtime env setup.conversion exposure) := by
      funext n; cases n <;> rfl
    rw [underRuntime] at hb
    obtain ⟨piece,success,typed,form,q⟩ := FunctionSyntax.stateAlias_complete_code setup library closed fresh exposure inputs tb fb current hb binder flag
    exact ⟨piece,success,typed,form,q.trans qb⟩
  | stepAlias current next binder flag ih =>
    obtain ⟨b,hb,tb,fb,qb⟩ := ih (inputs.nextState closed) (locals.nextState closed)
    have underRuntime (scope : Scope) : (Scope.push none scope).runtime env setup.conversion exposure =
        underFunctions (scope.runtime env setup.conversion exposure) := by
      funext n; cases n <;> rfl
    rw [underRuntime] at hb
    obtain ⟨piece,success,typed,form,q⟩ := FunctionSyntax.stepAlias_complete_code setup library closed fresh exposure inputs tb fb current hb binder flag
    exact ⟨piece,success,typed,form,q.trans qb⟩
  | stepSequence first next binder info ia ib =>
    obtain ⟨a,ha,ta,fa,qa⟩ := ia inputs locals
    obtain ⟨b,hb,tb,fb,qb⟩ := ib (inputs.nextState closed) (locals.nextState closed)
    have underRuntime (scope : Scope) : (Scope.push none scope).runtime env setup.conversion exposure =
        underFunctions (scope.runtime env setup.conversion exposure) := by
      funext n; cases n <;> rfl
    rw [underRuntime] at hb
    obtain ⟨result,parsed,typed,form,q⟩ := FunctionSyntax.stepSequence_complete_code setup library closed fresh exposure inputs ta tb fb ha hb binder info
    exact ⟨result,parsed,typed,form,by rw [q,qa,qb]⟩
  | forStatic start stop stride current body kn tn ki ti ih =>
    obtain ⟨startBound⟩ := start.typed (ctx := _) library.bounds library.scalars.toSignatures
    obtain ⟨stopBound⟩ := stop.typed (ctx := _) library.bounds library.scalars.toSignatures
    obtain ⟨strideBound⟩ := stride.typed (ctx := _) library.bounds library.scalars.toSignatures
    obtain ⟨b,hb,tb,fb,bCode⟩ := ih (For.nextInputs inputs closed library.scalars.word library.cons)
      ((locals.nextWord closed).nextState closed)
    have underRuntime (scope : Scope) : (Scope.push none scope).runtime env setup.conversion exposure =
        underFunctions (scope.runtime env setup.conversion exposure) := by
      funext n; cases n <;> rfl
    rw [underRuntime,underRuntime] at hb
    obtain ⟨target,_,_⟩ := StructuralLoop.next_typed inputs closed Arithmetic.SourceCasts.closed
      library.scalars.word library.returns.state library.cons tb
    obtain ⟨piece,parsed,⟨typed⟩,code⟩ := StructuralLoop.mapped_forStatic_complete_code inputs closed Arithmetic.SourceCasts.closed
      (fun _ _ _ h => For.Casts.base (.base (.source h))) startBound stopBound strideBound library.scalars.word library.returns.state library.cons tb
      (.continuation inputs target (b.represented.property.closed 0 b.closed) tb.value fb)
      library.forFact library.forConstructor library.range library.forHeader.header_typed
      coverage exposure kn tn ki ti current hb
    exact ⟨piece,parsed,typed,ScopedSyntax.head_form fresh typed.sourceCore.property (by rw [StructuralLoop.substitute_forStatic]; rfl) (by simp),by rw [code,bCode]⟩
  | unitBody next binder info ih =>
    obtain ⟨b,hb,tb,fb,bCode⟩ := ih (inputs.lift closed UnitStep.unitType) (locals.lift closed UnitStep.unitType)
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
      ScopedSyntax.head_form fresh typed.sourceCore.property (by rw [StructuralUnit.substitute_source]; rfl) (by simp),code.trans bCode⟩
  | unitLoop next binder info ih =>
    obtain ⟨b,hb,tb,fb,bCode⟩ := ih (inputs.lift closed UnitStep.unitType) (locals.lift closed UnitStep.unitType)
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
      ScopedSyntax.head_form fresh typed.sourceCore.property (by rw [StructuralUnit.substitute_source]; rfl) (by simp),code.trans bCode⟩
  | @forRange ctx p f nc nq σ scope original g bc bq n st kind count current body kn tn ki ti ih =>
    obtain ⟨c,hc,⟨tc⟩,cCode⟩ := count.complete setup library closed fresh exposure inputs locals
    let nextInputs := kind.nextInputs inputs closed library.scalars.toSignatures library.naturalLoops library.cons
    let nextLocals := kind.nextLocals locals closed library.scalars.toSignatures library.naturalLoops
    have child : ∃ b, StructuralBody.visit env setup.conversion exposure original (kind.context ctx) (kind.parameters p)
        kind.mode (under (under σ)) ((Scope.push none (Scope.push none scope)).runtime env setup.conversion exposure) = some b ∧
        ∃ typed : NaturalLoop.ChildCasts kind nextInputs b (Arithmetic.SourceCasts env) (For.Casts setup),
          Arithmetic.ValueForm setup (kind.context ctx) typed.sourceCore.val (optionType kind.result) ∧ b.code = bq := by
      cases kind with
      | forIn => exact ih nextInputs nextLocals
      | fold => exact ih nextInputs nextLocals
    obtain ⟨b,hb,tb,fb,bCode⟩ := child
    have underRuntime (scope : Scope) : (Scope.push none scope).runtime env setup.conversion exposure =
        underFunctions (scope.runtime env setup.conversion exposure) := by
      funext n; cases n <;> rfl
    rw [underRuntime,underRuntime] at hb
    have beta := NaturalLoop.continuation_cast setup inputs kind closed library.scalars.toSignatures
      library.naturalLoops library.steps library.cons library.eval fresh.nat fresh.state tb fb
    obtain ⟨piece,parsed,⟨typed⟩,code⟩ := NaturalLoop.mapped_forRange_complete_code inputs kind closed (fun _ _ _ h => For.Casts.base (.base (.source h)))
      library.scalars.toSignatures library.naturalLoops library.forHeader library.reads library.steps.state
      library.cons tc tb beta coverage exposure kn tn ki ti current hc hb
    refine ⟨piece,parsed,typed,?_,?_⟩
    · cases kind <;> exact ScopedSyntax.head_form fresh typed.sourceCore.property
        (by rw [NaturalLoop.Kind.substitute_source]; rfl) (by simp)
    · rw [code,cCode,bCode]
  | letValue annotation value next binder flag ih =>
    obtain ⟨a,ha,⟨ta⟩,qa⟩ := value.complete setup library closed fresh exposure inputs locals
    obtain ⟨b,hb,tb,fb,qb⟩ := ih
      (annotation.nextInputs inputs closed library.scalars.toSignatures library.cons)
      (annotation.nextLocals locals closed)
    have underRuntime (scope : Scope) : (Scope.push none scope).runtime env setup.conversion exposure =
        underFunctions (scope.runtime env setup.conversion exposure) := by
      funext n; cases n <;> rfl
    rw [underRuntime] at hb
    obtain ⟨result,parsed,typed,form,q⟩ := FunctionSyntax.letValue_complete_code annotation setup library closed fresh exposure inputs ta tb fb ha hb binder flag
    exact ⟨result,parsed,typed,form,by rw [q,qa,qb]⟩
  | bindValue annotation value next binder info ih =>
    obtain ⟨a,ha,⟨ta⟩,qa⟩ := value.complete setup library closed fresh exposure inputs locals
    obtain ⟨b,hb,tb,fb,qb⟩ := ih
      (annotation.nextInputs inputs closed library.scalars.toSignatures library.cons)
      (annotation.nextLocals locals closed)
    have underRuntime (scope : Scope) : (Scope.push none scope).runtime env setup.conversion exposure =
        underFunctions (scope.runtime env setup.conversion exposure) := by
      funext n; cases n <;> rfl
    rw [underRuntime] at hb
    cases annotation with
    | word =>
      obtain ⟨piece,parsed,typed,form,q⟩ := FunctionSyntax.readWord_complete_code setup library closed fresh exposure inputs ta tb fb ha hb binder info
      exact ⟨piece,parsed,typed,form,by rw [q,qa,qb]⟩
    | bitvec =>
      obtain ⟨piece,parsed,typed,form,q⟩ := WordBinder.mapped_bind_bits_complete_code setup library.scalars.toSignatures
        library.bind inputs closed library.cons library.returns.state library.eq library.eval
        library.bindValueFact library.letValueConstructor fresh.state (fresh.value _ (by simp))
        coverage exposure ta (value.valueForm fresh ta.sourceCore.property) tb fb ha hb binder info
      exact ⟨piece,parsed,typed,form,by rw [q,qa,qb]⟩
  | stepBindValue annotation value next binder info ih =>
    obtain ⟨a,ha,⟨ta⟩,qa⟩ := value.complete setup library closed fresh exposure inputs locals
    obtain ⟨b,hb,tb,fb,qb⟩ := ih
      (annotation.nextInputs inputs closed library.scalars.toSignatures library.cons)
      (annotation.nextLocals locals closed)
    have underRuntime (scope : Scope) : (Scope.push none scope).runtime env setup.conversion exposure =
        underFunctions (scope.runtime env setup.conversion exposure) := by
      funext n; cases n <;> rfl
    rw [underRuntime] at hb
    cases annotation with
    | word =>
      obtain ⟨piece,parsed,typed,form,q⟩ := FunctionSyntax.stepReadWord_complete_code setup library closed fresh exposure inputs ta tb fb ha hb binder info
      exact ⟨piece,parsed,typed,form,by rw [q,qa,qb]⟩
    | bitvec =>
      obtain ⟨piece,parsed,typed,form,q⟩ := WordBinder.mapped_step_bind_bits_complete_code setup library.scalars.toSignatures
        library.bind inputs closed library.cons library.steps library.eq library.eval
        library.stepBindValue library.letValueConstructor (fresh.readAux _ (by simp)) (fresh.value _ (by simp))
        coverage exposure ta (value.valueForm fresh ta.sourceCore.property) tb fb ha hb binder info
      exact ⟨piece,parsed,typed,form,by rw [q,qa,qb]⟩
  | stepLetValue annotation value next binder flag ih =>
    obtain ⟨a,ha,⟨ta⟩,qa⟩ := value.complete setup library closed fresh exposure inputs locals
    obtain ⟨b,hb,tb,fb,qb⟩ := ih
      (annotation.nextInputs inputs closed library.scalars.toSignatures library.cons)
      (annotation.nextLocals locals closed)
    have underRuntime (scope : Scope) : (Scope.push none scope).runtime env setup.conversion exposure =
        underFunctions (scope.runtime env setup.conversion exposure) := by
      funext n; cases n <;> rfl
    rw [underRuntime] at hb
    obtain ⟨result,parsed,typed,form,q⟩ := FunctionSyntax.stepLetValue_complete_code annotation setup library closed fresh exposure inputs ta tb fb ha hb binder flag
    exact ⟨result,parsed,typed,form,by rw [q,qa,qb]⟩
  | sequence first next binder info ia ib =>
    obtain ⟨a,ha,ta,fa,qa⟩ := ia inputs locals
    obtain ⟨b,hb,tb,fb,qb⟩ := ib (inputs.nextState closed) (locals.nextState closed)
    have underRuntime (scope : Scope) : (Scope.push none scope).runtime env setup.conversion exposure =
        underFunctions (scope.runtime env setup.conversion exposure) := by
      funext n; cases n <;> rfl
    rw [underRuntime] at hb
    obtain ⟨result,parsed,typed,form,q⟩ := FunctionSyntax.sequence_complete_code setup library closed fresh exposure inputs ta tb fb ha hb binder info
    exact ⟨result,parsed,typed,form,by rw [q,qa,qb]⟩
  | branch value decision yes no ia ib =>
    obtain ⟨e,he,⟨te⟩,qe⟩ := value.complete setup library closed fresh exposure inputs locals
    obtain ⟨a,ha,ta,fa,qa⟩ := ia inputs locals
    obtain ⟨b,hb,tb,fb,qb⟩ := ib inputs locals
    obtain ⟨result,parsed,typed,form,q⟩ := FunctionSyntax.branch_complete_code setup library closed fresh exposure inputs te ta tb decision he ha hb
    exact ⟨result,parsed,typed,form,by rw [q,qe,qa,qb]⟩
  | @booleanBranch ctx p f vc vq σ scope a g ac aq b h bc bq v value yes no ia ib =>
    obtain ⟨e,he,⟨te⟩,qe⟩ := value.complete setup library closed fresh exposure inputs locals
    obtain ⟨a,ha,ta,fa,qa⟩ := ia inputs locals
    obtain ⟨b,hb,tb,fb,qb⟩ := ib inputs locals
    obtain ⟨pt,dt⟩ := library.decisions.condition_typed library.scalars.toSignatures te.value
    have represented : Represents (σ.apply (Branch.nativeBooleanDecision v))
        (Branch.booleanDecision te.sourceCore.val) := by
      have substituted : σ.apply (Branch.nativeBooleanDecision v) = Branch.nativeBooleanDecision (σ.apply v) := by
        cases σ <;> rfl
      rw [substituted]
      exact Branch.booleanDecision_represents te.sourceCore.property
    obtain ⟨result,parsed,typed,form,q⟩ := FunctionSyntax.branch_typed_complete_code setup library closed fresh exposure inputs te ta tb represented pt dt he ha hb
    exact ⟨result,parsed,typed,form,by rw [q,qe,qa,qb]⟩
  | @annotatedBooleanBranch ctx p f vc vq σ scope a g ac aq b h bc bq v valueCore annotation operand value represented valueTyped valueShape yes no ia ib =>
    obtain ⟨e,he,⟨te⟩,qe⟩ := value.complete setup library closed fresh exposure inputs locals
    obtain ⟨a,ha,ta,fa,qa⟩ := ia inputs locals
    obtain ⟨b,hb,tb,fb,qb⟩ := ib inputs locals
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
    exact ⟨result,parsed,typed,form,by rw [q,qe,qa,qb]⟩
  | @annotatedStepBooleanBranch ctx p f vc vq σ scope a g ac aq b h bc bq v valueCore annotation operand value represented valueTyped valueShape yes no ia ib =>
    obtain ⟨e,he,⟨te⟩,qe⟩ := value.complete setup library closed fresh exposure inputs locals
    obtain ⟨a,ha,ta,fa,qa⟩ := ia inputs locals
    obtain ⟨b,hb,tb,fb,qb⟩ := ib inputs locals
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
    exact ⟨result,parsed,typed,form,by rw [q,qe,qa,qb]⟩
  | @stepBooleanBranch ctx p f vc vq σ scope a g ac aq b h bc bq v value yes no ia ib =>
    obtain ⟨e,he,⟨te⟩,qe⟩ := value.complete setup library closed fresh exposure inputs locals
    obtain ⟨a,ha,ta,fa,qa⟩ := ia inputs locals
    obtain ⟨b,hb,tb,fb,qb⟩ := ib inputs locals
    obtain ⟨pt,dt⟩ := library.decisions.condition_typed library.scalars.toSignatures te.value
    have represented : Represents (σ.apply (Branch.nativeBooleanDecision v))
        (Branch.booleanDecision te.sourceCore.val) := by
      have substituted : σ.apply (Branch.nativeBooleanDecision v) = Branch.nativeBooleanDecision (σ.apply v) := by
        cases σ <;> rfl
      rw [substituted]
      exact Branch.booleanDecision_represents te.sourceCore.property
    obtain ⟨result,parsed,typed,form,q⟩ := FunctionSyntax.stepBranch_complete_code setup library closed fresh exposure inputs te ta tb represented pt dt he ha hb
    exact ⟨result,parsed,typed,form,by rw [q,qe,qa,qb]⟩
  | @retainedCall mode scope σ depth bindings arity functions ctx p finalCtx finalInputs finalArgs sourceWrap nativeWrap codeWrap quoteWrap native code quotation u body bodyCore domain first rest domains fn argument allowed binding coherent arguments next arity dt bt ft ats tc pt rr sr ih =>
    obtain ⟨piece,success,typed,codeSame⟩ := binding.retained_call_from_body fn argument allowed coherent
      arguments arity dt bt ft ats tc pt rr sr setup library closed fresh exposure inputs locals (by
        intro finalTyped finalLocals
        have child := ih finalTyped finalLocals
        cases mode with
        | value => exact False.elim (allowed rfl)
        | body | step =>
          obtain ⟨piece,parsed,typed,form,codeSame⟩ := child
          exact ⟨piece,parsed,⟨typed,form⟩,codeSame⟩)
    cases mode with
    | value => exact False.elim (allowed rfl)
    | body | step =>
      obtain ⟨typed,form⟩ := typed
      exact ⟨piece,success,typed,form,codeSame⟩
  | @functionLet scope σ closure ctx p native code quotation u sourceBody functionValue domain codomain binder ty value next flag
      binding tail typeRep typeTyped bodyTyped valueTyped reducedRep sourceRep ih =>
    obtain ⟨piece,parsed,typed,form,q⟩ := ih inputs locals
    obtain ⟨result,success,codeSame,resultTyped,resultForm⟩ := function_let_step_complete setup
      library.steps.state library.steps.option library.eq library.eval fresh.state coverage exposure binder ty value next flag
      inputs typeRep typeTyped bodyTyped valueTyped reducedRep sourceRep typed form (fs := scope.runtime env setup.conversion exposure) (by
        dsimp only
        rw [binding.construct]
        exact parsed)
    exact ⟨result,success,resultTyped,resultForm,codeSame.trans q⟩
  | @stepFunctionLet scope σ closure ctx p native code quotation u sourceBody functionValue domain codomain binder ty value next flag
      binding tail typeRep typeTyped bodyTyped valueTyped reducedRep sourceRep ih =>
    obtain ⟨piece,parsed,typed,form,q⟩ := ih inputs locals
    obtain ⟨result,success,codeSame,resultTyped,resultForm⟩ := step_functionLet_complete setup
      library.steps library.eq library.eval fresh.state coverage exposure binder ty value next flag
      inputs typeRep typeTyped bodyTyped valueTyped reducedRep sourceRep typed form (fs := scope.runtime env setup.conversion exposure) (by
        dsimp only
        rw [binding.construct]
        exact parsed)
    exact ⟨result,success,resultTyped,resultForm,codeSame.trans q⟩

/-- Connect the retained-argument induction to the whole Source induction.
The body may contain arbitrary combinations of State/read bindings, branches,
loops and the other established constructors. No endpoint parsing success is
assumed here; it is derived by `Source.complete`. The final transport back to
the original call expression is supplied by `Source.retainedCall`. -/
theorem Source.completeArguments
    (arguments : ArgumentBindings (env := env) ctx p actuals saved
      finalCtx finalInputs finalArgs sourceWrap nativeWrap codeWrap quoteWrap)
    (source : Source ds (env := env) finalCtx finalInputs
      (closureSubstitution depth finalCtx.length bindings finalArgs)
      (functions.parameters finalArgs.length) raw native code quotation mode)
    (sourceArity : saved.length + actuals.length = arity) (modeAllowed : mode ≠ .value)
    (setup : AliasSetup env) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (fresh : ScopedSyntax.Fresh setup)
    (exposure : Exposure env) (inputs : InputsTyped env ctx p) (locals : ScalarSyntax.Locals env ctx p) :
    ∃ piece, retainArguments env setup.conversion exposure
        ((Closure.captured depth bindings arity raw functions).runtime env setup.conversion exposure)
        ctx p mode actuals saved =
          some ⟨sourceWrap ((closureSubstitution depth finalCtx.length bindings finalArgs).apply raw),piece⟩ ∧
      RetainedCasts setup inputs mode _ piece ∧ piece.code = quoteWrap quotation ∧
      FixedMemory.declared ds (codeWrap code) = true ∧
      ∀ i x y s ls, (codeWrap code).eval i x y s ls = nativeWrap native i x y ls s := by
  have arityMatches := arguments.argument_count.trans sourceArity
  obtain ⟨piece,parsed,typed,codeSame⟩ := arguments.complete setup library closed fresh exposure inputs locals
    ((Closure.captured depth bindings arity raw functions).runtime env setup.conversion exposure) mode (by
      intro finalTyped finalLocals
      have result := source.complete setup library closed fresh exposure finalTyped finalLocals
      cases mode with
      | value => exact False.elim (modeAllowed rfl)
      | body | step =>
        obtain ⟨child,success,typed,form,codeSame⟩ := result
        refine ⟨child,?_,⟨typed,form⟩,codeSame⟩
        simp only [Scope.runtime_parameters,arityMatches] at success
        simp only [Closure.runtime,arityMatches,bne_self_eq_false,Bool.false_eq_true,ite_false,
          success,bind,Option.bind,pure,Option.pure_def])
  exact ⟨piece,parsed,typed,codeSame,arguments.facts source.declared source.computation⟩

/-- Obtain source typing from the existing simultaneous success induction.
Clients do not supply a successful parse or manufacture its certificate. -/
theorem Source.bodyTyping (source : Source ds (env := env) ctx p σ scope raw native code quotation)
    (setup : AliasSetup env) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (fresh : ScopedSyntax.Fresh setup) (exposure : Exposure env)
    (inputs : InputsTyped env ctx p) (locals : ScalarSyntax.Locals env ctx p) :
    ∃ core, Represents (σ.apply raw) core ∧
      CastTyping env 0 (SourceCasts env) ctx core (optionType stateType) := by
  obtain ⟨piece,success,typed,form,exactCode⟩ := source.complete setup library closed fresh exposure inputs locals
  exact ⟨typed.sourceCore.val,typed.sourceCore.property,typed.value⟩

theorem Source.stepBodyTyping (source : Source ds (env := env) ctx p σ scope raw native code quotation .step)
    (setup : AliasSetup env) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (fresh : ScopedSyntax.Fresh setup) (exposure : Exposure env)
    (inputs : InputsTyped env ctx p) (locals : ScalarSyntax.Locals env ctx p) :
    ∃ core, Represents (σ.apply raw) core ∧
      CastTyping env 0 (SourceCasts env) ctx core (optionType Step.stepState) := by
  obtain ⟨piece,success,typed,form,exactCode⟩ := source.complete setup library closed fresh exposure inputs locals
  exact ⟨typed.sourceCore.val,typed.sourceCore.property,typed.value⟩

/-- Build the typed retained prefix from the existing whole-body Source
induction, in both ordinary and loop-continuation modes. Endpoint inputs,
local-variable invariants and body typing are all derived here; no endpoint
parse or separately typed retained/intermediate body is assumed. -/
theorem Source.retainedPrefix {functions : Scope}
    (arguments : ArgumentBindings (env := env) ctx p actuals saved
      finalCtx finalInputs finalArgs sourceWrap nativeWrap codeWrap quoteWrap)
    (source : Source ds (env := env) finalCtx finalInputs
      (closureSubstitution depth finalCtx.length bindings finalArgs)
      (functions.parameters finalArgs.length) raw native code quotation mode)
    (bound : depth ≤ ctx.length) (modeAllowed : mode ≠ .value)
    (setup : AliasSetup env) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (fresh : ScopedSyntax.Fresh setup)
    (exposure : Exposure env) (inputs : InputsTyped env ctx p) (locals : ScalarSyntax.Locals env ctx p) :
    ∃ retained original,
      Represents (sourceWrap ((closureSubstitution depth finalCtx.length bindings finalArgs).apply raw)) retained ∧
      Represents ((closureSubstitution depth ctx.length bindings (saved ++ actuals)).apply raw) original ∧
      RetainedConversion.Prefix env 0 (SourceCasts env)
        (optionType (if mode == .step then Step.stepState else stateType))
        ctx retained original (finalCtx.length - ctx.length) := by
  obtain ⟨⟨finalTyped⟩,⟨finalLocals⟩⟩ := arguments.endpointInputs library closed inputs locals
  cases mode with
  | value => exact False.elim (modeAllowed rfl)
  | body =>
    obtain ⟨core,represented,typed⟩ := source.bodyTyping setup library closed fresh exposure finalTyped finalLocals
    exact arguments.prefix library.scalars.toSignatures bound bindings raw represented typed
  | step =>
    obtain ⟨core,represented,typed⟩ := source.stepBodyTyping setup library closed fresh exposure finalTyped finalLocals
    exact arguments.prefix library.scalars.toSignatures bound bindings raw represented typed

/-- A captured call compiles through the retained runtime from source
conditions and the whole-body induction. This theorem assumes neither a
successful parser nor a retarget/reduction check. It also preserves the
certificate-typing invariant needed by enclosing source constructors. -/
theorem Source.completeRetainedCall {body : Lean.Expr} {bodyCore domain first : VExpr}
    {rest domains : List VExpr}
    (fn argument : Lean.Expr) (modeAllowed : mode ≠ .value)
    (binding : BindingValue scope ctx.length σ fn.getAppFn (.captured depth bindings arity body functions))
    (coherent : scope.Coherent ctx.length σ)
    (arguments : ArgumentBindings (env := env) ctx p
      ((Lean.Expr.app fn argument).getAppArgs.toList.map σ.apply) []
      finalCtx finalInputs finalArgs sourceWrap nativeWrap codeWrap quoteWrap)
    (source : Source ds (env := env) finalCtx finalInputs
      (closureSubstitution depth finalCtx.length bindings finalArgs)
      (functions.parameters finalArgs.length) body native code quotation mode)
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
    (setup : AliasSetup env) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (fresh : ScopedSyntax.Fresh setup)
    (exposure : Exposure env) (inputs : InputsTyped env ctx p) (locals : ScalarSyntax.Locals env ctx p) :
    ∃ piece, visit env setup.conversion exposure (.app fn argument) ctx p mode σ
        (scope.runtime env setup.conversion exposure) = some piece ∧
      RetainedCasts setup inputs mode (σ.apply (.app fn argument)) piece ∧
      piece.code = quoteWrap quotation ∧ FixedMemory.declared ds (codeWrap code) = true ∧
      ∀ i x y s ls, (codeWrap code).eval i x y s ls = nativeWrap native i x y ls s := by
  obtain ⟨piece,parsed,typed,codeSame⟩ := binding.retained_call_from_body fn argument modeAllowed coherent
    arguments arityMatches domainTyped bodyTyped firstTyped argumentTypes typesClosed prefixTypes
    reducedRep sourceRep setup library closed fresh exposure inputs locals (by
      intro finalTyped finalLocals
      have complete := source.complete setup library closed fresh exposure finalTyped finalLocals
      cases mode with
      | value => exact False.elim (modeAllowed rfl)
      | body | step =>
        obtain ⟨piece,success,typed,form,codeSame⟩ := complete
        exact ⟨piece,success,⟨typed,form⟩,codeSame⟩)
  exact ⟨piece,parsed,typed,codeSame,arguments.facts source.declared source.computation⟩

/-- Existing function-let rules with their enclosing representation premises
derived from source subterms, rather than supplied twice by the caller. -/
theorem Source.functionLetInferred {sourceBody functionValue domain codomain : VExpr}
    (binder : Lean.Name) (ty value next : Lean.Expr) (flag : Bool)
    (binding : BindingValue scope ctx.length σ value closure)
    (tail : Source ds (env := env) ctx p (letSubstitution σ value) (.push (some closure) scope) next native code quotation)
    (typeRep : Represents (σ.apply ty) (.forallE domain codomain))
    (valueRep : Represents (σ.apply value) functionValue)
    (bodyRep : Represents ((under σ).apply next) sourceBody)
    (typeTyped : CastTyping env 0 (SourceCasts env) ctx (.forallE domain codomain) (.sort u))
    (bodyTyped : CastTyping env 0 (SourceCasts env) ((.forallE domain codomain)::ctx) sourceBody (optionType stateType))
    (valueTyped : CastTyping env 0 (SourceCasts env) ctx functionValue (.forallE domain codomain)) :
    Source ds (env := env) ctx p σ scope (.letE binder ty value next flag) native code quotation := by
  obtain ⟨reduced,source⟩ := let_representations typeRep valueRep bodyRep binder flag
  exact .functionLet binder ty value next flag binding tail typeRep typeTyped bodyTyped valueTyped reduced source

theorem Source.stepFunctionLetInferred {sourceBody functionValue domain codomain : VExpr}
    (binder : Lean.Name) (ty value next : Lean.Expr) (flag : Bool)
    (binding : BindingValue scope ctx.length σ value closure)
    (tail : Source ds (env := env) ctx p (letSubstitution σ value) (.push (some closure) scope) next native code quotation .step)
    (typeRep : Represents (σ.apply ty) (.forallE domain codomain))
    (valueRep : Represents (σ.apply value) functionValue)
    (bodyRep : Represents ((under σ).apply next) sourceBody)
    (typeTyped : CastTyping env 0 (SourceCasts env) ctx (.forallE domain codomain) (.sort u))
    (bodyTyped : CastTyping env 0 (SourceCasts env) ((.forallE domain codomain)::ctx) sourceBody (optionType Step.stepState))
    (valueTyped : CastTyping env 0 (SourceCasts env) ctx functionValue (.forallE domain codomain)) :
    Source ds (env := env) ctx p σ scope (.letE binder ty value next flag) native code quotation .step := by
  obtain ⟨reduced,source⟩ := let_representations typeRep valueRep bodyRep binder flag
  exact .stepFunctionLet binder ty value next flag binding tail typeRep typeTyped bodyTyped valueTyped reduced source

/-- The result type excludes an additional outer lambda. This derives the
last-spine condition from a source body, rather than asking each caller. -/
theorem Source.bodyNotLambda (source : Source ds (env := env) ctx p σ scope raw native code quotation)
    (setup : AliasSetup env) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (fresh : ScopedSyntax.Fresh setup) (exposure : Exposure env)
    (inputs : InputsTyped env ctx p) (locals : ScalarSyntax.Locals env ctx p) :
    ∀ name ty body info, σ.apply raw ≠ .lam name ty body info := by
  obtain ⟨core,rep,typed⟩ := source.bodyTyping setup library closed fresh exposure inputs locals
  intro name ty body info same
  rw [same] at rep
  cases rep
  cases typed

/-- Shared construction of a helper value, its type and its representation.
The surrounding computation may be an ordinary or a loop body. -/
theorem Source.lambdaTyping {functionBody : Lean.Expr}
    (functionSource : Source ds (env := env) (domains.reverse ++ ctx) functionInputs
      functionSubstitution functionScope functionBody functionNative functionCode functionQuotation)
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

/-- Build a retained helper of any arity from the existing lambda judgment
and its body Source. Parameter types are independent static typing conditions;
value typing and function-type formation are conclusions, not obligations
repeated by each source program. -/
theorem Source.functionLetFromLambda {functionBody : Lean.Expr} {sourceBody domain : VExpr}
    (setup : AliasSetup env) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (fresh : ScopedSyntax.Fresh setup) (exposure : Exposure env)
    (binder : Lean.Name) (ty value next : Lean.Expr) (flag : Bool)
    (binding : BindingValue scope ctx.length σ value closure)
    (tail : Source ds (env := env) ctx p (letSubstitution σ value) (.push (some closure) scope) next native code quotation)
    (functionSource : Source ds (env := env) ((domain::domains).reverse ++ ctx) functionInputs
      functionSubstitution functionScope functionBody functionNative functionCode functionQuotation)
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
    Source ds (env := env) ctx p σ scope (.letE binder ty value next flag) native code quotation := by
  obtain ⟨functionCore,level,functionRep,functionTyped,typeTyped⟩ :=
    functionSource.lambdaTyping setup library closed fresh exposure inputs locals shape represented parameters
  exact .functionLetInferred binder ty value next flag binding tail typeRep
    functionRep bodyRep typeTyped bodyTyped functionTyped

/-- The same helper-value construction inside a ForInStep computation.
Only the continuation's result differs from the ordinary-body rule. -/
theorem Source.stepFunctionLetFromLambda {functionBody : Lean.Expr} {sourceBody domain : VExpr}
    (setup : AliasSetup env) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (fresh : ScopedSyntax.Fresh setup) (exposure : Exposure env)
    (binder : Lean.Name) (ty value next : Lean.Expr) (flag : Bool)
    (binding : BindingValue scope ctx.length σ value closure)
    (tail : Source ds (env := env) ctx p (letSubstitution σ value) (.push (some closure) scope) next native code quotation .step)
    (functionSource : Source ds (env := env) ((domain::domains).reverse ++ ctx) functionInputs
      functionSubstitution functionScope functionBody functionNative functionCode functionQuotation)
    (inputs : InputsTyped env ((domain::domains).reverse ++ ctx) functionInputs)
    (locals : ScalarSyntax.Locals env ((domain::domains).reverse ++ ctx) functionInputs)
    (shape : LambdaSource (σ.apply value) nativeDomains (functionSubstitution.apply functionBody))
    (represented : List.Forall₂ Represents nativeDomains (domain::domains))
    (parameters : ∀ d ∈ domain::domains, ∃ u, CastTyping env 0 (SourceCasts env) [] d (.sort u))
    (typeRep : Represents (σ.apply ty) (.forallE domain (domains.foldr VExpr.forallE (optionType stateType))))
    (bodyRep : Represents ((under σ).apply next) sourceBody)
    (bodyTyped : CastTyping env 0 (SourceCasts env)
      ((.forallE domain (domains.foldr VExpr.forallE (optionType stateType)))::ctx)
      sourceBody (optionType Step.stepState)) :
    Source ds (env := env) ctx p σ scope (.letE binder ty value next flag) native code quotation .step := by
  obtain ⟨functionCore,level,functionRep,functionTyped,typeTyped⟩ :=
    functionSource.lambdaTyping setup library closed fresh exposure inputs locals shape represented parameters
  exact .stepFunctionLetInferred binder ty value next flag binding tail typeRep
    functionRep bodyRep typeTyped bodyTyped functionTyped

/-- A lambda's body may be any already-supported structured computation.
Its function type and value typing follow from that Source, uniformly in the
surrounding captures. The open continuation's typing remains explicit. -/
theorem Source.stateFunctionLetFromSource {functionBody : Lean.Expr} {sourceBody : VExpr}
    (setup : AliasSetup env) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (fresh : ScopedSyntax.Fresh setup) (exposure : Exposure env)
    (inputs : InputsTyped env ctx p) (locals : ScalarSyntax.Locals env ctx p)
    (binder : Lean.Name) (ty value next : Lean.Expr) (flag : Bool)
    (argumentName : Lean.Name) (argumentInfo : Lean.BinderInfo)
    (binding : BindingValue scope ctx.length σ value closure)
    (tail : Source ds (env := env) ctx p (letSubstitution σ value) (.push (some closure) scope) next native code quotation)
    (functionSource : Source ds (env := env) (stateType::ctx) {p.lift with s := .bvar 0}
      functionSubstitution functionScope functionBody functionNative functionCode functionQuotation)
    (valueShape : σ.apply value = .lam argumentName state (functionSubstitution.apply functionBody) argumentInfo)
    (typeRep : Represents (σ.apply ty) (.forallE stateType (optionType stateType)))
    (bodyRep : Represents ((under σ).apply next) sourceBody)
    (bodyTyped : CastTyping env 0 (SourceCasts env) ((.forallE stateType (optionType stateType))::ctx)
      sourceBody (optionType stateType)) :
    Source ds (env := env) ctx p σ scope (.letE binder ty value next flag) native code quotation := by
  apply Source.functionLetFromLambda setup library closed fresh exposure binder ty value next flag binding tail
    functionSource (inputs.nextState closed) (locals.nextState closed)
    (domain := stateType) (domains := []) (nativeDomains := [state])
  · rw [valueShape]
    exact .last (functionSource.bodyNotLambda setup library closed fresh exposure
      (inputs.nextState closed) (locals.nextState closed))
  · exact .cons (.constant rfl) .nil
  · intro d member
    simp only [List.mem_singleton] at member
    subst d
    exact ⟨_,.constant library.returns.state (by simp) rfl⟩
  · exact typeRep
  · exact bodyRep
  · exact bodyTyped

/-- Preserve the actual inferred parameter annotations as well as the
requested checks. Prefix typing uses these annotations before substitution;
the caller does not re-infer each argument or assume alias equality. -/
theorem argumentsWithShapesFromSyntax (library : ScopedSyntax.Library env)
    (inputs : InputsTyped env ctx p) (typing : LexicalScalarCode.ScopeTyped env ctx p)
    (arguments : List.Forall₂ (fun domain raw =>
      (domain = stateType ∧ raw = p.s) ∨
      ∃ annotation : WordBinder.Annotation, domain = annotation.core ∧
        LexicalScalarSyntax.Form env ctx p [] raw ∧ LexicalScalarSyntax.StaticRegisters raw) domains rawArgs) :
    ∃ args actual, List.Forall₂ Represents rawArgs args ∧
      List.Forall₂ (fun ty arg => CastTyping env 0 (SourceCasts env) ctx arg ty) actual args ∧
      List.Forall₂ (fun domain arg => CheckedTyping env 0 (SourceCasts env) ctx arg domain) domains args ∧
      (∀ domain ∈ domains, CastTyping env 0 (SourceCasts env) [] domain (.sort (.succ .zero))) ∧
      (∀ ty ∈ actual, CastTyping env 0 (SourceCasts env) [] ty (.sort (.succ .zero))) ∧
      List.Forall₂ (fun declared inferred =>
        (declared = stateType ∧ inferred = stateType) ∨
        ∃ a b : WordBinder.Annotation, declared = a.core ∧ inferred = b.core) domains actual := by
  induction arguments with
  | nil => exact ⟨[],[],.nil,.nil,.nil,by simp,by simp,.nil⟩
  | @cons domain raw domains raws first rest ih =>
    obtain ⟨args,actual,represented,exactTypes,checkedTypes,parametersTyped,actualTyped,shapes⟩ := ih
    rcases first with ⟨rfl,rfl⟩ | ⟨annotation,rfl,form,static⟩
    · have stateTyped : CastTyping env 0 (SourceCasts env) [] stateType (.sort (.succ .zero)) :=
        .constant library.steps.state (by simp) rfl
      refine ⟨inputs.s.val::args,stateType::actual,.cons inputs.s.property represented,
        .cons (inputs.hs.withCasts _) exactTypes,.cons (.exact (inputs.hs.withCasts _)) checkedTypes,?_,?_,.cons (Or.inl ⟨rfl,rfl⟩) shapes⟩
      · intro d hd; rcases List.mem_cons.mp hd with rfl | hd
        · exact stateTyped
        · exact parametersTyped d hd
      · intro d hd; rcases List.mem_cons.mp hd with rfl | hd
        · exact stateTyped
        · exact actualTyped d hd
    · obtain ⟨value,actualAnnotation,rep,valueTyped,_⟩ := form.evidence static library.scalars library.decisions inputs typing (by simp)
      have rep : Represents raw value := by simpa only [LexicalScalarSyntax.expand_nil] using rep
      refine ⟨value::args,actualAnnotation.core::actual,.cons rep represented,
        .cons valueTyped exactTypes,.cons (annotation.argument (actualAnnotation.result valueTyped)) checkedTypes,?_,?_,.cons (Or.inr ⟨annotation,actualAnnotation,rfl,rfl⟩) shapes⟩
      · intro d hd; rcases List.mem_cons.mp hd with rfl | hd
        · exact (annotation.type_typed library.scalars.toSignatures).withCasts _
        · exact parametersTyped d hd
      · intro d hd; rcases List.mem_cons.mp hd with rfl | hd
        · exact (actualAnnotation.type_typed library.scalars.toSignatures).withCasts _
        · exact actualTyped d hd

/-- Compatibility projection of the same argument induction. -/
theorem argumentsWithTypesFromSyntax (library : ScopedSyntax.Library env)
    (inputs : InputsTyped env ctx p) (typing : LexicalScalarCode.ScopeTyped env ctx p)
    (arguments : List.Forall₂ (fun domain raw =>
      (domain = stateType ∧ raw = p.s) ∨
      ∃ annotation : WordBinder.Annotation, domain = annotation.core ∧
        LexicalScalarSyntax.Form env ctx p [] raw ∧ LexicalScalarSyntax.StaticRegisters raw) domains rawArgs) :
    ∃ args actual, List.Forall₂ Represents rawArgs args ∧
      List.Forall₂ (fun ty arg => CastTyping env 0 (SourceCasts env) ctx arg ty) actual args ∧
      List.Forall₂ (fun domain arg => CheckedTyping env 0 (SourceCasts env) ctx arg domain) domains args ∧
      (∀ domain ∈ domains, CastTyping env 0 (SourceCasts env) [] domain (.sort (.succ .zero))) ∧
      (∀ ty ∈ actual, CastTyping env 0 (SourceCasts env) [] ty (.sort (.succ .zero))) := by
  obtain ⟨args,actual,rep,exactTypes,checkedTypes,parametersTyped,actualTyped,shapes⟩ :=
    argumentsWithShapesFromSyntax library inputs typing arguments
  exact ⟨args,actual,rep,exactTypes,checkedTypes,parametersTyped,actualTyped⟩

/-- Each argument is described by source syntax and its parameter spelling.
The induction constructs all representations and actual checked argument types. -/
theorem argumentsFromSyntax (library : ScopedSyntax.Library env)
    (inputs : InputsTyped env ctx p) (typing : LexicalScalarCode.ScopeTyped env ctx p)
    (arguments : List.Forall₂ (fun domain raw =>
      (domain = stateType ∧ raw = p.s) ∨
      ∃ annotation : WordBinder.Annotation, domain = annotation.core ∧
        LexicalScalarSyntax.Form env ctx p [] raw ∧ LexicalScalarSyntax.StaticRegisters raw) domains rawArgs) :
    ∃ args, List.Forall₂ Represents rawArgs args ∧
      List.Forall₂ (fun domain arg => CheckedTyping env 0 (SourceCasts env) ctx arg domain) domains args ∧
      ∀ domain ∈ domains, CastTyping env 0 (SourceCasts env) [] domain (.sort (.succ .zero)) := by
  obtain ⟨args,actual,rep,exactTypes,checkedTypes,parametersTyped,actualTyped⟩ :=
    argumentsWithTypesFromSyntax library inputs typing arguments
  exact ⟨args,rep,checkedTypes,parametersTyped⟩

private theorem argument_representation_unique
    (first : List.Forall₂ Represents rawArgs firstArgs) (second : List.Forall₂ Represents rawArgs secondArgs) :
    firstArgs = secondArgs := by
  induction first generalizing secondArgs with
  | nil => cases second; rfl
  | cons rep reps ih =>
    cases second with
    | cons other others => rw [rep.unique other,ih others]

/-- Existing low-level call rules may name core arguments. Their checked
types still follow from source syntax; no per-argument type derivation or
successful checker result is required. -/
theorem argumentsTypedFromSyntax (library : ScopedSyntax.Library env)
    (inputs : InputsTyped env ctx p) (typing : LexicalScalarCode.ScopeTyped env ctx p)
    (arguments : List.Forall₂ (fun domain raw =>
      (domain = stateType ∧ raw = p.s) ∨
      ∃ annotation : WordBinder.Annotation, domain = annotation.core ∧
        LexicalScalarSyntax.Form env ctx p [] raw ∧ LexicalScalarSyntax.StaticRegisters raw) domains rawArgs)
    (represented : List.Forall₂ Represents rawArgs args) :
    List.Forall₂ (fun domain arg => CheckedTyping env 0 (SourceCasts env) ctx arg domain) domains args ∧
      ∀ domain ∈ domains, CastTyping env 0 (SourceCasts env) [] domain (.sort (.succ .zero)) := by
  obtain ⟨derived,rep,typed,parameters⟩ := argumentsFromSyntax library inputs typing arguments
  exact argument_representation_unique rep represented ▸ ⟨typed,parameters⟩


theorem argumentsTypedWithShapesFromSyntax (library : ScopedSyntax.Library env)
    (inputs : InputsTyped env ctx p) (typing : LexicalScalarCode.ScopeTyped env ctx p)
    (arguments : List.Forall₂ (fun domain raw =>
      (domain = stateType ∧ raw = p.s) ∨
      ∃ annotation : WordBinder.Annotation, domain = annotation.core ∧
        LexicalScalarSyntax.Form env ctx p [] raw ∧ LexicalScalarSyntax.StaticRegisters raw) domains rawArgs)
    (represented : List.Forall₂ Represents rawArgs args) :
    ∃ actual,
      List.Forall₂ (fun ty arg => CastTyping env 0 (SourceCasts env) ctx arg ty) actual args ∧
      List.Forall₂ (fun domain arg => CheckedTyping env 0 (SourceCasts env) ctx arg domain) domains args ∧
      (∀ domain ∈ domains, CastTyping env 0 (SourceCasts env) [] domain (.sort (.succ .zero))) ∧
      (∀ ty ∈ actual, CastTyping env 0 (SourceCasts env) [] ty (.sort (.succ .zero))) ∧
      List.Forall₂ (fun declared inferred =>
        (declared = stateType ∧ inferred = stateType) ∨
        ∃ a b : WordBinder.Annotation, declared = a.core ∧ inferred = b.core) domains actual := by
  obtain ⟨derived,actual,rep,exactTypes,checkedTypes,parametersTyped,actualTyped,shapes⟩ :=
    argumentsWithShapesFromSyntax library inputs typing arguments
  exact argument_representation_unique rep represented ▸ ⟨actual,exactTypes,checkedTypes,parametersTyped,actualTyped,shapes⟩

/-- Lookup of a nondependent function type is a source-scope condition. The
lifting performed by de Bruijn lookup is discharged once from closedness. -/
private theorem lookup_closed_type (selected : ctx[index]? = some ty) (closed : ty.ClosedN 0) :
    Lookup ctx index ty := by
  induction ctx generalizing index with
  | nil => simp at selected
  | cons binder rest ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at selected
      subst binder
      simpa only [closed.lift_eq] using (Lookup.zero (Γ := rest) (ty := ty))
    | succ index =>
      simpa only [closed.lift_eq] using Lookup.succ (A := binder) (ih selected)

/-- Type an open call before substituting the bound helper value. Source
argument syntax supplies checked Word/BV32 conversions and the function's
closed telescope; clients provide only its slot in the lexical type context.
This applies to arbitrary arity and is shared by all enclosing constructs. -/
theorem boundCallTypingFromSyntax (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env)
    (inputs : InputsTyped env ctx p) (typing : LexicalScalarCode.ScopeTyped env ctx p)
    (arguments : List.Forall₂ (fun domain raw =>
      (domain = stateType ∧ raw = p.s) ∨
      ∃ annotation : WordBinder.Annotation, domain = annotation.core ∧
        LexicalScalarSyntax.Form env ctx p [] raw ∧ LexicalScalarSyntax.StaticRegisters raw) domains rawArgs)
    (selected : ctx[index]? = some (domains.foldr VExpr.forallE (optionType stateType))) :
    ∃ core, Represents (rawArgs.foldl Lean.Expr.app (.bvar index)) core ∧
      CastTyping env 0 (SourceCasts env) ctx core (optionType stateType) := by
  obtain ⟨args,rep,types,parameters⟩ := argumentsFromSyntax library inputs typing arguments
  have resultType : CastTyping env 0 (SourceCasts env) [] (optionType stateType) (.sort (.succ .zero)) :=
    .application (.constant library.steps.option (by simp; trivial) rfl)
      (.constant library.steps.state (by simp) rfl)
  have suffixClosed := functionType_suffix_closed domains closed (fun d hd => ⟨_,parameters d hd⟩) resultType
  have allClosed := suffixClosed 0
  simp only [List.drop_zero] at allClosed
  exact ⟨_,app_represents .bvar rep,
    LeanTypeReduction.checked_spine_typed types suffixClosed (.bvar (lookup_closed_type selected allClosed))⟩

/-- Capturing and applying one parameter at the same lexical depth is ordinary
source substitution. This is independent of parsing or generated code. -/
theorem closure_single (depth : Nat) (argument body : Lean.Expr) :
    (closureSubstitution depth depth .identity [argument]).apply body =
      LeanBindings.instantiate argument body := by
  simp only [closureSubstitution,Substitution.apply,LeanBindings.instantiate]
  congr 1
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    simp [closureReference,Substitution.reference,LeanBindings.rename]

/-- Source scope and declaration facts construct the fixed-array entry once.
This definition depends on source derivations, not a successful frontend run. -/
def Source.toEntry (source : Source ds (env := env) context parameters .identity .empty raw native code quotation)
    (scope_ok : LeanScalar.wellScoped 1 raw = true) (unique : FixedMemory.unique ds = true) :
    FixedHLS.Entry (native 0 0 0 []) where
  program := {
    code := code
    correct := fun i x y s => (source.facts.2 i x y s []).trans
      (source.independent (show LexicalScalarCode.ExternalAt 1 parameters from ⟨rfl,rfl,rfl⟩) scope_ok i x y [] s) }
  declarations := ds
  unique := unique
  declared := source.facts.1

/-- Construct the command and native computation from the existing
computation-free helper grammar. Static conditions are propagated by the
same requirement parameter as the structured body grammar. -/
theorem constructFunctionSource
    (form : FunctionSyntax.Syntax env ctx p σ scope raw requirements mode) :
    (∀ e, requirements e → FixedSequenceCompleteness.InputConditions ds e) →
    ∃ native code quotation, Source ds (env := env) ctx p σ scope raw native code quotation mode := by
  induction form with
  | @plain mode ctx p raw requirements form =>
    intro conditions
    obtain ⟨f,c,q,h⟩ := FixedSequenceCompleteness.constructSource form conditions
    exact ⟨f,c,q,.plain h⟩
  | @base σ p raw ctx requirements scope head form =>
    intro conditions
    obtain ⟨f,c,q,h⟩ := FixedSequenceCompleteness.constructSource form conditions
    exact ⟨f,c,q,.base head h⟩
  | @valueCurrent ctx p σ scope raw requirements current =>
    intro conditions
    exact ⟨_,_,_,.valueCurrent current⟩
  | @valueAssign ctx p requirements σ scope st v register rn current value checked =>
    intro conditions
    have checked := conditions _ checked
    rw [substitute_valueAssign] at checked
    obtain ⟨f,c,q,value⟩ := FixedScalarCompleteness.Scoped.fromSyntax value checked.registers.2
    exact ⟨_,_,_,.valueAssign register rn current value⟩
  | @yield ctx p σ scope raw requirements value iv =>
    intro conditions
    obtain ⟨f,c,q,value⟩ := iv conditions
    exact ⟨_,_,_,.yield value⟩
  | @stepSequence ctx p σ scope a requirements b first next binder info ia ib =>
    intro conditions
    obtain ⟨f,ac,aq,first⟩ := ia conditions
    obtain ⟨g,bc,bq,next⟩ := ib conditions
    exact ⟨_,_,_,.stepSequence first next binder info⟩
  | @forStatic ctx p σ scope original requirements a b c st start stop stride current body kn tn ki ti checked ib =>
    intro conditions
    have checked := conditions _ checked
    rw [StructuralLoop.substitute_forStatic] at checked
    obtain ⟨a,b,c,start,stop,stride⟩ := checked.staticRange _ _ _ _ _ rfl
    obtain ⟨f,bc,bq,body⟩ := ib conditions
    exact ⟨_,_,_,.forStatic start stop stride current body kn tn ki ti⟩
  | @unitBody ctx σ scope b requirements p next binder info ib =>
    intro conditions
    obtain ⟨f,c,q,next⟩ := ib conditions
    exact ⟨_,_,_,.unitBody next binder info⟩
  | @unitLoop ctx σ scope b requirements p next binder info ib =>
    intro conditions
    obtain ⟨f,c,q,next⟩ := ib conditions
    exact ⟨_,_,_,.unitLoop next binder info⟩
  | @forRange ctx p σ scope original requirements n st kind count current body kn tn ki ti checked ib =>
    intro conditions
    have checked := conditions _ checked
    rw [NaturalLoop.Kind.substitute_source] at checked
    have static : LexicalScalarSyntax.StaticRegisters (σ.apply n) := by
      cases kind with
      | forIn => exact checked.registers.1.1.2.2.2
      | fold => exact checked.registers.2.2.2
    obtain ⟨f,nc,nq,count⟩ := FixedScalarCompleteness.Scoped.fromSyntax count static
    obtain ⟨g,bc,bq,body⟩ := ib conditions
    exact ⟨_,_,_,.forRange kind count current body kn tn ki ti⟩
  | @letValue ctx p σ scope b requirements v annotation value next binder flag checked ib =>
    intro conditions
    have checked := conditions _ checked
    rw [substitute_annotated_let] at checked
    obtain ⟨f,c,q,value⟩ := FixedScalarCompleteness.Scoped.fromSyntax value checked.registers.1
    obtain ⟨g,bc,bq,next⟩ := ib conditions
    exact ⟨_,_,_,.letValue annotation value next binder flag⟩
  | @bindValue ctx p σ scope b requirements v annotation value next binder info checked ib =>
    intro conditions
    have checked := conditions _ checked
    rw [WordBinder.substitute_readSource] at checked
    obtain ⟨f,c,q,value⟩ := FixedReadSourceCompleteness.constructSource value (checked.readBody annotation _ _ rfl)
    obtain ⟨g,bc,bq,next⟩ := ib conditions
    exact ⟨_,_,_,.bindValue annotation value next binder info⟩
  | @stepBindValue ctx p σ scope b requirements v annotation value next binder info checked ib =>
    intro conditions
    have checked := conditions _ checked
    rw [WordBinder.substitute_stepReadSource] at checked
    obtain ⟨f,c,q,value⟩ := FixedReadSourceCompleteness.constructSource value (checked.readStep annotation _ _ rfl)
    obtain ⟨g,bc,bq,next⟩ := ib conditions
    exact ⟨_,_,_,.stepBindValue annotation value next binder info⟩
  | @stepLetValue ctx p σ scope b requirements v annotation value next binder flag checked ib =>
    intro conditions
    have checked := conditions _ checked
    rw [substitute_annotated_let] at checked
    obtain ⟨f,c,q,value⟩ := FixedScalarCompleteness.Scoped.fromSyntax value checked.registers.1
    obtain ⟨g,bc,bq,next⟩ := ib conditions
    exact ⟨_,_,_,.stepLetValue annotation value next binder flag⟩
  | @stateLet ctx p σ scope v requirements b value next notAlias binder flag ia ib =>
    intro conditions
    obtain ⟨f,ac,aq,value⟩ := ia conditions
    obtain ⟨g,bc,bq,next⟩ := ib conditions
    exact ⟨_,_,_,.stateLet value next notAlias binder flag⟩
  | @stepStateLet ctx p σ scope v requirements b value next notAlias binder flag ia ib =>
    intro conditions
    obtain ⟨f,ac,aq,value⟩ := ia conditions
    obtain ⟨g,bc,bq,next⟩ := ib conditions
    exact ⟨_,_,_,.stepStateLet value next notAlias binder flag⟩
  | @stateAlias ctx σ scope b requirements p st current next binder flag ib =>
    intro conditions
    obtain ⟨f,c,q,next⟩ := ib conditions
    exact ⟨_,_,_,.stateAlias current next binder flag⟩
  | @stepAlias ctx σ scope b requirements p st current next binder flag ib =>
    intro conditions
    obtain ⟨f,c,q,next⟩ := ib conditions
    exact ⟨_,_,_,.stepAlias current next binder flag⟩
  | @sequence ctx p σ scope a requirements b first next binder info ia ib =>
    intro conditions
    obtain ⟨f,ac,aq,first⟩ := ia conditions
    obtain ⟨g,bc,bq,next⟩ := ib conditions
    exact ⟨_,_,_,.sequence first next binder info⟩
  | @branch ctx p σ scope a requirements b v d value decision yes no checked ia ib =>
    intro conditions
    have checked := conditions _ checked
    rw [substitute_branch] at checked
    have static : LexicalScalarSyntax.StaticRegisters (σ.apply v) := by
      cases σ <;> exact checked.registers.1.1.1.2.1.2.1.2
    obtain ⟨f,c,q,value⟩ := FixedScalarCompleteness.Scoped.fromSyntax value static
    obtain ⟨g,ac,aq,yes⟩ := ia conditions
    obtain ⟨h,bc,bq,no⟩ := ib conditions
    exact ⟨_,_,_,.branch value decision yes no⟩
  | @booleanBranch ctx p σ scope a requirements b v value yes no checked ia ib =>
    intro conditions
    have checked := conditions _ checked
    rw [substitute_branch] at checked
    have static : LexicalScalarSyntax.StaticRegisters (σ.apply v) := by
      cases σ <;> exact checked.registers.1.1.1.2.1.2.1.2
    obtain ⟨f,c,q,value⟩ := FixedScalarCompleteness.Scoped.fromSyntax value static
    obtain ⟨g,ac,aq,yes⟩ := ia conditions
    obtain ⟨h,bc,bq,no⟩ := ib conditions
    exact ⟨_,_,_,.booleanBranch value yes no⟩
  | @annotatedBooleanBranch ctx p σ scope a requirements b v valueCore annotation operand value represented typed form yes no checked ia ib =>
    intro conditions
    have checked := conditions _ checked
    rw [AnnotatedBranch.substitute_source] at checked
    have static : LexicalScalarSyntax.StaticRegisters (σ.apply v) := by
      cases σ <;> cases annotation <;> exact checked.registers.1.1.1.2.1.2.1.2
    obtain ⟨f,c,q,value⟩ := FixedScalarCompleteness.Scoped.fromSyntax value static
    obtain ⟨g,ac,aq,yes⟩ := ia conditions
    obtain ⟨h,bc,bq,no⟩ := ib conditions
    exact ⟨_,_,_,.annotatedBooleanBranch annotation operand value represented typed form yes no⟩
  | @annotatedStepBooleanBranch ctx p σ scope a requirements b v valueCore annotation operand value represented typed form yes no checked ia ib =>
    intro conditions
    have checked := conditions _ checked
    rw [AnnotatedBranch.Loop.substitute_source] at checked
    have static : LexicalScalarSyntax.StaticRegisters (σ.apply v) := by
      cases σ <;> cases annotation <;> exact checked.registers.1.1.1.2.1.2.1.2
    obtain ⟨f,c,q,value⟩ := FixedScalarCompleteness.Scoped.fromSyntax value static
    obtain ⟨g,ac,aq,yes⟩ := ia conditions
    obtain ⟨h,bc,bq,no⟩ := ib conditions
    exact ⟨_,_,_,.annotatedStepBooleanBranch annotation operand value represented typed form yes no⟩
  | @stepBooleanBranch ctx p σ scope a requirements b v value yes no checked ia ib =>
    intro conditions
    have checked := conditions _ checked
    rw [substitute_stepBranch] at checked
    have static : LexicalScalarSyntax.StaticRegisters (σ.apply v) := by
      cases σ <;> exact checked.registers.1.1.1.2.1.2.1.2
    obtain ⟨f,c,q,value⟩ := FixedScalarCompleteness.Scoped.fromSyntax value static
    obtain ⟨g,ac,aq,yes⟩ := ia conditions
    obtain ⟨h,bc,bq,no⟩ := ib conditions
    exact ⟨_,_,_,.stepBooleanBranch value yes no⟩
  | retainedCall fn argument allowed binding coherent arguments next count dt bt ft ats tc pt rr sr ih =>
    intro conditions
    obtain ⟨sw,nw,cw,qw,arguments⟩ := arguments
    obtain ⟨native,code,quotation,body⟩ := ih conditions
    exact ⟨_,_,_,.retainedCall fn argument allowed binding coherent arguments body count dt bt ft ats tc pt rr sr⟩
  | @functionLet scope σ closure ctx p requirements u sourceBody functionValue domain codomain binder ty value next flag binding tail typeRep typeTyped bodyTyped valueTyped reducedRep sourceRep ib =>
    intro conditions
    obtain ⟨f,c,q,derived⟩ := ib conditions
    exact ⟨_,_,_,.functionLet binder ty value next flag binding derived typeRep typeTyped bodyTyped valueTyped reducedRep sourceRep⟩
  | @stepFunctionLet scope σ closure ctx p requirements u sourceBody functionValue domain codomain binder ty value next flag binding tail typeRep typeTyped bodyTyped valueTyped reducedRep sourceRep ib =>
    intro conditions
    obtain ⟨f,c,q,derived⟩ := ib conditions
    exact ⟨_,_,_,.stepFunctionLet binder ty value next flag binding derived typeRep typeTyped bodyTyped valueTyped reducedRep sourceRep⟩

/-- Construct the ordinary retained entry directly under the actual loaded
library, then reuse Entry.compile_total. No direct-substitution compiler is
selected here; both the syntax and generated entry use retained arguments.
Parser success, generated commands and Entries are conclusions. -/
theorem generatesRetainedSyntaxInstalled (input : NativeEnvironment.Input nativeEnvironment name)
    (form : ∀ (env : VEnv) (setup : AliasSetup env) (library : ScopedSyntax.Library env),
      SignatureExtension StandardLibrary.model env → ClosedConstantTypes env → ScopedSyntax.Fresh setup →
      Exposure env → FunctionSyntax.Syntax env context parameters .identity .empty input.header.body
        (FixedSequenceCompleteness.InputConditions ds))
    (scope_ok : LeanScalar.wellScoped 1 input.header.body = true)
    (unique : FixedMemory.unique ds = true) (outputs : List Nat)
    (outputsDeclared : outputs.all (fun a => (FixedMemory.lookup ds a).isSome) = true)
    (budget : Nat) (strategy : Circuit.Pipelining.LoopStrategy) :
    ∃ result, StructuralBody.compileRetained nativeEnvironment name = some result ∧ result.CodeTyped ∧
      ∃ env : VEnv, ∃ native code,
        Source ds (env := env) context parameters .identity .empty input.header.body native code result.code ∧
        ∃ entry : FixedHLS.Entry (native 0 0 0 []), entry.program.code = code ∧ entry.declarations = ds ∧
          ∃ compiled, entry.compile outputs budget strategy = .ok compiled := by
  refine input.compilesInstalledCodeWith StructuralBody.bodyRetained (fun quotation => ∃ env : VEnv, ∃ native code,
    Source ds (env := env) context parameters .identity .empty input.header.body native code quotation ∧
    ∃ entry : FixedHLS.Entry (native 0 0 0 []), entry.program.code = code ∧ entry.declarations = ds ∧
      ∃ compiled, entry.compile outputs budget strategy = .ok compiled) ?_
  intro env setup library installed closed fresh exposure
  obtain ⟨native,code,quotation,source⟩ := constructFunctionSource
    (form env setup library installed closed fresh exposure) (fun _ h => h)
  obtain ⟨piece,success,typed,_,same⟩ := source.complete setup library closed fresh exposure
    (initialInputs library.connection.word library.connection.nilWords) (.empty rfl)
  let entry := source.toEntry scope_ok unique
  obtain ⟨compiled,done⟩ := entry.compile_total outputs budget strategy outputsDeclared
  refine ⟨piece,success,typed,env,native,code,?_,entry,rfl,rfl,compiled,done⟩
  exact same.symm ▸ source

/-- The source judgment for the retained traversal constructs the whole fixed
array entry and RTL result. No successful parse, generated command or Entry
is an input. Retained helper applications use the same recursive Source/Syntax induction;
the independent call typing and representation conditions remain explicit. -/
theorem generatesRetainedSyntax (input : NativeEnvironment.Input nativeEnvironment name)
    (form : FunctionSyntax.Syntax StandardLibrary.model context parameters .identity .empty input.header.body
      (FixedSequenceCompleteness.InputConditions ds))
    (scope_ok : LeanScalar.wellScoped 1 input.header.body = true)
    (unique : FixedMemory.unique ds = true) (outputs : List Nat)
    (outputsDeclared : outputs.all (fun a => (FixedMemory.lookup ds a).isSome) = true)
    (budget : Nat) (strategy : Circuit.Pipelining.LoopStrategy) :
    ∃ native code quotation,
      Source ds (env := StandardLibrary.model) context parameters .identity .empty input.header.body native code quotation ∧
      ∃ result, StructuralBody.compileRetained nativeEnvironment name = some result ∧
        result.CodeTyped ∧ result.code = quotation ∧
        ∃ entry : FixedHLS.Entry (native 0 0 0 []), entry.program.code = code ∧ entry.declarations = ds ∧
          ∃ compiled, entry.compile outputs budget strategy = .ok compiled := by
  obtain ⟨native,code,quotation,source⟩ := constructFunctionSource form (fun _ h => h)
  let entry := source.toEntry scope_ok unique
  obtain ⟨compiled,done⟩ := entry.compile_total outputs budget strategy outputsDeclared
  obtain ⟨result,parsed,typed,sameCode⟩ := input.compilesInstalledCodeWith StructuralBody.bodyRetained
    (fun emitted => emitted = quotation) (by
      intro env setup library installed closed fresh exposure
      have derived := source.install installed
      obtain ⟨piece,success,typed,_,same⟩ := derived.complete setup library closed fresh exposure
        (initialInputs library.connection.word library.connection.nilWords) (.empty rfl)
      exact ⟨piece,success,typed,same⟩)
  exact ⟨native,code,quotation,source,result,parsed,typed,sameCode,entry,rfl,rfl,compiled,done⟩

end IRComparison.WordFrontend.FixedFunctionCompleteness

namespace IRComparison.WordFrontend.FunctionSyntax
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic StructuralBody StructuralSyntax
set_option maxHeartbeats 2400000
/-- The ordinary helper telescope extends the existing source scope. State
parameters replace the current State; scalar parameters add retained values.
This is proof-side scope bookkeeping, not a source language or an IR. -/
def parameterInputs : List VExpr → Inputs → Inputs
  | [],p => p
  | domain::rest,p => parameterInputs rest
      (if domain = stateType then {p.lift with s := .bvar 0}
       else {p.lift with locals := .bvar 0::p.lift.locals})

private theorem annotation_not_state (a : WordBinder.Annotation) : a.core ≠ stateType := by
  cases a <;> simp [WordBinder.Annotation.core,wordType,bitvecType,stateType]

@[simp] theorem parameterInputs_scalar (a : WordBinder.Annotation) (rest : List VExpr) (p : Inputs) :
    parameterInputs (a.core::rest) p = parameterInputs rest {p.lift with locals := .bvar 0::p.lift.locals} := by
  simp only [parameterInputs,if_neg (annotation_not_state a)]

@[simp] theorem parameterInputs_state (rest : List VExpr) (p : Inputs) :
    parameterInputs (stateType::rest) p = parameterInputs rest {p.lift with s := .bvar 0} := by
  simp [parameterInputs]

/-- Proof-side parameter placement. The source lambda binds every parameter;
the retained call binds scalars and aliases State parameters to the current
State. This records existing contexts/references, not another source IR. -/
def parameterLayout (openStates : Bool) : List VExpr → List VExpr → Inputs → List Lean.Expr →
    List VExpr × Inputs × List Lean.Expr
  | [],ctx,p,saved => (ctx,p,saved)
  | domain::rest,ctx,p,saved =>
    if domain = stateType then
      if openStates then
        parameterLayout openStates rest (stateType::ctx) {p.lift with s := .bvar 0}
          (saved.map (LeanBindings.rename Nat.succ) ++ [.bvar 0])
      else parameterLayout openStates rest ctx p (saved ++ [p.s])
    else parameterLayout openStates rest (domain::ctx) {p.lift with locals := .bvar 0::p.lift.locals}
      (saved.map (LeanBindings.rename Nat.succ) ++ [.bvar 0])

@[simp] theorem parameterLayout_state (openStates : Bool) :
    parameterLayout openStates (stateType::rest) ctx p saved =
      if openStates then parameterLayout openStates rest (stateType::ctx) {p.lift with s := .bvar 0}
        (saved.map (LeanBindings.rename Nat.succ) ++ [.bvar 0])
      else parameterLayout openStates rest ctx p (saved ++ [p.s]) := by
  simp only [parameterLayout,ite_true]

@[simp] theorem parameterLayout_scalar (openStates : Bool) (a : WordBinder.Annotation) :
    parameterLayout openStates (a.core::rest) ctx p saved =
      parameterLayout openStates rest (a.core::ctx) {p.lift with locals := .bvar 0::p.lift.locals}
        (saved.map (LeanBindings.rename Nat.succ) ++ [.bvar 0]) := by
  simp only [parameterLayout,if_neg (annotation_not_state a)]

/-- Opening all parameters is exactly the already-used lambda scope. -/
theorem parameterLayout_open (domains : List VExpr) (ctx : List VExpr) (p : Inputs) (saved : List Lean.Expr) :
    parameterLayout true domains ctx p saved =
      (domains.reverse ++ ctx,parameterInputs domains p,openArguments domains.length saved) := by
  induction domains generalizing ctx p saved with
  | nil => rfl
  | cons domain rest ih =>
    by_cases same : domain = stateType
    · subst domain
      simp only [parameterLayout_state,ite_true,ih,parameterInputs_state,List.reverse_cons,
        List.append_assoc,List.singleton_append,List.length_cons,openArguments]
    · simp only [parameterLayout,if_neg same,parameterInputs,if_neg same,ih,
        List.reverse_cons,List.append_assoc,List.singleton_append,List.length_cons,openArguments]

/-- Both parameter placements preserve the source typing and reference
invariants. State aliases need no extra slot in the retained placement.
Saved arguments may already be present; they do not affect the input scope. -/
theorem parameterLayout_scope
    (library : ScopedSyntax.Library env) (closed : ClosedConstantTypes env)
    (inputs : InputsTyped env ctx p) (locals : ScalarSyntax.Locals env ctx p)
    (typing : LexicalScalarCode.ScopeTyped env ctx p)
    (domains : List VExpr)
    (allowed : ∀ d ∈ domains, d = stateType ∨ ∃ a : WordBinder.Annotation, d = a.core)
    (openStates : Bool) (saved : List Lean.Expr) :
    let frame := parameterLayout openStates domains ctx p saved
    Nonempty (InputsTyped env frame.1 frame.2.1) ∧
    Nonempty (ScalarSyntax.Locals env frame.1 frame.2.1) ∧
    LexicalScalarCode.ScopeTyped env frame.1 frame.2.1 ∧
    (ScalarSyntax.ReferenceScope p → ScalarSyntax.ReferenceScope frame.2.1) := by
  induction domains generalizing ctx p saved with
  | nil => exact ⟨⟨inputs⟩,⟨locals⟩,typing,id⟩
  | cons domain rest ih =>
    have remaining := fun d hd => allowed d (List.mem_cons_of_mem _ hd)
    rcases allowed domain (by simp) with rfl | ⟨a,rfl⟩
    · cases openStates with
      | false =>
        simpa only [parameterLayout_state,Bool.false_eq_true,ite_false] using
          ih inputs locals typing remaining (saved ++ [p.s])
      | true =>
        obtain ⟨ni,nl,nt,nr⟩ := ih (inputs.nextState closed) (locals.nextState closed)
          (typing.nextState closed) remaining (saved.map (LeanBindings.rename Nat.succ) ++ [.bvar 0])
        simpa only [parameterLayout_state,ite_true] using
          And.intro ni ⟨nl,nt,fun reference => nr reference.state⟩
    · obtain ⟨ni,nl,nt,nr⟩ := ih (a.nextInputs inputs closed library.scalars.toSignatures library.cons)
        (a.nextLocals locals closed) (typing.nextWord closed a) remaining
        (saved.map (LeanBindings.rename Nat.succ) ++ [.bvar 0])
      simpa only [parameterLayout_scalar] using
        And.intro ni ⟨nl,nt,fun reference => nr reference.scalar⟩

/-- Original lambda scopes use the same invariant proof as retained calls. -/
theorem parameterScope
    (library : ScopedSyntax.Library env) (closed : ClosedConstantTypes env)
    (inputs : InputsTyped env ctx p) (locals : ScalarSyntax.Locals env ctx p)
    (typing : LexicalScalarCode.ScopeTyped env ctx p)
    (domains : List VExpr)
    (allowed : ∀ d ∈ domains, d = stateType ∨ ∃ a : WordBinder.Annotation, d = a.core) :
    Nonempty (InputsTyped env (domains.reverse ++ ctx) (parameterInputs domains p)) ∧
    Nonempty (ScalarSyntax.Locals env (domains.reverse ++ ctx) (parameterInputs domains p)) ∧
    LexicalScalarCode.ScopeTyped env (domains.reverse ++ ctx) (parameterInputs domains p) ∧
    (ScalarSyntax.ReferenceScope p → ScalarSyntax.ReferenceScope (parameterInputs domains p)) := by
  simpa only [parameterLayout_open] using
    parameterLayout_scope library closed inputs locals typing domains allowed true []

/-- Word versus BitVec annotation changes do not change lexical positions or
which State is current. -/
theorem parameterInputs_retag
    (shapes : List.Forall₂ (fun declared inferred =>
      (declared = stateType ∧ inferred = stateType) ∨
      ∃ a b : WordBinder.Annotation, declared = a.core ∧ inferred = b.core) domains actual) (p : Inputs) :
    parameterInputs actual p = parameterInputs domains p := by
  induction shapes generalizing p with
  | nil => rfl
  | cons head rest ih =>
    rcases head with ⟨rfl,rfl⟩ | ⟨a,b,rfl,rfl⟩
    · simp only [parameterInputs_state]; exact ih _
    · simp only [parameterInputs_scalar]; exact ih _

/-- A partial application changes type spellings but keeps the same source
scope. Both sides are derived from the original argument shape relation. -/
theorem parameterInputs_prefix
    (shapes : List.Forall₂ (fun declared inferred =>
      (declared = stateType ∧ inferred = stateType) ∨
      ∃ a b : WordBinder.Annotation, declared = a.core ∧ inferred = b.core) domains actual) (n : Nat) (p : Inputs) :
    parameterInputs (actual.take n ++ domains.drop n) p = parameterInputs domains p := by
  induction shapes generalizing n p with
  | nil => simp [parameterInputs]
  | @cons domain inferred domains actual head rest ih =>
    cases n with
    | zero => simp
    | succ n =>
      rcases head with ⟨rfl,rfl⟩ | ⟨a,b,rfl,rfl⟩
      · simp only [List.take_succ_cons,List.drop_succ_cons,List.cons_append,parameterInputs_state]; exact ih n _
      · simp only [List.take_succ_cons,List.drop_succ_cons,List.cons_append,parameterInputs_scalar]; exact ih n _

theorem parameterTypes_prefix
    (shapes : List.Forall₂ (fun declared inferred =>
      (declared = stateType ∧ inferred = stateType) ∨
      ∃ a b : WordBinder.Annotation, declared = a.core ∧ inferred = b.core) domains actual) (n : Nat) :
    ∀ d ∈ actual.take n ++ domains.drop n, d = stateType ∨ ∃ a : WordBinder.Annotation, d = a.core := by
  have both : (∀ d ∈ domains, d = stateType ∨ ∃ a : WordBinder.Annotation, d = a.core) ∧
      (∀ d ∈ actual, d = stateType ∨ ∃ a : WordBinder.Annotation, d = a.core) := by
    induction shapes with
    | nil => simp
    | cons head rest ih =>
      rcases head with ⟨rfl,rfl⟩ | ⟨a,b,rfl,rfl⟩
      all_goals constructor
      all_goals intro d hd
      all_goals rcases List.mem_cons.mp hd with rfl | hd
      all_goals first | exact Or.inl rfl | exact Or.inr ⟨_,rfl⟩ | exact ih.1 d hd | exact ih.2 d hd
  intro d hd
  rcases List.mem_append.mp hd with hd | hd
  · exact both.2 d (List.mem_of_mem_take hd)
  · exact both.1 d (List.mem_of_mem_drop hd)
end IRComparison.WordFrontend.FunctionSyntax


namespace IRComparison.WordFrontend.FixedFunctionCompleteness
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic StructuralBody StructuralSyntax FunctionSyntax

end IRComparison.WordFrontend.FixedFunctionCompleteness

namespace IRComparison.WordFrontend.FunctionSyntax
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic StructuralBody StructuralSyntax
set_option maxHeartbeats 2400000

/-- Source-only composition also applies while a local helper remains an
opaque bound function. Neither child is required to have been compiled. -/
theorem sourceCheckedBindTyping (library : ScopedSyntax.Library env)
    (domainRep : Represents nativeDomain domain) (resultRep : Represents nativeResult result)
    (domainTyped : DirectTyping env 0 ctx domain (.sort (.succ .zero)))
    (resultTyped : DirectTyping env 0 ctx result (.sort (.succ .zero)))
    (domainClosed : domain.ClosedN 0) (resultClosed : result.ClosedN 0)
    (first : ∃ core, Represents a core ∧ CheckedTyping env 0 (SourceCasts env) ctx core (optionType domain))
    (next : ∃ core, Represents b core ∧ CastTyping env 0 (SourceCasts env) (domain::ctx) core (optionType result))
    (binder : Lean.Name) (info : Lean.BinderInfo) :
    ∃ core, Represents (Lean.mkApp2 (bindHead nativeDomain nativeResult) a (.lam binder nativeDomain b info)) core ∧
      CastTyping env 0 (SourceCasts env) ctx core (optionType result) := by
  obtain ⟨ac,ar,aTyped⟩ := first
  obtain ⟨bc,br,bt⟩ := next
  have headerRep : Represents (bindHead nativeDomain nativeResult) (optionBindHeader domain result) :=
    .app (.app (.app (.app (.constant rfl) (.constant rfl))
      (.app (.app (.constant rfl) (.constant rfl)) (.constant rfl))) domainRep) resultRep
  have head := (library.bind.header_typed domainTyped resultTyped domainClosed resultClosed).withCasts (SourceCasts env)
  have applied := CastTyping.checkedApplication head aTyped
  simp only [VExpr.inst,optionType,domainClosed.instN_eq (Nat.zero_le _),resultClosed.instN_eq (Nat.zero_le _)] at applied
  exact ⟨_,.app (.app headerRep ar) (.lam domainRep br),
    by simpa only [optionType,VExpr.inst,resultClosed.instN_eq (Nat.zero_le _)] using
      CastTyping.application applied (.lambda (domainTyped.withCasts _) bt)⟩

/-- Source-only composition also applies while a local helper remains an
opaque bound function. Neither child is required to have been compiled. -/
theorem sourceBindTyping (library : ScopedSyntax.Library env)
    (domainRep : Represents nativeDomain domain) (resultRep : Represents nativeResult result)
    (domainTyped : DirectTyping env 0 ctx domain (.sort (.succ .zero)))
    (resultTyped : DirectTyping env 0 ctx result (.sort (.succ .zero)))
    (domainClosed : domain.ClosedN 0) (resultClosed : result.ClosedN 0)
    (first : ∃ core, Represents a core ∧ CastTyping env 0 (SourceCasts env) ctx core (optionType domain))
    (next : ∃ core, Represents b core ∧ CastTyping env 0 (SourceCasts env) (domain::ctx) core (optionType result))
    (binder : Lean.Name) (info : Lean.BinderInfo) :
    ∃ core, Represents (Lean.mkApp2 (bindHead nativeDomain nativeResult) a (.lam binder nativeDomain b info)) core ∧
      CastTyping env 0 (SourceCasts env) ctx core (optionType result) := by
  exact sourceCheckedBindTyping library domainRep resultRep domainTyped resultTyped domainClosed resultClosed
    (by obtain ⟨core,rep,typed⟩ := first; exact ⟨core,rep,.exact typed⟩) next binder info

theorem sourceBooleanTyping (library : ScopedSyntax.Library env)
    (inputs : InputsTyped env ctx p) (scope : LexicalScalarCode.ScopeTyped env ctx p)
    (value : LexicalScalarSyntax.Form env ctx p [] v) (static : LexicalScalarSyntax.StaticRegisters v)
    (typeRep : Represents nativeType ty) (typeTyped : DirectTyping env 0 ctx ty (.sort (.succ .zero)))
    (typeClosed : ty.ClosedN 0)
    (yes : ∃ core, Represents a core ∧ CastTyping env 0 (SourceCasts env) ctx core ty)
    (no : ∃ core, Represents b core ∧ CastTyping env 0 (SourceCasts env) ctx core ty) :
    ∃ core, Represents (Step.nativeChoice nativeType (Branch.nativeCondition v)
      (Branch.nativeBooleanDecision v) a b) core ∧ CastTyping env 0 (SourceCasts env) ctx core ty := by
  obtain ⟨vc,annotation,vr,vt,_⟩ := value.evidence static library.scalars library.decisions inputs scope (by simp)
  simp only [LexicalScalarSyntax.expand_nil] at vr
  obtain ⟨ac,ar,aTyped⟩ := yes
  obtain ⟨bc,br,bt⟩ := no
  obtain ⟨conditionTyped,decisionTyped⟩ := library.decisions.condition_typed library.scalars.toSignatures (annotation.result vt)
  exact ⟨_,Step.nativeChoice_represents typeRep (Branch.condition_represents vr)
    (Branch.booleanDecision_represents vr) ar br,
    Branch.ite_typed typeTyped typeClosed conditionTyped decisionTyped aTyped bt library.ite⟩

theorem sourceForStaticTyping (library : ScopedSyntax.Library env)
    (inputs : InputsTyped env ctx p)
    (start : For.Bound env ctx a) (stop : For.Bound env ctx b) (stride : For.Bound env ctx c)
    (body : ∃ core, Represents original core ∧
      CastTyping env 0 (SourceCasts env) (stateType::wordType::ctx) core (optionType Step.stepState))
    (kn tn : Lean.Name) (ki ti : Lean.BinderInfo) :
    ∃ core, Represents (For.source a b c p.s (.lam kn word (.lam tn state original ti) ki)) core ∧
      CastTyping env 0 (SourceCasts env) ctx core (optionType stateType) := by
  obtain ⟨bc,br,bt⟩ := body
  have wordTyped : CastTyping env 0 (SourceCasts env) ctx wordType (.sort (.succ .zero)) :=
    .constant library.scalars.word (by simp) rfl
  have stateTyped : CastTyping env 0 (SourceCasts env) (wordType::ctx) stateType (.sort (.succ .zero)) :=
    .constant library.returns.state (by simp) rfl
  exact ⟨_,For.source_represents start.represented.property stop.represented.property stride.represented.property inputs.s.property
    (.lam (.constant rfl) (.lam (.constant rfl) br)),
    For.source_typed library.forHeader.header_typed library.range (start.typed.mono (fun _ _ _ h => .arithmetic h)) (stop.typed.mono (fun _ _ _ h => .arithmetic h)) (stride.typed.mono (fun _ _ _ h => .arithmetic h)) (inputs.hs.withCasts _)
      (.lambda wordTyped (.lambda stateTyped bt))⟩

/-- Both List.range iterator spellings share the same source typing rule;
the body may itself contain local calls, branches, or nested loops. -/
theorem sourceForRangeTyping (library : ScopedSyntax.Library env)
    (inputs : InputsTyped env ctx p) (scope : LexicalScalarCode.ScopeTyped env ctx p)
    (kind : NaturalLoop.Kind)
    (count : LexicalScalarSyntax.Form env ctx p [] n) (static : LexicalScalarSyntax.StaticRegisters n)
    (body : ∃ core, Represents original core ∧ CastTyping env 0 (SourceCasts env) (kind.context ctx)
      core (sourceResultType kind.mode))
    (kn tn : Lean.Name) (ki ti : Lean.BinderInfo) :
    ∃ core, Represents (kind.source n p.s (kind.nativeLambda kn tn ki ti original)) core ∧
      CastTyping env 0 (SourceCasts env) ctx core (optionType stateType) := by
  obtain ⟨nc,annotation,nr,nt,_⟩ := count.evidence static library.scalars library.decisions inputs scope (by simp)
  simp only [LexicalScalarSyntax.expand_nil] at nr
  obtain ⟨bc,br,bt⟩ := body
  have first : CastTyping env 0 (SourceCasts env) ctx (.const kind.first []) (.sort (.succ .zero)) := by
    cases kind
    · exact .constant library.scalars.natural (by simp) rfl
    · exact .constant library.returns.state (by simp) rfl
  have second : CastTyping env 0 (SourceCasts env) ((.const kind.first [])::ctx) (.const kind.second []) (.sort (.succ .zero)) := by
    cases kind
    · exact .constant library.returns.state (by simp) rfl
    · exact .constant library.scalars.natural (by simp) rfl
  have result : sourceResultType kind.mode = optionType kind.result := by cases kind <;> rfl
  rw [result] at bt
  exact ⟨_,kind.source_represents nr inputs.s.property (kind.lambda_represents br),
    NaturalLoop.source_typed library.naturalLoops library.scalars.toSignatures library.forHeader library.reads inputs kind
      (annotation.result nt) (.lambda first (.lambda second bt))⟩
end IRComparison.WordFrontend.FunctionSyntax

namespace IRComparison.WordFrontend.FunctionSyntax
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic StructuralBody StructuralSyntax
/-- A single nondependent binding proof covers both let and beta syntax.
The children supply source typing, including an opaque helper call, without
requiring a successful parse or its generated code. -/
theorem sourceCheckedLetTyping
    (domainRep : Represents nativeDomain domain)
    (domainTyped : CastTyping env 0 (SourceCasts env) ctx domain (.sort u))
    (resultClosed : result.ClosedN 0)
    (value : ∃ core, Represents v core ∧ CheckedTyping env 0 (SourceCasts env) ctx core domain)
    (body : ∃ core, Represents b core ∧ CastTyping env 0 (SourceCasts env) (domain::ctx) core result)
    (binder : Lean.Name) (flag : Bool) (info : Lean.BinderInfo) :
    ∃ core, Represents (.letE binder nativeDomain v b flag) core ∧
      Represents (.app (.lam binder nativeDomain b info) v) core ∧
      CastTyping env 0 (SourceCasts env) ctx core result := by
  obtain ⟨vc,vr,vt⟩ := value
  obtain ⟨bc,br,bt⟩ := body
  have typed := CastTyping.checkedApplication (.lambda domainTyped bt) vt
  rw [resultClosed.instN_eq (Nat.zero_le 0)] at typed
  exact ⟨_,.letE domainRep vr br,.app (.lam domainRep br) vr,typed⟩

/-- Let and beta spellings share source construction even when their body
contains an abstract locally bound helper. Actual Word/BV32 spelling is inferred. -/
theorem sourceBinderTyping (library : ScopedSyntax.Library env)
    (inputs : InputsTyped env ctx p) (scope : LexicalScalarCode.ScopeTyped env ctx p)
    (annotation : WordBinder.Annotation)
    (value : LexicalScalarSyntax.Form env ctx p [] v) (static : LexicalScalarSyntax.StaticRegisters v)
    (resultClosed : result.ClosedN 0)
    (body : ∃ core, Represents b core ∧ CastTyping env 0 (SourceCasts env) (annotation.core::ctx) core result)
    (binder : Lean.Name) (flag : Bool) (info : Lean.BinderInfo) :
    ∃ core, Represents (.letE binder annotation.native v b flag) core ∧
      Represents (.app (.lam binder annotation.native b info) v) core ∧
      CastTyping env 0 (SourceCasts env) ctx core result := by
  obtain ⟨vc,actual,vr,vt,_⟩ := value.evidence static library.scalars library.decisions inputs scope (by simp)
  simp only [LexicalScalarSyntax.expand_nil] at vr
  exact sourceCheckedLetTyping annotation.represented
    ((annotation.type_typed library.scalars.toSignatures).withCasts _)
    resultClosed ⟨vc,vr,annotation.argument (actual.result vt)⟩ body binder flag info

end IRComparison.WordFrontend.FunctionSyntax

namespace IRComparison.WordFrontend.FixedFunctionCompleteness
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic StructuralBody StructuralSyntax FunctionSyntax
set_option maxHeartbeats 2400000
end IRComparison.WordFrontend.FixedFunctionCompleteness

namespace IRComparison.WordFrontend.FixedFunctionCompleteness
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic StructuralBody StructuralSyntax FunctionSyntax
set_option maxHeartbeats 2400000

/-- A scalar actual is retained using the existing scalar source induction.
No generated command, core argument, type-conversion result or successful
parse is supplied. The endpoint body remains arbitrary retained Syntax. -/
theorem retainedScalarCallFromOpenBody {body functionBody : Lean.Expr}
    (setup : AliasSetup env) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (fresh : ScopedSyntax.Fresh setup) (exposure : Exposure env)
    (inputs : InputsTyped env ctx p) (locals : ScalarSyntax.Locals env ctx p)
    (typing : LexicalScalarCode.ScopeTyped env ctx p)
    (annotation : WordBinder.Annotation) (fn argument : Lean.Expr) (modeAllowed : mode ≠ .value)
    (coherent : scope.Coherent ctx.length σ)
    (binding : BindingValue scope ctx.length σ fn.getAppFn (.captured depth captured 1 body functions))
    (arguments : ((Lean.Expr.app fn argument).getAppArgs.toList.map σ.apply) = [actual])
    (value : LexicalScalarSyntax.Form env ctx p [] actual) (static : LexicalScalarSyntax.StaticRegisters actual)
    (notState : sameTerm actual p.s = false)
    (next : ∀ a : WordBinder.Annotation,
      Syntax env (mode := mode) (a.core::ctx)
        {p.lift with locals := .bvar 0::p.lift.locals}
        (closureSubstitution depth (a.core::ctx).length captured [.bvar 0])
        (functions.parameters 1) body requirements)
    (shape : LambdaSource (σ.apply fn.getAppFn) [annotation.native] functionBody) :
    Syntax env (mode := mode) ctx p σ scope (.app fn argument) requirements := by
  obtain ⟨native,code,quotation,source⟩ := FixedScalarCompleteness.Scoped.fromSyntax value static
  obtain ⟨core,a,represented,typed,form⟩ := source.evidence library.scalars library.decisions inputs typing
  have retainedArgs : ArgumentBindings.Syntax env ctx p [actual] [] (a.core::ctx)
      {p.lift with locals := .bvar 0::p.lift.locals} [.bvar 0] :=
    (ArgumentBindings.scalar source a represented typed notState .done).syntax
  have opened := binding.openedScalar coherent shape
  have bodyTyping (b : WordBinder.Annotation) : ∃ core, Represents functionBody core ∧
      CastTyping env 0 (SourceCasts env) (b.core::ctx) core (sourceResultType mode) := by
    obtain ⟨core,rep,typed⟩ := (next b).sourceTyping setup library closed fresh exposure
      (b.nextInputs inputs closed library.scalars.toSignatures library.cons)
      (b.nextLocals locals closed)
    exact ⟨core,by simpa only [List.length_cons,opened] using rep,typed⟩
  obtain ⟨bodyCore,bodyRep,bodyTyped⟩ := bodyTyping annotation
  obtain ⟨functionRep,_⟩ := lambdaSource_typed shape (.cons annotation.represented .nil) closed
    (fun d hd => by
      have same : d = annotation.core := by simpa using hd
      subst d
      exact ⟨_,(annotation.type_typed library.scalars.toSignatures).withCasts _⟩)
    bodyRep (by simpa using bodyTyped)
  have argsRep : List.Forall₂ Represents
      ((Lean.Expr.app fn argument).getAppArgs.toList.map σ.apply) [core] := by
    rw [arguments]; exact .cons represented .nil
  apply Syntax.retainedCallFromBodyTypes library closed fn argument modeAllowed coherent binding
    (by rw [arguments]; rfl) (arguments ▸ retainedArgs) (next a)
    (.cons typed .nil) (.cons (annotation.argument (a.result typed)) .nil) rfl ?_ ?_ argsRep functionRep
  · intro d member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨_,(annotation.type_typed library.scalars.toSignatures).withCasts _⟩
    · have same : d = a.core := List.mem_singleton.mp member
      subst d
      exact ⟨_,(a.type_typed library.scalars.toSignatures).withCasts _⟩
  · intro n hn
    have casesN : n = 0 ∨ n = 1 := by simp only [List.length_cons,List.length_nil] at hn; omega
    rcases casesN with rfl | rfl
    · exact bodyTyped
    · obtain ⟨core,rep,typed⟩ := bodyTyping a
      have same := rep.unique bodyRep
      subst core
      exact typed

/-- Compatibility wrapper: the former independent body family is no longer
needed. The retained open-body derivation supplies original lambda typing. -/
theorem retainedScalarCallFromSyntax {body functionBody : Lean.Expr} (setup : AliasSetup env) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (fresh : ScopedSyntax.Fresh setup) (exposure : Exposure env)
    (inputs : InputsTyped env ctx p) (locals : ScalarSyntax.Locals env ctx p)
    (typing : LexicalScalarCode.ScopeTyped env ctx p)
    (annotation : WordBinder.Annotation) (fn argument : Lean.Expr) (modeAllowed : mode ≠ .value)
    (coherent : scope.Coherent ctx.length σ)
    (binding : BindingValue scope ctx.length σ fn.getAppFn (.captured depth captured 1 body functions))
    (arguments : ((Lean.Expr.app fn argument).getAppArgs.toList.map σ.apply) = [actual])
    (value : LexicalScalarSyntax.Form env ctx p [] actual) (static : LexicalScalarSyntax.StaticRegisters actual)
    (notState : sameTerm actual p.s = false)
    (next : ∀ a : WordBinder.Annotation,
      Syntax env (mode := mode) (a.core::ctx)
        {p.lift with locals := .bvar 0::p.lift.locals}
        (closureSubstitution depth (a.core::ctx).length captured [.bvar 0])
        (functions.parameters 1) body requirements)
    (bodies : ∀ a : WordBinder.Annotation,
      Syntax env (mode := mode) (a.core::ctx)
        {p.lift with locals := .bvar 0::p.lift.locals}
        .identity bodyScope functionBody bodyRequirements)
    (shape : LambdaSource (σ.apply fn.getAppFn) [annotation.native] functionBody) :
    Syntax env (mode := mode) ctx p σ scope (.app fn argument) requirements := by
  exact retainedScalarCallFromOpenBody setup library closed fresh exposure inputs locals typing
    annotation fn argument modeAllowed coherent binding arguments value static notState next shape

end IRComparison.WordFrontend.FixedFunctionCompleteness

namespace IRComparison.WordFrontend.FixedFunctionCompleteness
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic StructuralBody StructuralSyntax FunctionSyntax
set_option maxHeartbeats 2400000
/-- Arbitrary State/scalar argument lists use the existing source-only type
and parameter-scope inductions. Intermediate argument cores, alias checks,
lambda types and all prefix input/local environments are conclusions, not
obligations of the call site. This does not assume successful analysis. -/
theorem retainedCallFromSourceScope {body functionBody : Lean.Expr} {domain : VExpr} {tailDomains : List VExpr}
    (setup : AliasSetup env) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (fresh : ScopedSyntax.Fresh setup) (exposure : Exposure env)
    (sourceInputs : InputsTyped env ctx p) (sourceLocals : ScalarSyntax.Locals env ctx p)
    (sourceScope : LexicalScalarCode.ScopeTyped env ctx p)
    (fn argument : Lean.Expr) (modeAllowed : mode ≠ .value)
    (coherent : scope.Coherent ctx.length σ)
    (binding : BindingValue scope ctx.length σ fn.getAppFn (.captured depth captured arity body functions))
    (length : ((Lean.Expr.app fn argument).getAppArgs.toList.map σ.apply).length = arity)
    (retainedArgs : ArgumentBindings.Syntax env ctx p
      ((Lean.Expr.app fn argument).getAppArgs.toList.map σ.apply) [] finalCtx finalInputs finalArgs)
    (next : Syntax env (mode := mode) finalCtx finalInputs
      (closureSubstitution depth finalCtx.length captured finalArgs)
      (functions.parameters finalArgs.length) body requirements)
    (argumentSyntax : List.Forall₂ (fun domain raw =>
      (domain = stateType ∧ raw = p.s) ∨
      ∃ annotation : WordBinder.Annotation, domain = annotation.core ∧
        LexicalScalarSyntax.Form env ctx p [] raw ∧ LexicalScalarSyntax.StaticRegisters raw)
      (domain::tailDomains) ((Lean.Expr.app fn argument).getAppArgs.toList.map σ.apply))
    (bodies : ∀ actual, List.Forall₂ (fun declared inferred =>
      (declared = stateType ∧ inferred = stateType) ∨
      ∃ a b : WordBinder.Annotation, declared = a.core ∧ inferred = b.core) (domain::tailDomains) actual →
      ∀ n, n ≤ (domain::tailDomains).length →
      Syntax env ((actual.take n ++ (domain::tailDomains).drop n).reverse ++ ctx)
        (parameterInputs (domain::tailDomains) p) .identity bodyScope functionBody bodyRequirements mode)
    (shape : LambdaSource (σ.apply fn.getAppFn) nativeDomains functionBody)
    (domainRep : List.Forall₂ Represents nativeDomains (domain::tailDomains)) :
    Syntax env (mode := mode) ctx p σ scope (.app fn argument) requirements := by
  obtain ⟨args,actual,argsRep,exactTypes,checks,declaredTyped,actualTyped,shapes⟩ :=
    argumentsWithShapesFromSyntax library sourceInputs sourceScope argumentSyntax
  have sameLength {xs ys : List VExpr} {R : VExpr → VExpr → Prop} (h : List.Forall₂ R xs ys) : xs.length = ys.length := by
    induction h with
    | nil => rfl
    | cons h hs ih => exact congrArg Nat.succ ih
  have len := sameLength checks
  have scopes (n : Nat) := parameterScope library closed sourceInputs sourceLocals sourceScope
    (actual.take n ++ (domain::tailDomains).drop n) (parameterTypes_prefix shapes n)
  cases checks with
  | cons firstCheck remainingChecks =>
    apply Syntax.retainedCallFromLambdaBodies setup library closed fresh exposure fn argument modeAllowed
      coherent binding length retainedArgs next exactTypes (.cons firstCheck remainingChecks) len
    · intro ty member
      rcases List.mem_append.mp member with member | member
      · exact ⟨_,declaredTyped ty member⟩
      · exact ⟨_,actualTyped ty member⟩
    · intro n hn; exact bodies actual shapes n (len.symm ▸ hn)
    · intro n hn
      exact Classical.choice (by simpa only [parameterInputs_prefix shapes n p] using (scopes n).1)
    · intro n hn
      exact Classical.choice (by simpa only [parameterInputs_prefix shapes n p] using (scopes n).2.1)
    · exact argsRep
    · exact shape
    · exact domainRep

end IRComparison.WordFrontend.FixedFunctionCompleteness

namespace IRComparison.WordFrontend.FixedFunctionCompleteness
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic StructuralBody StructuralSyntax FunctionSyntax
set_option maxHeartbeats 2400000

/-- A well-typed scalar cannot be the current State expression. Dispatch
separation follows from source typing, not from a per-call parser check. -/
theorem _root_.IRComparison.WordFrontend.LexicalScalarCode.Evidence.notState
    (value : LexicalScalarCode.Evidence env ctx raw) (inputs : InputsTyped env ctx p) :
    sameTerm raw p.s = false := by
  cases found : sameTerm raw p.s with
  | false => rfl
  | true =>
    obtain ⟨core,annotation,represented,typed,_⟩ := value
    have same := sameTerm_sound represented inputs.s.property found
    rw [same] at typed
    have impossible := typed.unique (inputs.hs.withCasts (SourceCasts env))
    cases annotation <;> simp [WordBinder.Annotation.core,wordType,bitvecType,stateType] at impossible

/-- Independent State/scalar source arguments give the classifications used
by the common retained-argument construction. State separation is derived. -/
theorem sourceArgumentCases
    (library : ScopedSyntax.Library env) (sourceInputs : InputsTyped env ctx p)
    (sourceScope : LexicalScalarCode.ScopeTyped env ctx p)
    {ds : List VExpr} {xs : List Lean.Expr}
      (h : List.Forall₂ (fun domain raw =>
        (domain = stateType ∧ raw = p.s) ∨
        ∃ annotation : WordBinder.Annotation, domain = annotation.core ∧
          LexicalScalarSyntax.Form env ctx p [] raw ∧ LexicalScalarSyntax.StaticRegisters raw) ds xs) :
      ∀ raw ∈ xs, raw = p.s ∨
        (∃ core, Represents raw core ∧ CastTyping env 0 (SourceCasts env) ctx core UnitStep.unitType) ∨
        (LexicalScalarSyntax.Form env ctx p [] raw ∧ LexicalScalarSyntax.StaticRegisters raw ∧ sameTerm raw p.s = false) := by
    induction h with
    | nil => simp
    | cons head tail ih =>
      intro raw member
      rcases List.mem_cons.mp member with rfl | member
      · rcases head with ⟨_,current⟩ | ⟨a,_,form,static⟩
        · exact Or.inl current
        · have evidence := form.evidence static library.scalars library.decisions sourceInputs sourceScope (by simp)
          exact Or.inr (Or.inr ⟨form,static,by
            simpa only [LexicalScalarSyntax.expand_nil] using evidence.notState sourceInputs⟩)
      · exact ih raw member

/-- Source argument syntax constructs the whole retained telescope before
entering the existing arbitrary-body call rule. The body construction receives
the endpoint's derived scope and typing invariants; no generated code or
successful compiler check is assumed. -/
theorem retainedCallFromSourceArguments {body functionBody : Lean.Expr} {domain : VExpr} {tailDomains : List VExpr}
    (setup : AliasSetup env) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (fresh : ScopedSyntax.Fresh setup) (exposure : Exposure env)
    (sourceInputs : InputsTyped env ctx p) (sourceLocals : ScalarSyntax.Locals env ctx p)
    (sourceScope : LexicalScalarCode.ScopeTyped env ctx p) (references : ScalarSyntax.ReferenceScope p)
    (fn argument : Lean.Expr) (modeAllowed : mode ≠ .value)
    (coherent : scope.Coherent ctx.length σ)
    (binding : BindingValue scope ctx.length σ fn.getAppFn (.captured depth captured arity body functions))
    (length : ((Lean.Expr.app fn argument).getAppArgs.toList.map σ.apply).length = arity)
    (argumentSyntax : List.Forall₂ (fun domain raw =>
      (domain = stateType ∧ raw = p.s) ∨
      ∃ annotation : WordBinder.Annotation, domain = annotation.core ∧
        LexicalScalarSyntax.Form env ctx p [] raw ∧ LexicalScalarSyntax.StaticRegisters raw)
      (domain::tailDomains) ((Lean.Expr.app fn argument).getAppArgs.toList.map σ.apply))
    (next : ∀ finalCtx finalInputs finalArgs,
      ArgumentBindings.Syntax env ctx p ((Lean.Expr.app fn argument).getAppArgs.toList.map σ.apply)
        [] finalCtx finalInputs finalArgs →
      InputsTyped env finalCtx finalInputs → ScalarSyntax.Locals env finalCtx finalInputs →
      LexicalScalarCode.ScopeTyped env finalCtx finalInputs → ScalarSyntax.ReferenceScope finalInputs →
      Syntax env (mode := mode) finalCtx finalInputs
        (closureSubstitution depth finalCtx.length captured finalArgs)
        (functions.parameters finalArgs.length) body requirements)
    (bodies : ∀ actual, List.Forall₂ (fun declared inferred =>
      (declared = stateType ∧ inferred = stateType) ∨
      ∃ a b : WordBinder.Annotation, declared = a.core ∧ inferred = b.core) (domain::tailDomains) actual →
      ∀ n, n ≤ (domain::tailDomains).length →
      Syntax env ((actual.take n ++ (domain::tailDomains).drop n).reverse ++ ctx)
        (parameterInputs (domain::tailDomains) p) .identity bodyScope functionBody bodyRequirements mode)
    (shape : LambdaSource (σ.apply fn.getAppFn) nativeDomains functionBody)
    (domainRep : List.Forall₂ Represents nativeDomains (domain::tailDomains)) :
    Syntax env (mode := mode) ctx p σ scope (.app fn argument) requirements := by
  have sourceArgs := sourceArgumentCases library sourceInputs sourceScope argumentSyntax
  obtain ⟨fc,fp,fa,sw,nw,cw,qw,args⟩ := ArgumentBindings.fromSyntax library closed sourceInputs sourceScope references sourceArgs []
  obtain ⟨⟨fi⟩,⟨fl⟩⟩ := args.endpointInputs library closed sourceInputs sourceLocals
  obtain ⟨ft,fr⟩ := args.endpointScope closed sourceScope references
  exact retainedCallFromSourceScope setup library closed fresh exposure sourceInputs sourceLocals sourceScope
    fn argument modeAllowed coherent binding length args.syntax (next fc fp fa args.syntax fi fl ft fr)
    argumentSyntax bodies shape domainRep

end IRComparison.WordFrontend.FixedFunctionCompleteness

namespace IRComparison.WordFrontend.FixedFunctionCompleteness
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic StructuralBody StructuralSyntax FunctionSyntax
set_option maxHeartbeats 3200000

private theorem scalarShapeAnnotations (declared : List WordBinder.Annotation)
    (shapes : List.Forall₂ (fun declared inferred =>
      (declared = stateType ∧ inferred = stateType) ∨
      ∃ a b : WordBinder.Annotation, declared = a.core ∧ inferred = b.core)
      (declared.map WordBinder.Annotation.core) actual) :
    ∃ inferred : List WordBinder.Annotation, actual = inferred.map WordBinder.Annotation.core ∧ inferred.length = declared.length := by
  induction declared generalizing actual with
  | nil => cases shapes; exact ⟨[],rfl,rfl⟩
  | cons a rest ih =>
    cases shapes with
    | cons head tail =>
      rcases head with ⟨bad,_⟩ | ⟨da,b,_,rfl⟩
      · exact False.elim (FunctionSyntax.annotation_not_state a bad)
      · obtain ⟨bs,rfl,count⟩ := ih tail
        exact ⟨b::bs,rfl,congrArg Nat.succ count⟩


end IRComparison.WordFrontend.FixedFunctionCompleteness

namespace IRComparison.WordFrontend.FunctionSyntax
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic StructuralBody StructuralSyntax
set_option maxHeartbeats 3200000

private theorem parameterType_closed
    (allowed : domain = stateType ∨ ∃ a : WordBinder.Annotation, domain = a.core) : domain.ClosedN 0 := by
  rcases allowed with rfl | ⟨a,rfl⟩
  · trivial
  · exact a.closed

/-- Typed source arguments retain their types when a scalar slot is added.
The relation contains source expressions and their types, not parsed code. -/
theorem argumentTypes_lift
    (closed : ClosedConstantTypes env)
    (typed : List.Forall₂ (fun domain raw => ∃ core, Represents raw core ∧
      CastTyping env 0 (SourceCasts env) ctx core domain) domains actuals)
    (allowed : ∀ domain ∈ domains, domain = stateType ∨ ∃ a : WordBinder.Annotation, domain = a.core)
    (binder : VExpr) :
    List.Forall₂ (fun domain raw => ∃ core, Represents raw core ∧
      CastTyping env 0 (SourceCasts env) (binder::ctx) core domain)
      domains (actuals.map (LeanBindings.rename Nat.succ)) := by
  induction typed with
  | nil => exact .nil
  | @cons domain raw domains actuals head tail ih =>
    obtain ⟨core,rep,typed⟩ := head
    refine .cons ⟨_,rep.lift,?_⟩ (ih (fun d hd => allowed d (List.mem_cons_of_mem _ hd)))
    simpa only [(parameterType_closed (allowed domain List.mem_cons_self)).lift_eq] using
      typed.lift closed SourceCasts.closed binder

/-- Derive the endpoint of an arbitrary mixed State/scalar argument telescope
from the independently inferred argument types. No fixed arity is inspected. -/
theorem _root_.IRComparison.WordFrontend.StructuralBody.ArgumentBindings.parameterLayout
    (arguments : ArgumentBindings (env := env) ctx p actuals saved fc fp fa sw nw cw qw)
    (library : ScopedSyntax.Library env) (closed : ClosedConstantTypes env)
    (inputs : InputsTyped env ctx p)
    (typed : List.Forall₂ (fun domain raw => ∃ core, Represents raw core ∧
      CastTyping env 0 (SourceCasts env) ctx core domain) domains actuals)
    (allowed : ∀ domain ∈ domains, domain = stateType ∨ ∃ a : WordBinder.Annotation, domain = a.core) :
    FunctionSyntax.parameterLayout false domains ctx p saved = (fc,fp,fa) := by
  induction arguments generalizing domains with
  | done => cases typed; rfl
  | state current next ih =>
    cases typed with
    | cons head tail =>
      obtain ⟨core,rep,typed⟩ := head
      rw [current] at rep
      have same := rep.unique inputs.s.property
      rw [same] at typed
      have domainEq := typed.unique (inputs.hs.withCasts (SourceCasts env))
      subst domainEq
      simpa only [FunctionSyntax.parameterLayout_state,Bool.false_eq_true,ite_false,current] using
        ih inputs tail (fun d hd => allowed d (List.mem_cons_of_mem _ hd))
  | unit rep unitTyped next ih =>
    cases typed with
    | cons head tail =>
      obtain ⟨core,other,typed⟩ := head
      have same := other.unique rep
      rw [same] at typed
      have impossible := typed.unique unitTyped
      rcases allowed _ List.mem_cons_self with rfl | ⟨a,rfl⟩
      · simp [stateType,UnitStep.unitType] at impossible
      · cases a <;> simp [WordBinder.Annotation.core,wordType,bitvecType,UnitStep.unitType] at impossible
  | scalar source a rep scalarTyped apart next ih =>
    cases typed with
    | cons head tail =>
      obtain ⟨core,other,typed⟩ := head
      have same := other.unique rep
      rw [same] at typed
      have domainEq := typed.unique scalarTyped
      subst domainEq
      have remaining := fun d hd => allowed d (List.mem_cons_of_mem _ hd)
      simpa only [FunctionSyntax.parameterLayout_scalar] using
        ih (a.nextInputs inputs closed library.scalars.toSignatures library.cons)
          (argumentTypes_lift closed tail remaining a.core) remaining

/-- Every intermediate Word/BV32 spelling is a source signature of the same
shape. This supplies all original partial-application bodies from one family. -/
theorem parameterShapes_prefix
    (shapes : List.Forall₂ (fun declared inferred =>
      (declared = stateType ∧ inferred = stateType) ∨
      ∃ a b : WordBinder.Annotation, declared = a.core ∧ inferred = b.core) domains actual) (n : Nat) :
    List.Forall₂ (fun declared inferred =>
      (declared = stateType ∧ inferred = stateType) ∨
      ∃ a b : WordBinder.Annotation, declared = a.core ∧ inferred = b.core)
      domains (actual.take n ++ domains.drop n) := by
  have self : List.Forall₂ (fun declared inferred =>
      (declared = stateType ∧ inferred = stateType) ∨
      ∃ a b : WordBinder.Annotation, declared = a.core ∧ inferred = b.core) domains domains := by
    induction shapes with
    | nil => exact .nil
    | cons head tail ih =>
      rcases head with ⟨rfl,_⟩ | ⟨a,b,rfl,_⟩
      · exact .cons (Or.inl ⟨rfl,rfl⟩) ih
      · exact .cons (Or.inr ⟨a,a,rfl,rfl⟩) ih
  induction shapes generalizing n with
  | nil => simpa using (List.Forall₂.nil : List.Forall₂ _ [] [])
  | cons head tail ih =>
    cases n with
    | zero => simpa using self
    | succ n =>
      cases self with
      | cons _ next => exact .cons head (ih n next)

end IRComparison.WordFrontend.FunctionSyntax

namespace IRComparison.WordFrontend.FunctionSyntax
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic StructuralBody StructuralSyntax

/-- Scalars occupy the same positions in the lambda and retained contexts. -/
theorem parameterLayout_scalars (openStates : Bool) (annotations : List WordBinder.Annotation)
    (ctx : List VExpr) (p : Inputs) (saved : List Lean.Expr) :
    parameterLayout openStates (annotations.map WordBinder.Annotation.core) ctx p saved =
      ((annotations.map WordBinder.Annotation.core).reverse ++ ctx,
        parameterInputs (annotations.map WordBinder.Annotation.core) p,openArguments annotations.length saved) := by
  induction annotations generalizing ctx p saved with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.map_cons,parameterLayout_scalar,ih,parameterInputs_scalar,
      List.reverse_cons,List.append_assoc,List.singleton_append,List.length_cons,openArguments]

/-- When every actual is a scalar, the existing general telescope has exactly
one source parameter slot per actual. This is a derived layout property,
not a restriction on the general argument builder or on mixed calls. -/
theorem _root_.IRComparison.WordFrontend.StructuralBody.ArgumentBindings.scalarLayout
    (arguments : ArgumentBindings (env := env) ctx p actuals saved fc fp fa sw nw cw qw)
    (setup : AliasSetup env) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (exposure : Exposure env) (inputs : InputsTyped env ctx p)
    (values : ∀ raw ∈ actuals, LexicalScalarCode.Evidence env ctx raw ∧ sameTerm raw p.s = false) :
    ∃ annotations : List WordBinder.Annotation,
      fc = (annotations.map WordBinder.Annotation.core).reverse ++ ctx ∧
      fp = parameterInputs (annotations.map WordBinder.Annotation.core) p ∧
      fa = openArguments annotations.length saved ∧ annotations.length = actuals.length := by
  have choose {xs : List Lean.Expr} (values : ∀ raw ∈ xs, LexicalScalarCode.Evidence env ctx raw) :
      ∃ annotations : List WordBinder.Annotation,
        List.Forall₂ (fun domain raw => ∃ core, Represents raw core ∧
          CastTyping env 0 (SourceCasts env) ctx core domain)
          (annotations.map WordBinder.Annotation.core) xs := by
    induction xs with
    | nil => exact ⟨[],.nil⟩
    | cons raw rest ih =>
      obtain ⟨core,a,rep,typed,_⟩ := values raw List.mem_cons_self
      obtain ⟨annotations,tail⟩ := ih (fun r hr => values r (List.mem_cons_of_mem _ hr))
      exact ⟨a::annotations,.cons ⟨core,rep,typed⟩ tail⟩
  obtain ⟨annotations,typed⟩ := choose (fun raw member => (values raw member).1)
  have layout := arguments.parameterLayout library closed inputs typed (by
    intro d member
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp member
    exact Or.inr ⟨a,rfl⟩)
  rw [parameterLayout_scalars] at layout
  obtain ⟨hc,rest⟩ := Prod.mk.inj layout
  exact ⟨annotations,hc.symm,(congrArg Prod.fst rest).symm,(congrArg Prod.snd rest).symm,
    by simpa only [List.length_map] using List.Forall₂.length_eq typed⟩

/-- Reuse the represented argument list and its inferred types; no second
inference of the source expressions is required to determine their layout. -/
theorem argumentTypes_of_representations
    (represented : List.Forall₂ Represents raws cores)
    (typed : List.Forall₂ (fun domain core => CastTyping env 0 (SourceCasts env) ctx core domain) domains cores) :
    List.Forall₂ (fun domain raw => ∃ core, Represents raw core ∧
      CastTyping env 0 (SourceCasts env) ctx core domain) domains raws := by
  induction represented generalizing domains with
  | nil => cases typed; exact .nil
  | cons rep tail ih =>
    cases typed with
    | cons first rest => exact .cons ⟨_,rep,first⟩ (ih rest)

end IRComparison.WordFrontend.FunctionSyntax

namespace IRComparison.WordFrontend.FixedFunctionCompleteness
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic StructuralBody StructuralSyntax FunctionSyntax
set_option maxHeartbeats 3200000

/-- A single body family over the two existing parameter placements supplies
original lambda typing and retained-call syntax for arbitrary mixed
State/scalar arguments. The family describes source bindings, not parsing or
generated code; subsequent body constructors are the existing Syntax rules. -/
theorem retainedArgumentsFromBodyFamily {body functionBody : Lean.Expr} {domain : VExpr} {tailDomains : List VExpr}
    (setup : AliasSetup env) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (fresh : ScopedSyntax.Fresh setup) (exposure : Exposure env)
    (sourceInputs : InputsTyped env ctx p) (sourceLocals : ScalarSyntax.Locals env ctx p)
    (sourceScope : LexicalScalarCode.ScopeTyped env ctx p) (references : ScalarSyntax.ReferenceScope p)
    (fn argument : Lean.Expr) (modeAllowed : mode ≠ .value)
    (coherent : scope.Coherent ctx.length σ)
    (binding : BindingValue scope ctx.length σ fn.getAppFn (.captured depth captured arity body functions))
    (length : ((Lean.Expr.app fn argument).getAppArgs.toList.map σ.apply).length = arity)
    (argumentSyntax : List.Forall₂ (fun domain raw =>
      (domain = stateType ∧ raw = p.s) ∨
      ∃ annotation : WordBinder.Annotation, domain = annotation.core ∧
        LexicalScalarSyntax.Form env ctx p [] raw ∧ LexicalScalarSyntax.StaticRegisters raw)
      (domain::tailDomains) ((Lean.Expr.app fn argument).getAppArgs.toList.map σ.apply))
    (bodies : ∀ actual, List.Forall₂ (fun declared inferred =>
      (declared = stateType ∧ inferred = stateType) ∨
      ∃ a b : WordBinder.Annotation, declared = a.core ∧ inferred = b.core) (domain::tailDomains) actual →
      ∀ openStates : Bool,
      let frame := parameterLayout openStates actual ctx p []
      InputsTyped env frame.1 frame.2.1 → ScalarSyntax.Locals env frame.1 frame.2.1 →
      LexicalScalarCode.ScopeTyped env frame.1 frame.2.1 → ScalarSyntax.ReferenceScope frame.2.1 →
      Syntax env (mode := mode) frame.1 frame.2.1
        (closureSubstitution depth frame.1.length captured frame.2.2)
        (functions.parameters frame.2.2.length) body requirements)
    (shape : LambdaSource (σ.apply fn.getAppFn) nativeDomains functionBody)
    (domainRep : List.Forall₂ Represents nativeDomains (domain::tailDomains)) :
    Syntax env (mode := mode) ctx p σ scope (.app fn argument) requirements := by
  obtain ⟨args,actual,argsRep,exactTypes,checks,declaredTyped,actualTyped,shapes⟩ :=
    argumentsWithShapesFromSyntax library sourceInputs sourceScope argumentSyntax
  have signatureLength : (domain::tailDomains).length = arity :=
    (List.Forall₂.length_eq argumentSyntax).trans length
  have allowedActual : ∀ d ∈ actual, d = stateType ∨ ∃ a : WordBinder.Annotation, d = a.core := by
    have all := parameterTypes_prefix shapes actual.length
    have drop : (domain::tailDomains).drop actual.length = [] := List.drop_eq_nil_of_le (by
      have := List.Forall₂.length_eq shapes; omega)
    simpa only [List.take_length,drop,List.append_nil] using all
  obtain ⟨fc,fp,fa,sw,nw,cw,qw,retained⟩ := ArgumentBindings.fromSyntax library closed sourceInputs sourceScope references
    (sourceArgumentCases library sourceInputs sourceScope argumentSyntax) []
  have frame := retained.parameterLayout library closed sourceInputs
    (argumentTypes_of_representations argsRep exactTypes) allowedActual
  obtain ⟨⟨fi⟩,⟨fl⟩,ft,fr⟩ := parameterLayout_scope library closed sourceInputs sourceLocals sourceScope actual allowedActual false []
  have next := bodies actual shapes false fi fl ft (fr references)
  rw [frame] at next
  have opened := binding.openedArguments coherent shape ((List.Forall₂.length_eq domainRep).trans signatureLength)
  have openedAt : (closureSubstitution depth (arity+ctx.length) captured (openArguments arity [])).apply body = functionBody := by
    rw [Nat.add_comm arity ctx.length]
    exact opened
  have bodyTyping (as : List VExpr) (shapeTypes : List.Forall₂ (fun declared inferred =>
      (declared = stateType ∧ inferred = stateType) ∨
      ∃ a b : WordBinder.Annotation, declared = a.core ∧ inferred = b.core) (domain::tailDomains) as) :
      ∃ core, Represents functionBody core ∧
        CastTyping env 0 (SourceCasts env) (as.reverse ++ ctx) core (sourceResultType mode) := by
    have allowed : ∀ d ∈ as, d = stateType ∨ ∃ a : WordBinder.Annotation, d = a.core := by
      have all := parameterTypes_prefix shapeTypes as.length
      have drop : (domain::tailDomains).drop as.length = [] := List.drop_eq_nil_of_le (by
        have := List.Forall₂.length_eq shapeTypes; omega)
      simpa only [List.take_length,drop,List.append_nil] using all
    obtain ⟨⟨inputs⟩,⟨locals⟩,typing,reference⟩ :=
      parameterLayout_scope library closed sourceInputs sourceLocals sourceScope as allowed true []
    have source := bodies as shapeTypes true inputs locals typing (reference references)
    simp only [parameterLayout_open] at source inputs locals
    obtain ⟨core,rep,typed⟩ := source.sourceTyping setup library closed fresh exposure inputs locals
    have count : as.length = arity := (List.Forall₂.length_eq shapeTypes).symm.trans signatureLength
    refine ⟨core,?_,typed⟩
    simpa only [List.length_append,List.length_reverse,count,openedAt] using rep
  have self := parameterShapes_prefix shapes 0
  simp only [List.take_zero,List.drop_zero,List.nil_append] at self
  obtain ⟨coreBody,bodyRep,initialTyped⟩ := bodyTyping (domain::tailDomains) self
  obtain ⟨functionRep,_⟩ := lambdaSource_typed shape domainRep closed
    (fun d member => ⟨_,declaredTyped d member⟩) bodyRep initialTyped
  have argsCount := List.Forall₂.length_eq checks
  cases args with
  | nil => cases checks
  | cons first rest =>
    apply Syntax.retainedCallFromBodyTypes library closed fn argument modeAllowed coherent binding length
      retained.syntax next exactTypes checks argsCount
      (fun d member => by
        rcases List.mem_append.mp member with member | member
        · exact ⟨_,declaredTyped d member⟩
        · exact ⟨_,actualTyped d member⟩) ?_ argsRep functionRep
    intro n hn
    obtain ⟨core,rep,typed⟩ := bodyTyping _ (parameterShapes_prefix shapes n)
    have same := rep.unique bodyRep
    subst core
    exact typed

end IRComparison.WordFrontend.FixedFunctionCompleteness

namespace IRComparison.WordFrontend.FixedFunctionCompleteness
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic StructuralBody StructuralSyntax FunctionSyntax
set_option maxHeartbeats 3200000

/-- One arbitrary helper-body syntax family supplies both the retained body
and every original partial-application type, at any scalar arity. Captured
State, reads, branches, loops and nested helpers remain ordinary body syntax.
Mixed State/scalar formal lists continue through the existing general rule. -/
theorem retainedScalarArgumentsFromOpenBody {body functionBody : Lean.Expr}
    (setup : AliasSetup env) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (fresh : ScopedSyntax.Fresh setup) (exposure : Exposure env)
    (sourceInputs : InputsTyped env ctx p) (sourceLocals : ScalarSyntax.Locals env ctx p)
    (sourceScope : LexicalScalarCode.ScopeTyped env ctx p) (references : ScalarSyntax.ReferenceScope p)
    (declaredHead : WordBinder.Annotation) (declaredTail : List WordBinder.Annotation)
    (fn argument : Lean.Expr) (modeAllowed : mode ≠ .value)
    (coherent : scope.Coherent ctx.length σ)
    (binding : BindingValue scope ctx.length σ fn.getAppFn
      (.captured depth captured (declaredHead::declaredTail).length body functions))
    (length : ((Lean.Expr.app fn argument).getAppArgs.toList.map σ.apply).length = (declaredHead::declaredTail).length)
    (values : ∀ raw ∈ ((Lean.Expr.app fn argument).getAppArgs.toList.map σ.apply),
      LexicalScalarSyntax.Form env ctx p [] raw ∧ LexicalScalarSyntax.StaticRegisters raw)
    (bodies : ∀ annotations : List WordBinder.Annotation, annotations.length = (declaredHead::declaredTail).length →
      Syntax env (mode := mode)
        ((annotations.map WordBinder.Annotation.core).reverse ++ ctx)
        (parameterInputs (annotations.map WordBinder.Annotation.core) p)
        (closureSubstitution depth ((annotations.map WordBinder.Annotation.core).reverse ++ ctx).length captured
          (openArguments annotations.length []))
        (functions.parameters annotations.length) body requirements)
    (shape : LambdaSource (σ.apply fn.getAppFn) ((declaredHead::declaredTail).map WordBinder.Annotation.native) functionBody) :
    Syntax env (mode := mode) ctx p σ scope (.app fn argument) requirements := by
  apply retainedArgumentsFromBodyFamily setup library closed fresh exposure sourceInputs sourceLocals
    sourceScope references fn argument modeAllowed coherent binding length
    (domain := declaredHead.core) (tailDomains := declaredTail.map WordBinder.Annotation.core)
    (nativeDomains := (declaredHead::declaredTail).map WordBinder.Annotation.native)
    (functionBody := functionBody)
  · have build {xs : List Lean.Expr} (as : List WordBinder.Annotation)
        (count : xs.length = as.length)
        (source : ∀ raw ∈ xs, LexicalScalarSyntax.Form env ctx p [] raw ∧ LexicalScalarSyntax.StaticRegisters raw) :
        List.Forall₂ (fun domain raw => (domain = stateType ∧ raw = p.s) ∨
          ∃ a : WordBinder.Annotation, domain = a.core ∧ LexicalScalarSyntax.Form env ctx p [] raw ∧ LexicalScalarSyntax.StaticRegisters raw)
          (as.map WordBinder.Annotation.core) xs := by
      induction as generalizing xs with
      | nil => cases xs with
        | nil => exact .nil
        | cons => simp at count
      | cons a rest ih => cases xs with
        | nil => simp at count
        | cons raw xs =>
          have h := source raw List.mem_cons_self
          exact .cons (Or.inr ⟨a,rfl,h.1,h.2⟩)
            (ih (by simpa using count) (fun r hr => source r (List.mem_cons_of_mem _ hr)))
    exact build (declaredHead::declaredTail) length values
  · intro actual shapes openStates
    dsimp only
    intro _ _ _ _
    obtain ⟨annotations,rfl,count⟩ := scalarShapeAnnotations (declaredHead::declaredTail) shapes
    simpa only [parameterLayout_scalars,openArguments_length,List.length_nil,Nat.zero_add] using bodies annotations count
  · exact shape
  · have build (as : List WordBinder.Annotation) : List.Forall₂ Represents (as.map WordBinder.Annotation.native)
        (as.map WordBinder.Annotation.core) := by
      induction as with
      | nil => exact .nil
      | cons a rest ih => exact .cons a.represented ih
    exact build _

end IRComparison.WordFrontend.FixedFunctionCompleteness

namespace IRComparison.WordFrontend.FunctionSyntax
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic StructuralBody StructuralSyntax
set_option maxHeartbeats 2400000

/-- Read bindings keep their actual Word/BitVec annotation. Only source forms
and typing of the continuation are inputs; read parsing and its checked
Option conversion are derived by the existing read completeness proof. -/
theorem sourceReadBindTyping {body : Lean.Expr} (setup : AliasSetup env) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (fresh : ScopedSyntax.Fresh setup) (exposure : Exposure env)
    (inputs : InputsTyped env ctx p) (locals : ScalarSyntax.Locals env ctx p)
    (annotation : WordBinder.Annotation) (read : ScopedSyntax.ReadForm env ctx p first)
    (resultRep : Represents nativeResult result)
    (resultTyped : DirectTyping env 0 ctx result (.sort (.succ .zero))) (resultClosed : result.ClosedN 0)
    (next : ∃ core, Represents body core ∧
      CastTyping env 0 (SourceCasts env) (annotation.core::ctx) core (optionType result))
    (binder : Lean.Name) (info : Lean.BinderInfo) :
    ∃ core, Represents (Lean.mkApp2 (bindHead annotation.native nativeResult) first
      (.lam binder annotation.native body info)) core ∧
      CastTyping env 0 (SourceCasts env) ctx core (optionType result) := by
  obtain ⟨piece,success,⟨typed⟩⟩ := ScopedSyntax.read_complete setup library closed fresh exposure inputs locals read
  apply sourceCheckedBindTyping library annotation.represented resultRep
    (annotation.type_typed library.scalars.toSignatures) resultTyped annotation.closed resultClosed
    (next := next) (binder := binder) (info := info)
  refine ⟨typed.sourceCore.val,typed.sourceCore.property,?_⟩
  cases annotation with
  | word => exact typed.value
  | bitvec => exact WordBinder.checked_option_bitvec library.returns.option typed.value

/-- Primitive State updates supply both sides of a paired continuation from
scalar source forms, with original typing derived rather than supplied. -/
theorem Syntax.valueAssignPaired {τ : Substitution}
    (setup : AliasSetup env) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (fresh : ScopedSyntax.Fresh setup) (exposure : Exposure env)
    (inputs : InputsTyped env originalCtx originalInputs) (locals : ScalarSyntax.Locals env originalCtx originalInputs)
    (register : Nat) (rn : NatNotation)
    (current : σ.apply st = p.s) (originalCurrent : τ.apply st = originalInputs.s)
    (value : LexicalScalarSyntax.Form env ctx p [] (σ.apply v) ∧
      LexicalScalarSyntax.Form env originalCtx originalInputs [] (τ.apply v))
    (checked : requirements (σ.apply (app ``HybridWord.State.set [st,rn.native register,v]))) :
    Syntax env (mode := .value) ctx p σ scope
      (app ``HybridWord.State.set [st,rn.native register,v]) requirements ∧
      ∃ core, Represents (τ.apply (app ``HybridWord.State.set [st,rn.native register,v])) core ∧
        CastTyping env 0 (SourceCasts env) originalCtx core stateType := by
  have original : Syntax env (mode := .value) originalCtx originalInputs τ .empty
      (app ``HybridWord.State.set [st,rn.native register,v]) :=
    .valueAssign register rn originalCurrent value.2
  exact ⟨.valueAssign register rn current value.1 checked,
    original.sourceTyping setup library closed fresh exposure inputs locals⟩

/-- Build the current body and its open source typing together.
The two contexts may differ because a function-let is substituted in one
and still an opaque variable in the other. No new syntax judgment is added.
State/read bindings and larger continuations can compose these paired rules. -/
theorem Syntax.stateLetPaired (library : ScopedSyntax.Library env)
    (mode : Mode) (notValue : mode ≠ .value)
    (value : Syntax env (mode := .value) ctx p σ scope v requirements ∧
      ∃ core, Represents (τ.apply v) core ∧ CastTyping env 0 (SourceCasts env) originalCtx core stateType)
    (next : Syntax env (mode := mode) (stateType::ctx)
        {p.lift with s := .bvar 0} (under σ) (.push none scope) b requirements ∧
      ∃ core, Represents ((under τ).apply b) core ∧
        CastTyping env 0 (SourceCasts env) (stateType::originalCtx) core (sourceResultType mode))
    (notAlias : sameTerm (σ.apply v) p.s = false) (binder : Lean.Name) (flag : Bool) :
    Syntax env (mode := mode) ctx p σ scope (StateLet.source binder v b flag) requirements ∧
      ∃ core, Represents (τ.apply (StateLet.source binder v b flag)) core ∧
        CastTyping env 0 (SourceCasts env) originalCtx core (sourceResultType mode) := by
  obtain ⟨vc,vr,vt⟩ := value.2
  obtain ⟨core,rep,_,typed⟩ := sourceCheckedLetTyping (nativeDomain := state) (domain := stateType) (.constant rfl)
    (.constant library.returns.state (by simp) rfl)
    (show (sourceResultType mode).ClosedN 0 by cases mode <;> trivial)
    ⟨vc,vr,.exact vt⟩ next.2 binder flag .default
  refine ⟨?_,core,?_,typed⟩
  · cases mode with
    | body => exact .stateLet value.1 next.1 notAlias binder flag
    | step => exact .stepStateLet value.1 next.1 notAlias binder flag
    | value => exact False.elim (notValue rfl)
  · simpa only [StateLet.source,StructuralStep.Alias.substitute_latest_let] using rep

/-- A do-read builds the continuation's retained syntax and original typing
in one composition; callers do not reassemble two enclosing body trees. -/
theorem Syntax.bindValuePaired (setup : AliasSetup env) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (fresh : ScopedSyntax.Fresh setup) (exposure : Exposure env)
    (inputs : InputsTyped env originalCtx originalInputs) (locals : ScalarSyntax.Locals env originalCtx originalInputs)
    (annotation : WordBinder.Annotation)
    (read : ScopedSyntax.ReadForm env ctx p (σ.apply v) ∧
      ScopedSyntax.ReadForm env originalCtx originalInputs (τ.apply v))
    (next : Syntax env (annotation.core::ctx)
        {p.lift with locals := .bvar 0::p.lift.locals} (under σ) (.push none scope) b requirements ∧
      ∃ core, Represents ((under τ).apply b) core ∧
        CastTyping env 0 (SourceCasts env) (annotation.core::originalCtx) core (optionType stateType))
    (binder : Lean.Name) (info : Lean.BinderInfo)
    (checked : requirements (σ.apply (WordBinder.readSource annotation v (.lam binder annotation.native b info)))) :
    Syntax env ctx p σ scope
      (WordBinder.readSource annotation v (.lam binder annotation.native b info)) requirements ∧
      ∃ core, Represents (τ.apply (WordBinder.readSource annotation v (.lam binder annotation.native b info))) core ∧
        CastTyping env 0 (SourceCasts env) originalCtx core (optionType stateType) := by
  obtain ⟨core,rep,typed⟩ := sourceReadBindTyping setup library closed fresh exposure inputs locals annotation read.2 (nativeResult := state) (result := stateType)
    (.constant rfl) (.constant library.returns.state (by simp) rfl) (by trivial) next.2 binder info
  exact ⟨.bindValue annotation read.1 next.1 binder info checked,core,
    by rw [WordBinder.substitute_readSource]; exact rep,typed⟩

/-- The same read typing proof is used inside a loop step. -/
theorem Syntax.stepBindValuePaired (setup : AliasSetup env) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (fresh : ScopedSyntax.Fresh setup) (exposure : Exposure env)
    (inputs : InputsTyped env originalCtx originalInputs) (locals : ScalarSyntax.Locals env originalCtx originalInputs)
    (annotation : WordBinder.Annotation)
    (read : ScopedSyntax.ReadForm env ctx p (σ.apply v) ∧
      ScopedSyntax.ReadForm env originalCtx originalInputs (τ.apply v))
    (next : Syntax env (mode := .step) (annotation.core::ctx)
        {p.lift with locals := .bvar 0::p.lift.locals} (under σ) (.push none scope) b requirements ∧
      ∃ core, Represents ((under τ).apply b) core ∧
        CastTyping env 0 (SourceCasts env) (annotation.core::originalCtx) core (optionType Step.stepState))
    (binder : Lean.Name) (info : Lean.BinderInfo)
    (checked : requirements (σ.apply (WordBinder.stepReadSource annotation v (.lam binder annotation.native b info)))) :
    Syntax env (mode := .step) ctx p σ scope
      (WordBinder.stepReadSource annotation v (.lam binder annotation.native b info)) requirements ∧
      ∃ core, Represents (τ.apply (WordBinder.stepReadSource annotation v (.lam binder annotation.native b info))) core ∧
        CastTyping env 0 (SourceCasts env) originalCtx core (optionType Step.stepState) := by
  obtain ⟨core,rep,typed⟩ := sourceReadBindTyping setup library closed fresh exposure inputs locals annotation read.2 (nativeResult := stepType) (result := Step.stepState)
    (.app (.constant rfl) (.constant rfl)) library.steps.step_typed (by trivial) next.2 binder info
  exact ⟨.stepBindValue annotation read.1 next.1 binder info checked,core,
    by rw [WordBinder.substitute_stepReadSource]; exact rep,typed⟩

/-- Branch children supply paired facts once, including arbitrary nested
State/read bindings and helper calls. Original guard typing is derived from
its independent scalar form and static register condition. -/
theorem Syntax.booleanBranchPaired {τ : Substitution} (library : ScopedSyntax.Library env)
    (inputs : InputsTyped env originalCtx originalInputs)
    (typing : LexicalScalarCode.ScopeTyped env originalCtx originalInputs)
    (value : LexicalScalarSyntax.Form env ctx p [] (σ.apply v) ∧
      LexicalScalarSyntax.Form env originalCtx originalInputs [] (τ.apply v))
    (static : LexicalScalarSyntax.StaticRegisters (τ.apply v))
    (yes : Syntax env ctx p σ scope a requirements ∧
      ∃ core, Represents (τ.apply a) core ∧ CastTyping env 0 (SourceCasts env) originalCtx core (optionType stateType))
    (no : Syntax env ctx p σ scope b requirements ∧
      ∃ core, Represents (τ.apply b) core ∧ CastTyping env 0 (SourceCasts env) originalCtx core (optionType stateType))
    (checked : requirements (σ.apply (Branch.source v (Branch.nativeBooleanDecision v) a b))) :
    Syntax env ctx p σ scope (Branch.source v (Branch.nativeBooleanDecision v) a b) requirements ∧
      ∃ core, Represents (τ.apply (Branch.source v (Branch.nativeBooleanDecision v) a b)) core ∧
        CastTyping env 0 (SourceCasts env) originalCtx core (optionType stateType) := by
  obtain ⟨core,rep,typed⟩ := sourceBooleanTyping library inputs typing value.2 static
    (nativeType := .app (.const ``Option [.zero]) state) (ty := optionType stateType)
    (.app (.constant rfl) (.constant rfl)) library.toLibrary.option_typed (by trivial) yes.2 no.2
  refine ⟨.booleanBranch value.1 yes.1 no.1 checked,core,?_,typed⟩
  cases τ <;> exact rep

end IRComparison.WordFrontend.FunctionSyntax

namespace IRComparison.WordFrontend.FunctionSyntax
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic StructuralBody StructuralSyntax
set_option maxHeartbeats 2400000

/-- Current-State leaves need no separate original core or type derivation. -/
theorem Syntax.valueCurrentPaired {τ : Substitution}
    (inputs : InputsTyped env originalCtx originalInputs)
    (current : σ.apply raw = p.s) (originalCurrent : τ.apply raw = originalInputs.s) :
    Syntax env (mode := .value) ctx p σ scope raw requirements ∧
      ∃ core, Represents (τ.apply raw) core ∧
        CastTyping env 0 (SourceCasts env) originalCtx core stateType :=
  ⟨.valueCurrent current,inputs.s.val,by rw [originalCurrent]; exact inputs.s.property,inputs.hs.withCasts _⟩

/-- Loop yield reuses the same State-value pair, including a State update. -/
theorem Syntax.yieldPaired {τ : Substitution} (library : ScopedSyntax.Library env)
    (value : Syntax env (mode := .value) ctx p σ scope raw requirements ∧
      ∃ core, Represents (τ.apply raw) core ∧ CastTyping env 0 (SourceCasts env) originalCtx core stateType) :
    Syntax env (mode := .step) ctx p σ scope (Step.yieldSource raw) requirements ∧
      ∃ core, Represents (τ.apply (Step.yieldSource raw)) core ∧
        CastTyping env 0 (SourceCasts env) originalCtx core (optionType Step.stepState) := by
  obtain ⟨core,rep,typed⟩ := value.2
  exact ⟨.yield value.1,_,by rw [substitute_yield]; exact Step.yield_represents rep,
    Step.yield_typed library.steps typed⟩

/-- The existing Option bind rule types ordinary sequential composition. -/
theorem Syntax.sequencePaired (library : ScopedSyntax.Library env)
    (first : Syntax env ctx p σ scope a requirements ∧
      ∃ core, Represents (τ.apply a) core ∧ CastTyping env 0 (SourceCasts env) originalCtx core (optionType stateType))
    (next : Syntax env (stateType::ctx) {p.lift with s := .bvar 0}
        (under σ) (.push none scope) b requirements ∧
      ∃ core, Represents ((under τ).apply b) core ∧
        CastTyping env 0 (SourceCasts env) (stateType::originalCtx) core (optionType stateType))
    (binder : Lean.Name) (info : Lean.BinderInfo) :
    Syntax env ctx p σ scope (sequenceSource a (.lam binder state b info)) requirements ∧
      ∃ core, Represents (τ.apply (sequenceSource a (.lam binder state b info))) core ∧
        CastTyping env 0 (SourceCasts env) originalCtx core (optionType stateType) := by
  obtain ⟨core,rep,typed⟩ := sourceBindTyping library
    (nativeDomain := state) (nativeResult := state) (.constant rfl) (.constant rfl)
    (.constant library.returns.state (by simp) rfl) (.constant library.returns.state (by simp) rfl)
    (by trivial) (by trivial) first.2 next.2 binder info
  exact ⟨.sequence first.1 next.1 binder info,core,by rw [substitute_sequence]; exact rep,typed⟩

/-- Ordinary commands can precede a loop-step continuation, without a second
induction through either child. -/
theorem Syntax.stepSequencePaired (library : ScopedSyntax.Library env)
    (first : Syntax env ctx p σ scope a requirements ∧
      ∃ core, Represents (τ.apply a) core ∧ CastTyping env 0 (SourceCasts env) originalCtx core (optionType stateType))
    (next : Syntax env (mode := .step) (stateType::ctx) {p.lift with s := .bvar 0}
        (under σ) (.push none scope) b requirements ∧
      ∃ core, Represents ((under τ).apply b) core ∧
        CastTyping env 0 (SourceCasts env) (stateType::originalCtx) core (optionType Step.stepState))
    (binder : Lean.Name) (info : Lean.BinderInfo) :
    Syntax env (mode := .step) ctx p σ scope
      (StructuralStep.sequenceSource a (.lam binder state b info)) requirements ∧
      ∃ core, Represents (τ.apply (StructuralStep.sequenceSource a (.lam binder state b info))) core ∧
        CastTyping env 0 (SourceCasts env) originalCtx core (optionType Step.stepState) := by
  obtain ⟨core,rep,typed⟩ := sourceBindTyping library
    (nativeDomain := state) (nativeResult := stepType) (.constant rfl) (.app (.constant rfl) (.constant rfl))
    (.constant library.returns.state (by simp) rfl) library.steps.step_typed
    (by trivial) (by trivial) first.2 next.2 binder info
  exact ⟨.stepSequence first.1 next.1 binder info,core,by rw [substitute_stepSequence]; exact rep,typed⟩

/-- Static-range source typing and retained syntax share the same child pair.
This rule neither expands iterations nor assumes a particular body shape. -/
theorem Syntax.forStaticPaired (library : ScopedSyntax.Library env)
    (inputs : InputsTyped env originalCtx originalInputs)
    (start : For.Bound env ctx (σ.apply a) × For.Bound env originalCtx (τ.apply a))
    (stop : For.Bound env ctx (σ.apply b) × For.Bound env originalCtx (τ.apply b))
    (stride : For.Bound env ctx (σ.apply c) × For.Bound env originalCtx (τ.apply c))
    (current : σ.apply st = p.s) (originalCurrent : τ.apply st = originalInputs.s)
    (body : Syntax env (mode := .step) (stateType::wordType::ctx) (For.parameters p)
        (under (under σ)) (.push none (.push none scope)) raw requirements ∧
      ∃ core, Represents ((under (under τ)).apply raw) core ∧
        CastTyping env 0 (SourceCasts env) (stateType::wordType::originalCtx) core (optionType Step.stepState))
    (kn tn : Lean.Name) (ki ti : Lean.BinderInfo)
    (checked : requirements (σ.apply (For.source a b c st (.lam kn word (.lam tn state raw ti) ki)))) :
    Syntax env ctx p σ scope (For.source a b c st (.lam kn word (.lam tn state raw ti) ki)) requirements ∧
      ∃ core, Represents (τ.apply (For.source a b c st (.lam kn word (.lam tn state raw ti) ki))) core ∧
        CastTyping env 0 (SourceCasts env) originalCtx core (optionType stateType) := by
  obtain ⟨core,rep,typed⟩ := sourceForStaticTyping library inputs start.2 stop.2 stride.2 body.2 kn tn ki ti
  exact ⟨.forStatic start.1 stop.1 stride.1 current body.1 kn tn ki ti checked,core,
    by rw [StructuralLoop.substitute_forStatic,originalCurrent]; exact rep,typed⟩

/-- forIn and foldlM use their existing binder orders and result modes.
Only the source body is processed; run-time loop counts are not unfolded. -/
theorem Syntax.forRangePaired (library : ScopedSyntax.Library env)
    (inputs : InputsTyped env originalCtx originalInputs)
    (typing : LexicalScalarCode.ScopeTyped env originalCtx originalInputs)
    (kind : NaturalLoop.Kind)
    (count : LexicalScalarSyntax.Form env ctx p [] (σ.apply n) ∧
      LexicalScalarSyntax.Form env originalCtx originalInputs [] (τ.apply n))
    (static : LexicalScalarSyntax.StaticRegisters (τ.apply n))
    (current : σ.apply st = p.s) (originalCurrent : τ.apply st = originalInputs.s)
    (body : Syntax env (mode := kind.mode) (kind.context ctx) (kind.parameters p)
        (under (under σ)) (.push none (.push none scope)) raw requirements ∧
      ∃ core, Represents ((under (under τ)).apply raw) core ∧
        CastTyping env 0 (SourceCasts env) (kind.context originalCtx) core (sourceResultType kind.mode))
    (kn tn : Lean.Name) (ki ti : Lean.BinderInfo)
    (checked : requirements (σ.apply (kind.source n st (kind.nativeLambda kn tn ki ti raw)))) :
    Syntax env ctx p σ scope (kind.source n st (kind.nativeLambda kn tn ki ti raw)) requirements ∧
      ∃ core, Represents (τ.apply (kind.source n st (kind.nativeLambda kn tn ki ti raw))) core ∧
        CastTyping env 0 (SourceCasts env) originalCtx core (optionType stateType) := by
  obtain ⟨core,rep,typed⟩ := sourceForRangeTyping library inputs typing kind count.2 static body.2 kn tn ki ti
  exact ⟨.forRange kind count.1 current body.1 kn tn ki ti checked,core,
    by rw [kind.substitute_source,originalCurrent]; exact rep,typed⟩

end IRComparison.WordFrontend.FunctionSyntax
