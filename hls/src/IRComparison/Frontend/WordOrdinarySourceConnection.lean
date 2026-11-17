import IRComparison.Frontend.WordOrdinarySourceRetag
import IRComparison.Frontend.WordOrdinarySourceSubstitution
import IRComparison.Frontend.WordOrdinarySourceFlow

/-! Internal bridges from original-source derivations to the existing Syntax
rules. These are induction steps, not the final public generation theorem:
the retained child Syntax is still to be constructed by the whole-source
interpretation. No success of parsing is assumed here. -/
namespace IRComparison.WordFrontend.OrdinarySource
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic StructuralBody FunctionSyntax
set_option maxHeartbeats 2400000

/-- Changing only Word/BV32 annotations does not change which original
lexical slots are State values. -/
theorem DemandsTyped.retag (typed : DemandsTyped Γ requires)
    (related : Context.Related Γ Δ) : DemandsTyped Δ requires := by
  intro n member
  obtain ⟨other,found,same⟩ := related.lookup (typed n member)
  cases same
  exact found

/-- Internal interpretation of the original State-use summary. Only the
State slots actually used by the source must denote the current State. -/
def CurrentMapping (σ : Substitution) (p : Inputs) (requires : List Nat) : Prop :=
  ∀ i ∈ requires, σ.reference i = p.s

theorem CurrentMapping.append (left : CurrentMapping σ p a) (right : CurrentMapping σ p b) :
    CurrentMapping σ p (a ++ b) := by
  intro i member
  exact (List.mem_append.mp member).elim (left i) (right i)

theorem CurrentMapping.left (mapping : CurrentMapping σ p (a ++ b)) : CurrentMapping σ p a :=
  fun i member => mapping i (List.mem_append_left _ member)

theorem CurrentMapping.right (mapping : CurrentMapping σ p (a ++ b)) : CurrentMapping σ p b :=
  fun i member => mapping i (List.mem_append_right _ member)

theorem CurrentMapping.appLeft (mapping : CurrentMapping σ p (stateVariables Γ (.app f a))) :
    CurrentMapping σ p (stateVariables Γ f) := by
  have pair : CurrentMapping σ p (stateVariables Γ f ++ stateVariables Γ a) := by
    simpa only [stateVariables,freeVariables,List.filter_append] using mapping
  exact pair.left

theorem CurrentMapping.appRight (mapping : CurrentMapping σ p (stateVariables Γ (.app f a))) :
    CurrentMapping σ p (stateVariables Γ a) := by
  have pair : CurrentMapping σ p (stateVariables Γ f ++ stateVariables Γ a) := by
    simpa only [stateVariables,freeVariables,List.filter_append] using mapping
  exact pair.right

theorem StateRef.current (source : StateRef Γ raw)
    (mapping : CurrentMapping σ p (stateVariables Γ raw)) : σ.apply raw = p.s := by
  cases source with
  | «variable» found =>
    rw [Substitution.apply_eq]
    apply mapping
    simp [stateVariables,freeVariables,found]

/-- Scalar/read/Unit bindings retain their values and shift outer State
references. The absence of a State demand at the new value is derived. -/
theorem CurrentMapping.underValue (mapping : CurrentMapping σ p (outsideValue requires))
    (typed : DemandsTyped (slot::Γ) requires) (notState : slot ≠ .value .state) :
    CurrentMapping (under σ) p.lift requires := by
  intro i member
  have positive := typed.valueBound notState i member
  cases i with
  | zero => omega
  | succ i =>
    have same := mapping i (List.mem_map.mpr ⟨i+1,member,rfl⟩)
    simpa only [under_reference,LeanBindings.underSubst,Inputs.lift] using
      congrArg (LeanBindings.rename Nat.succ) same

/-- A State-producing command establishes a fresh current State. This proof
is common to State lets and Option State sequencing. -/
theorem currentMapping_state (p : Inputs) (latest : currentOnly 0 requires) :
    CurrentMapping (under σ) {p.lift with s := .bvar 0} requires := by
  intro i member
  rw [latest i member]
  simp [under_reference,LeanBindings.underSubst,For.parameters]

/-- Both loop binders are interpreted structurally, without unfolding runtime
iterations. The native forIn/foldlM binder order remains explicit. -/
theorem currentMapping_range (kind : NaturalLoop.Kind)
    (latest : currentOnly (rangeStatePosition kind) requires) :
    CurrentMapping (under (under σ)) (kind.parameters p) requires := by
  intro i member
  rw [latest i member]
  cases kind <;> simp [under_reference,LeanBindings.underSubst,LeanBindings.rename,rangeStatePosition,NaturalLoop.Kind.parameters,NaturalScope.forInParameters,NaturalScope.foldParameters]

theorem currentMapping_staticRange (latest : currentOnly 0 requires) :
    CurrentMapping (under (under σ)) (For.parameters p) requires := by
  intro i member
  rw [latest i member]
  simp [under_reference,LeanBindings.underSubst,For.parameters]

/-- Function declarations do not create a target value binder. Their capture
summaries refer to outer source variables, whose mapping is unchanged. -/
theorem CurrentMapping.functionLet (mapping : CurrentMapping σ p (outsideValue requires))
    (typed : DemandsTyped (.function signature::Γ) requires) (value : Lean.Expr) :
    CurrentMapping (letSubstitution σ value) p requires := by
  intro i member
  have positive := typed.valueBound (by simp) i member
  cases i with
  | zero => omega
  | succ i => exact mapping i (List.mem_map.mpr ⟨i+1,member,rfl⟩)

private theorem parametersRepresented (parameters : List Parameter) :
    List.Forall₂ Represents (parameters.map Parameter.native) (parameters.map Parameter.core) := by
  induction parameters with
  | nil => exact .nil
  | cons p ps ih => exact .cons p.represented ih

/-- The call rule derives capture-substituted body types and argument checks
from original lexical derivations. Its retained child remains the recursive
Syntax induction hypothesis, not a premise of the source entrance. -/
theorem retainedCallMapped {body : Lean.Expr}
    (library : ScopedSyntax.Library env) (closed : ClosedConstantTypes env)
    (source : Body ds ((head::tail).reverse.map Slot.value ++ Γ) result original)
    (captureMapping : TypedMapping env Γ.core ctx captureCore)
    (captureRepresented : ∀ n, Represents (captureReferences n) (captureCore n))
    (shape : LambdaSource originalFunction ((head::tail).map Parameter.native) original)
    (fn argument : Lean.Expr)
    (functionMatches : σ.apply fn.getAppFn = LeanBindings.substitute captureReferences originalFunction)
    (coherent : scope.Coherent ctx.length σ)
    (binding : BindingValue scope ctx.length σ fn.getAppFn (.captured depth captured arity body functions))
    (length : ((Lean.Expr.app fn argument).getAppArgs.toList.map σ.apply).length = arity)
    (arguments : Arguments Δ (head::tail) originalArguments)
    (argumentMapping : TypedMapping env Δ.core ctx argumentCore)
    (argumentRepresented : ∀ n, Represents (argumentReferences n) (argumentCore n))
    (argumentsMatch : originalArguments.map (LeanBindings.substitute argumentReferences) =
      (Lean.Expr.app fn argument).getAppArgs.toList.map σ.apply)
    (retainedArgs : ArgumentBindings.Syntax env ctx p
      ((Lean.Expr.app fn argument).getAppArgs.toList.map σ.apply) [] finalCtx finalInputs finalArgs)
    (next : Syntax env (mode := result.mode) finalCtx finalInputs
      (closureSubstitution depth finalCtx.length captured finalArgs)
      (functions.parameters finalArgs.length) body requirements) :
    Syntax env (mode := result.mode) ctx p σ scope (.app fn argument) requirements := by
  obtain ⟨actual,cores,shapes,reps,types,checks⟩ := arguments.evidenceMapped library closed argumentMapping argumentRepresented
  rw [argumentsMatch] at reps
  have domainsLength := List.Forall₂.length_eq checks
  cases cores with
  | nil => simp at domainsLength
  | cons first rest =>
    obtain ⟨bc,br,bodyTypes⟩ := source.typingPrefixesMapped shapes library closed captureMapping captureRepresented
    obtain ⟨originalCore,originalRep,_⟩ := source.typing library closed
    have functionRep := lambdaSourceMapped_represents shape originalRep captureRepresented
    have bodySame := (originalRep.substitute _ _ (openMapping_represented captureRepresented (head::tail).length)).unique br
    rw [bodySame,← functionMatches] at functionRep
    have exactTypes : List.Forall₂ (fun ty arg => CastTyping env 0 (SourceCasts env) ctx arg ty)
        (actual.map Parameter.core) (first::rest) := List.forall₂_map_left_iff.mpr types
    have declaredChecks : List.Forall₂ (fun ty arg => CheckedTyping env 0 (SourceCasts env) ctx arg ty)
        ((head::tail).map Parameter.core) (first::rest) := List.forall₂_map_left_iff.mpr checks
    have params (ps : List Parameter) : ∀ d ∈ ps.map Parameter.core,
        ∃ u, CastTyping env 0 (SourceCasts env) [] d (.sort u) := by
      intro d hd
      obtain ⟨parameter,_,rfl⟩ := List.mem_map.mp hd
      exact ⟨_,(parameter.typed library).withCasts _⟩
    apply Syntax.retainedCallFromBodyTypes library closed fn argument (by cases result <;> simp [Result.mode])
      coherent binding length retainedArgs next exactTypes declaredChecks
      (by simpa only [List.length_map,List.length_cons] using domainsLength) ?_ ?_ reps functionRep
    · intro d member
      rcases List.mem_append.mp member with left | right
      · exact params (head::tail) d left
      · exact params actual d right
    · intro n hn
      have typed := bodyTypes n
      have resultEq : FunctionSyntax.sourceResultType result.mode = optionType result.core := by cases result <;> rfl
      rw [resultEq]
      simpa only [List.map_append,List.map_take,List.map_drop,List.map_cons] using typed

/-- The previous same-scope call bridge is an identity instance of the shared
captured-environment construction. -/
theorem retainedCall {body : Lean.Expr}
    (library : ScopedSyntax.Library env) (closed : ClosedConstantTypes env)
    (source : Body ds ((head::tail).reverse.map Slot.value ++ Γ) result original)
    (fn argument : Lean.Expr)
    (coherent : scope.Coherent Γ.core.length σ)
    (binding : BindingValue scope Γ.core.length σ fn.getAppFn (.captured depth captured arity body functions))
    (length : ((Lean.Expr.app fn argument).getAppArgs.toList.map σ.apply).length = arity)
    (arguments : Arguments Γ (head::tail) ((Lean.Expr.app fn argument).getAppArgs.toList.map σ.apply))
    (shape : LambdaSource (σ.apply fn.getAppFn) ((head::tail).map Parameter.native) original)
    (retainedArgs : ArgumentBindings.Syntax env Γ.core p
      ((Lean.Expr.app fn argument).getAppArgs.toList.map σ.apply) [] finalCtx finalInputs finalArgs)
    (next : Syntax env (mode := result.mode) finalCtx finalInputs
      (closureSubstitution depth finalCtx.length captured finalArgs)
      (functions.parameters finalArgs.length) body requirements) :
    Syntax env (mode := result.mode) Γ.core p σ scope (.app fn argument) requirements := by
  apply retainedCallMapped (captureReferences := Lean.Expr.bvar) (argumentReferences := Lean.Expr.bvar)
    library closed source TypedMapping.identity (fun _ => Represents.bvar) shape fn argument
    (by simp) coherent binding length arguments TypedMapping.identity (fun _ => Represents.bvar)
    (by simp) retainedArgs next

/-- Original helper declarations supply function and continuation typing.
Only the retained continuation remains as an internal induction hypothesis;
no second generation proof of an unused helper declaration is required. -/
theorem functionLet
    (library : ScopedSyntax.Library env) (closed : ClosedConstantTypes env)
    (valueSource : Function ds Γ value ⟨head::tail,helperResult⟩)
    (nextSource : Body ds (.function ⟨head::tail,helperResult⟩::Γ) result nextRaw)
    (spelling : Signature.Spelling ⟨head::tail,helperResult⟩ ty)
    (mapping : TypedMapping env Γ.core ctx τ)
    (represented : ∀ n, Represents (σ.reference n) (τ n))
    (binding : BindingValue scope ctx.length σ value closure)
    (tailSyntax : Syntax env (mode := result.mode) ctx p
      (letSubstitution σ value) (.push (some closure) scope) nextRaw requirements)
    (binder : Lean.Name) (flag : Bool) :
    Syntax env (mode := result.mode) ctx p σ scope
      (.letE binder ty value nextRaw flag) requirements := by
  obtain ⟨vc,vr,vt⟩ := valueSource.typingMapped library closed mapping represented
  have nextMapping : TypedMapping env (Context.core (.function ⟨head::tail,helperResult⟩::Γ))
      (Signature.core ⟨head::tail,helperResult⟩::ctx) (coreUnder τ) :=
    mapping.underClosed closed _ (Signature.closed _)
  obtain ⟨bc,br,bt⟩ := nextSource.typingMapped library closed nextMapping (mappingUnderRepresented represented)
  obtain ⟨level,typeTyped⟩ := Signature.typed ⟨head::tail,helperResult⟩ library closed (ctx := ctx)
  have typeAt : Represents (σ.apply ty) (Signature.core ⟨head::tail,helperResult⟩) := by
    rw [Substitution.apply_eq,spelling.substitute]
    exact spelling.represented
  have valueAt : Represents (σ.apply value) vc := by simpa only [Substitution.apply_eq] using vr
  have nextAt : Represents ((under σ).apply nextRaw) bc := by
    simpa only [Substitution.apply_eq,under_reference] using br
  obtain ⟨reduced,original⟩ := FunctionSyntax.let_representations
    (binder := binder) (ty := ty) (flag := flag) typeAt valueAt nextAt
  cases result with
  | body => exact .functionLet binder ty value nextRaw flag binding tailSyntax typeAt typeTyped bt vt reduced original
  | step => exact .stepFunctionLet binder ty value nextRaw flag binding tailSyntax typeAt typeTyped bt vt reduced original

/-- Compatibility wrapper: the former identity-only bridge now uses the same
captured-environment proof as every other helper declaration. -/
theorem functionLetIdentity
    (library : ScopedSyntax.Library env) (closed : ClosedConstantTypes env)
    (valueSource : Function ds Γ value ⟨head::tail,helperResult⟩)
    (nextSource : Body ds (.function ⟨head::tail,helperResult⟩::Γ) result nextRaw)
    (spelling : Signature.Spelling ⟨head::tail,helperResult⟩ ty)
    (binding : BindingValue scope Γ.core.length .identity value closure)
    (tailSyntax : Syntax env (mode := result.mode) Γ.core p
      (letSubstitution .identity value) (.push (some closure) scope) nextRaw requirements)
    (binder : Lean.Name) (flag : Bool) :
    Syntax env (mode := result.mode) Γ.core p .identity scope
      (.letE binder ty value nextRaw flag) requirements :=
  functionLet (σ := .identity) library closed valueSource nextSource spelling TypedMapping.identity
    (fun _ => Represents.bvar) binding tailSyntax binder flag

end IRComparison.WordFrontend.OrdinarySource
