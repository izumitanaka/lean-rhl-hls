import IRComparison.Frontend.WordOrdinarySourceBody

/-! Construct the retained helper-body environment from the existing argument
telescope. No retained-body Source judgment is requested from the caller. -/
namespace IRComparison.WordFrontend.OrdinarySource
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic StructuralBody ScalarSyntax
set_option maxHeartbeats 2400000

private theorem Parameter.core_injective {a b : Parameter} (same : a.core = b.core) : a = b := by
  rcases a with (_|_)|_|_|_ <;> rcases b with (_|_)|_|_|_ <;>
    simp_all [Parameter.core,WordBinder.Annotation.core,stateType,natType,wordType,bitvecType,UnitStep.unitType]

private theorem closure_append (capture target : Nat) (captured : Substitution)
    (saved : List Lean.Expr) (value : Lean.Expr) :
    closureSubstitution capture target captured (saved ++ [value]) =
      .bindings (fun n => match n with | 0 => value | n+1 => (closureSubstitution capture target captured saved).reference n) := by
  apply congrArg Substitution.bindings
  funext n
  cases n with
  | zero => simp [closureReference]
  | succ n =>
    simp [closureReference,Substitution.reference,List.reverse_append,List.getElem?_cons_succ,
      Nat.add_sub_add_right,closureSubstitution]

private theorem closure_open (bound : capture ≤ target) (captured : Substitution) (saved : List Lean.Expr) :
    closureSubstitution capture (target+1) captured (saved.map (LeanBindings.rename Nat.succ) ++ [.bvar 0]) =
      under (closureSubstitution capture target captured saved) := by
  apply congrArg Substitution.bindings
  funext n
  exact FunctionSyntax.closureSubstitution_open_next bound captured saved (.bvar n)

private theorem argumentTypes_lift
    (closed : ClosedConstantTypes env)
    (typed : List.Forall₂ (fun (parameter : Parameter) raw => ∃ core, Represents raw core ∧
      CastTyping env 0 (SourceCasts env) ctx core parameter.core) domains actuals)
    (binder : VExpr) :
    List.Forall₂ (fun (parameter : Parameter) raw => ∃ core, Represents raw core ∧
      CastTyping env 0 (SourceCasts env) (binder::ctx) core parameter.core)
      domains (actuals.map (LeanBindings.rename Nat.succ)) := by
  induction typed with
  | nil => exact .nil
  | @cons parameter raw domains actuals head tail ih =>
    obtain ⟨core,rep,typed⟩ := head
    exact .cons ⟨_,rep.lift,by simpa only [parameter.closed.lift_eq] using typed.lift closed SourceCasts.closed binder⟩ ih

/-- Proof bookkeeping for ordinary target binders, in introduction order.
This is a list of existing source parameter kinds, not an executable IR. -/
def targetContext : List Parameter → List VExpr → List VExpr
  | [],ctx => ctx
  | parameter::rest,ctx => targetContext rest (parameter.core::ctx)

def targetInputs : List Parameter → Inputs → Inputs
  | [],p => p
  | parameter::rest,p => targetInputs rest (parameter.extendInputs p)

theorem targetContext_append (first second : List Parameter) (ctx : List VExpr) :
    targetContext (first++second) ctx = targetContext second (targetContext first ctx) := by
  induction first generalizing ctx with
  | nil => rfl
  | cons p ps ih => exact ih _

theorem targetInputs_append (first second : List Parameter) (p : Inputs) :
    targetInputs (first++second) p = targetInputs second (targetInputs first p) := by
  induction first generalizing p with
  | nil => rfl
  | cons a as ih => exact ih _

theorem targetContext_length (path : List Parameter) (ctx : List VExpr) :
    (targetContext path ctx).length = ctx.length + path.length := by
  induction path generalizing ctx with
  | nil => rfl
  | cons a as ih => simpa only [targetContext,List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (a.core::ctx)

private theorem closure_shift_reference (bound : capture ≤ target) (captured : Substitution) (saved : List Lean.Expr) :
    closureSubstitution capture (target+1) captured (saved.map (LeanBindings.rename Nat.succ)) =
      .bindings (fun n => LeanBindings.rename Nat.succ ((closureSubstitution capture target captured saved).reference n)) := by
  apply congrArg Substitution.bindings
  funext n
  simp only [closureReference,← List.map_reverse,List.getElem?_map,List.length_map]
  cases present : saved.reverse[n]? with
  | some value => simp [present,Substitution.reference,closureSubstitution,closureReference]
  | none =>
    simp only [present,Option.map_none,Substitution.reference,closureSubstitution,closureReference,
      LeanBindings.rename_comp]
    congr 1
    funext k
    simp only [Function.comp_apply]
    omega

/-- All later scalar/State/read/loop binders preserve captured scalar values.
The original source context is unchanged; only target references are shifted.
This transports the same captured-body induction hypothesis to later calls. -/
theorem ScalarFrame.captureExtension
    (frame : ScalarFrame env Γ ctx p (closureSubstitution capture ctx.length captured []) τ)
    (path : List Parameter) (bound : capture ≤ ctx.length)
    (library : ScopedSyntax.Library env) (closed : ClosedConstantTypes env)
    (inputs : InputsTyped env ctx p) (typing : LexicalScalarCode.ScopeTyped env ctx p)
    (references : ReferenceScope p) :
    ∃ targetTypes, ScalarFrame env Γ (targetContext path ctx) (targetInputs path p)
      (closureSubstitution capture (targetContext path ctx).length captured []) targetTypes := by
  induction path generalizing ctx p τ with
  | nil => exact ⟨τ,frame⟩
  | cons parameter rest ih =>
    obtain ⟨⟨newInputs⟩,newTyping,newReferences⟩ := parameter.extendTyped library closed inputs typing references
    have shifted := frame.shiftTarget closed inputs typing references parameter
    have same : closureSubstitution capture (parameter.core::ctx).length captured [] =
        .bindings (fun n => LeanBindings.rename Nat.succ ((closureSubstitution capture ctx.length captured []).reference n)) :=
      closure_shift_reference bound captured []
    rw [← same] at shifted
    exact ih shifted (by simpa using Nat.le_trans bound (Nat.le_succ _)) newInputs newTyping newReferences

/-- Derive all target typing/reference obligations along the common binder
path. This includes the current State reference and is reused at helper calls. -/
theorem targetTyped (path : List Parameter) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (inputs : InputsTyped env ctx p)
    (typing : LexicalScalarCode.ScopeTyped env ctx p) (references : ReferenceScope p)
    (stateReference : ∃ index, p.s = .bvar index) :
    Nonempty (InputsTyped env (targetContext path ctx) (targetInputs path p)) ∧
      LexicalScalarCode.ScopeTyped env (targetContext path ctx) (targetInputs path p) ∧
      ReferenceScope (targetInputs path p) ∧ (∃ index, (targetInputs path p).s = .bvar index) := by
  induction path generalizing ctx p with
  | nil => exact ⟨⟨inputs⟩,typing,references,stateReference⟩
  | cons parameter rest ih =>
    obtain ⟨⟨nextInputs⟩,nextTyping,nextReferences⟩ := parameter.extendTyped library closed inputs typing references
    have nextState : ∃ index, (parameter.extendInputs p).s = .bvar index := by
      obtain ⟨index,same⟩ := stateReference
      cases parameter with
      | state => exact ⟨0,rfl⟩
      | scalar a | natural | unit => exact ⟨index+1,by simp [Parameter.extendInputs,Inputs.lift,same,LeanBindings.rename]⟩
    exact ih nextInputs nextTyping nextReferences nextState

/-- At declaration time reopening a captured environment is the identity on
references. No source syntax is expanded to obtain this frame. -/
theorem ScalarFrame.atCapture (frame : ScalarFrame env Γ ctx p σ τ) :
    ScalarFrame env Γ ctx p (closureSubstitution ctx.length ctx.length σ []) τ := by
  have same (n : Nat) : (closureSubstitution ctx.length ctx.length σ []).reference n = σ.reference n := by
    change LeanBindings.rename (fun i => i+(ctx.length-ctx.length)) (σ.reference (n-0)) = _
    simpa only [Nat.sub_self,Nat.add_zero,Nat.sub_zero] using LeanBindings.rename_id (σ.reference n)
  exact ⟨frame.typed,by simpa only [same] using frame.represented,
    by simpa only [same] using frame.valueReference,
    by simpa only [same] using frame.scalar,
    by simpa only [same] using frame.natural⟩

/-- Derive the existing call dispatch from the original argument and its
source parameter type. Nat iteration binders are represented in ScalarFrame,
but the existing helper calling convention is State, Unit and Word/BV32. -/
theorem Argument.retainedCase (source : Argument Γ parameter raw)
    (related : Context.Related Γ Δ) (frame : ScalarFrame env Δ ctx p σ τ)
    (library : ScopedSyntax.Library env) (closed : ClosedConstantTypes env)
    (inputs : InputsTyped env ctx p) (typing : LexicalScalarCode.ScopeTyped env ctx p)
    (references : ReferenceScope p) (current : CurrentMapping σ p (stateVariables Γ raw)) :
    σ.apply raw = p.s ∨
      (∃ core, Represents (σ.apply raw) core ∧ CastTyping env 0 (SourceCasts env) ctx core UnitStep.unitType) ∨
      (LexicalScalarSyntax.Form env ctx p [] (σ.apply raw) ∧
        LexicalScalarSyntax.StaticRegisters (σ.apply raw) ∧ sameTerm (σ.apply raw) p.s = false) := by
  cases source with
  | scalar value =>
    obtain ⟨form,static⟩ := value.forms related frame library closed inputs typing references current
    exact Or.inr (Or.inr ⟨form,static,(frame.evidence value related library closed).notState inputs⟩)
  | state value => exact Or.inl (value.current current)
  | unit =>
    refine Or.inr (Or.inl ⟨_,?_,library.units.value_typed.withCasts _⟩)
    cases σ <;> exact .constant rfl
  | @unitVariable index found =>
    obtain ⟨slot,lookup,same⟩ := related.lookup found
    cases same
    refine Or.inr (Or.inl ⟨τ index,?_,?_⟩)
    · simpa only [Substitution.apply_eq,LeanBindings.substitute] using frame.represented _
    · simpa only [substitute_closed Parameter.unit.closed] using frame.typed _ _ (Context.lookup lookup)

/-- A single traversal of the original argument list constructs the retained
binding telescope. No successful parser or retained-body judgment is assumed. -/
theorem Arguments.retained (source : Arguments Γ domains raws)
    (related : Context.Related Γ Δ) (frame : ScalarFrame env Δ ctx p σ τ)
    (library : ScopedSyntax.Library env) (closed : ClosedConstantTypes env)
    (inputs : InputsTyped env ctx p) (typing : LexicalScalarCode.ScopeTyped env ctx p)
    (references : ReferenceScope p)
    (current : CurrentMapping σ p (raws.flatMap (stateVariables Γ))) :
    ∃ finalCtx finalInputs finalArgs,
      ArgumentBindings.Syntax env ctx p (raws.map σ.apply) [] finalCtx finalInputs finalArgs := by
  apply StructuralBody.ArgumentBindings.fromSyntax library closed inputs typing references
  intro mapped member
  obtain ⟨raw,present,rfl⟩ := List.mem_map.mp member
  have select {domains : List Parameter} {raws : List Lean.Expr}
      (arguments : Arguments Γ domains raws) :
      ∀ raw ∈ raws, ∃ parameter, parameter ∈ domains ∧ Argument Γ parameter raw := by
    induction arguments with
    | nil => simp
    | @cons parameter value domains values head tail ih =>
      intro raw present
      rcases List.mem_cons.mp present with rfl | member
      · exact ⟨parameter,by simp,head⟩
      · obtain ⟨p,hp,proof⟩ := ih raw member
        exact ⟨p,List.mem_cons_of_mem _ hp,proof⟩
  have selected := select source raw present
  obtain ⟨parameter,declared,proof⟩ := selected
  exact proof.retainedCase related frame library closed inputs typing references
    (fun n member => current n (List.mem_flatMap.mpr ⟨raw,present,member⟩))

/-- Unit actuals are source literals or lexical values. Their static-register
properties follow from that syntax and the current binding environment. -/
theorem Argument.unitSafe (source : Argument Γ parameter raw) (registers : RegisterMapping σ)
    (unit : parameter = .unit) :
    LexicalScalarSyntax.StaticRegisters (σ.apply raw) ∧
      (σ.apply raw).getAppFn.constName? ≠ some ``HybridWord.State.regs := by
  cases source with
  | scalar value | state value => cases unit
  | unit => cases σ <;> exact ⟨by trivial,by intro h; cases h⟩
  | @unitVariable index found =>
    simpa only [Substitution.apply_eq,LeanBindings.substitute] using And.intro (registers.static index) (registers.head index)

theorem Arguments.unitSafe (source : Arguments Γ declared raws)
    (relation : List.Forall₂ Parameter.Related declared actual) (registers : RegisterMapping σ) :
    List.Forall₂ (fun parameter raw => parameter = .unit →
      LexicalScalarSyntax.StaticRegisters raw ∧ raw.getAppFn.constName? ≠ some ``HybridWord.State.regs)
      actual (raws.map σ.apply) := by
  induction source generalizing actual with
  | nil => cases relation; exact .nil
  | cons head tail ih =>
    cases relation with
    | cons same rest =>
      refine .cons ?_ (ih rest)
      intro unit
      subst_vars
      cases same
      exact head.unitSafe registers rfl

private theorem staticHead_lift
    (safe : LexicalScalarSyntax.StaticRegisters raw ∧ raw.getAppFn.constName? ≠ some ``HybridWord.State.regs) :
    LexicalScalarSyntax.StaticRegisters (LeanBindings.rename Nat.succ raw) ∧
      (LeanBindings.rename Nat.succ raw).getAppFn.constName? ≠ some ``HybridWord.State.regs := by
  refine ⟨safe.1.rename Nat.succ,?_⟩
  have head (value : Lean.Expr) : (LeanBindings.rename Nat.succ value).getAppFn.constName? = value.getAppFn.constName? := by
    induction value with
    | app f a ih _ => exact ih
    | _ => rfl
  rw [head]
  exact safe.2

private theorem unitSafe_lift
    (safe : List.Forall₂ (fun (parameter : Parameter) raw => parameter = .unit →
      LexicalScalarSyntax.StaticRegisters raw ∧ raw.getAppFn.constName? ≠ some ``HybridWord.State.regs)
      domains actuals) :
    List.Forall₂ (fun (parameter : Parameter) raw => parameter = .unit →
      LexicalScalarSyntax.StaticRegisters raw ∧ raw.getAppFn.constName? ≠ some ``HybridWord.State.regs)
      domains (actuals.map (LeanBindings.rename Nat.succ)) := by
  induction safe with
  | nil => exact .nil
  | cons head tail ih => exact .cons (fun unit => staticHead_lift (head unit)) ih

private theorem savedSafe_append
    (safe : ∀ raw ∈ saved, LexicalScalarSyntax.StaticRegisters raw ∧ raw.getAppFn.constName? ≠ some ``HybridWord.State.regs)
    (valueSafe : LexicalScalarSyntax.StaticRegisters value ∧ value.getAppFn.constName? ≠ some ``HybridWord.State.regs) :
    ∀ raw ∈ saved++[value], LexicalScalarSyntax.StaticRegisters raw ∧ raw.getAppFn.constName? ≠ some ``HybridWord.State.regs := by
  intro raw member
  rcases List.mem_append.mp member with old | new
  · exact safe raw old
  · have same : raw = value := by simpa using new
    subst raw
    exact valueSafe

/-- Internal State correspondence for an argument prefix. Only formal State
parameters alias the current State; captured States retain their original
identity and are demanded only where the original flow judgment uses them. -/
structure StateLinks (before : Substitution) (initial : Inputs) (after : Substitution) (final : Inputs)
    (domains : List Parameter) : Prop where
  outer : ∀ n, before.reference n = initial.s → after.reference (n+domains.length) = final.s
  formal : ∀ n, domains.reverse[n]? = some .state → after.reference n = final.s

theorem StateLinks.refl (σ : Substitution) (p : Inputs) : StateLinks σ p σ p [] :=
  ⟨fun _ h => h,by intro n found; simp at found⟩

theorem StateLinks.cons (tail : StateLinks middle next after final domains)
    (outer : ∀ n, before.reference n = initial.s → middle.reference (n+1) = next.s)
    (formal : parameter = .state → middle.reference 0 = next.s) :
    StateLinks before initial after final (parameter::domains) := by
  constructor
  · intro n current
    simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using tail.outer (n+1) (outer n current)
  · intro n found
    by_cases inside : n < domains.length
    · apply tail.formal n
      simpa only [List.reverse_cons,List.getElem?_append,List.length_reverse,inside,ite_true] using found
    · have beyond : domains.reverse[n]? = none := List.getElem?_eq_none_iff.mpr (by simpa using Nat.le_of_not_gt inside)
      have last : [parameter][n-domains.length]? = some .state := by
        simpa only [List.reverse_cons,List.getElem?_append,List.length_reverse,inside,ite_false] using found
      have atEnd : n = domains.length := by
        have small := List.getElem?_eq_some_iff.mp last
        have : n-domains.length < 1 := by simpa using small.1
        omega
      subst n
      have isState : parameter = .state := by simpa using last
      simpa only [Nat.zero_add] using tail.outer 0 (formal isState)

/-- The original body's State-demand list is sufficient at the retained
endpoint: formal demands use call-time State actuals, outer demands use the
captured source requirements. No post-substitution flow premise is supplied. -/
theorem StateLinks.current (links : StateLinks before initial after final domains)
    (typed : DemandsTyped (domains.reverse.map Slot.value ++ Γ) requires)
    (captured : CurrentMapping before initial (outerDemands domains.length requires)) :
    CurrentMapping after final requires := by
  intro n member
  have slot := typed n member
  by_cases inside : n < domains.length
  · apply links.formal n
    simp only [List.getElem?_append,List.length_map,List.length_reverse,inside,ite_true,List.getElem?_map] at slot
    cases found : domains.reverse[n]? with
    | none => simp [found] at slot
    | some parameter =>
      have same : parameter = .state := by simpa [found] using slot
      simpa only [same] using found
  · have present : n-domains.length ∈ outerDemands domains.length requires := by
      apply List.mem_filterMap.mpr
      exact ⟨n,member,by simp [Nat.le_of_not_gt inside]⟩
    have equality := links.outer (n-domains.length) (captured _ present)
    simpa only [Nat.sub_add_cancel (Nat.le_of_not_gt inside)] using equality

/-- The actual telescope constructs the helper's whole retained environment.
State/Unit parameters alias their call-time values; scalar parameters use
exactly the existing letValue binder. The arbitrary original body is not
examined here, so the result applies to any nesting of its commands. -/
theorem ArgumentBindings.heldEnvironment
    (arguments : StructuralBody.ArgumentBindings (env := env) ctx p actuals saved
      finalCtx finalInputs finalArgs sw nw cw qw)
    (library : ScopedSyntax.Library env) (closed : ClosedConstantTypes env)
    (inputs : InputsTyped env ctx p) (typing : LexicalScalarCode.ScopeTyped env ctx p)
    (references : ReferenceScope p) (stateReference : ∃ index, p.s = .bvar index)
    (types : List.Forall₂ (fun (parameter : Parameter) raw => ∃ core, Represents raw core ∧
      CastTyping env 0 (SourceCasts env) ctx core parameter.core) domains actuals)
    (bound : capture ≤ ctx.length)
    (frame : ScalarFrame env Γ ctx p (closureSubstitution capture ctx.length captured saved) τ)
    (unitSafe : List.Forall₂ (fun (parameter : Parameter) raw => parameter = .unit →
      LexicalScalarSyntax.StaticRegisters raw ∧ raw.getAppFn.constName? ≠ some ``HybridWord.State.regs) domains actuals)
    (savedSafe : ∀ raw ∈ saved, LexicalScalarSyntax.StaticRegisters raw ∧ raw.getAppFn.constName? ≠ some ``HybridWord.State.regs) :
    ∃ targetTypes,
      ScalarFrame env (domains.reverse.map Slot.value ++ Γ) finalCtx finalInputs
        (closureSubstitution capture finalCtx.length captured finalArgs) targetTypes ∧
      StateLinks (closureSubstitution capture ctx.length captured saved) p
        (closureSubstitution capture finalCtx.length captured finalArgs) finalInputs domains ∧
      ∃ path, finalCtx = targetContext path ctx ∧ finalInputs = targetInputs path p ∧
        ∀ raw ∈ finalArgs, LexicalScalarSyntax.StaticRegisters raw ∧ raw.getAppFn.constName? ≠ some ``HybridWord.State.regs := by
  induction arguments generalizing Γ domains τ with
  | done =>
    cases types
    exact ⟨τ,frame,StateLinks.refl _ _,[],rfl,rfl,savedSafe⟩
  | @state value ctx p rest saved fc fp fa sw nw cw qw current next ih =>
    cases types with
    | @cons parameter raw domains rest head tail =>
      obtain ⟨core,rep,typed⟩ := head
      rw [current] at rep
      have same := rep.unique inputs.s.property
      rw [same] at typed
      have parameterEq : parameter = .state := Parameter.core_injective (typed.unique (inputs.hs.withCasts (SourceCasts env)))
      subst parameter
      cases unitSafe with
      | cons safeHead safeTail =>
        have rawRep : Represents value inputs.s.val := by rw [current]; exact inputs.s.property
        have boundFrame := frame.bindHeld .state rawRep (inputs.hs.withCasts (SourceCasts env))
          (fun _ => by rw [current]; exact stateReference) (by intro a h; cases h) (by intro h; cases h)
        have linked := Eq.mpr (congrArg
          (fun substitution => ScalarFrame env (.value .state::Γ) ctx p substitution
            (fun n => match n with | 0 => inputs.s.val | n+1 => τ n))
          (closure_append capture ctx.length captured saved value)) boundFrame
        obtain ⟨target,result,links,path,hctx,hinputs,finalSafe⟩ := ih inputs typing references stateReference tail bound linked safeTail
          (savedSafe_append savedSafe (by
            rw [current]
            obtain ⟨index,same⟩ := stateReference
            rw [same]
            exact ⟨by trivial,by intro h; cases h⟩))
        refine ⟨target,by simpa only [List.reverse_cons,List.map_append,List.map_cons,List.map_nil,List.append_assoc,
          List.cons_append,List.nil_append] using result, StateLinks.cons links ?_ ?_,?_⟩
        · intro n same
          rw [closure_append]
          exact same
        · intro _
          rw [closure_append]
          exact current
        · exact ⟨path,hctx,hinputs,finalSafe⟩
  | @unit value unitCore ctx p rest saved fc fp fa sw nw cw qw represented unitTyped next ih =>
    cases types with
    | @cons parameter raw domains rest head tail =>
      obtain ⟨core,rep,typed⟩ := head
      have same := rep.unique represented
      rw [same] at typed
      have parameterEq : parameter = .unit := Parameter.core_injective (typed.unique unitTyped)
      subst parameter
      cases unitSafe with
      | cons safeHead safeTail =>
        have boundFrame := frame.bindHeld .unit represented unitTyped
          (fun impossible => False.elim (impossible rfl)) (by intro a h; cases h) (by intro h; cases h)
        have linked := Eq.mpr (congrArg
          (fun substitution => ScalarFrame env (.value .unit::Γ) ctx p substitution
            (fun n => match n with | 0 => unitCore | n+1 => τ n))
          (closure_append capture ctx.length captured saved value)) boundFrame
        obtain ⟨target,result,links,path,hctx,hinputs,finalSafe⟩ := ih inputs typing references stateReference tail bound linked safeTail (savedSafe_append savedSafe (safeHead rfl))
        refine ⟨target,by simpa only [List.reverse_cons,List.map_append,List.map_cons,List.map_nil,List.append_assoc,
          List.cons_append,List.nil_append] using result, StateLinks.cons links ?_ ?_,?_⟩
        · intro n same
          rw [closure_append]
          exact same
        · intro impossible
          cases impossible
        · exact ⟨path,hctx,hinputs,finalSafe⟩
  | @scalar ctx p value f vc vq valueCore fc fp fa sw nw cw qw rest saved valueSource annotation represented scalarTyped apart next ih =>
    cases types with
    | @cons parameter raw domains rest head tail =>
      obtain ⟨core,rep,typed⟩ := head
      have same := rep.unique represented
      rw [same] at typed
      have parameterEq : parameter = .scalar annotation := Parameter.core_injective (typed.unique scalarTyped)
      subst parameter
      cases unitSafe with
      | cons safeHead safeTail =>
        have boundFrame := frame.underScalar closed inputs typing references annotation
        rw [← closure_open bound] at boundFrame
        have stateRef : ∃ index, ((Parameter.scalar annotation).extendInputs p).s = .bvar index := by
          obtain ⟨index,same⟩ := stateReference
          exact ⟨index+1,by simp [Parameter.extendInputs,Inputs.lift,same,LeanBindings.rename]⟩
        obtain ⟨target,result,links,path,hctx,hinputs,finalSafe⟩ := ih
          (annotation.nextInputs inputs closed library.scalars.toSignatures library.cons)
          (typing.nextWord closed annotation) references.scalar stateRef
          (argumentTypes_lift closed tail annotation.core) (by simpa using Nat.le_trans bound (Nat.le_succ _)) boundFrame (unitSafe_lift safeTail)
          (savedSafe_append (by
            intro raw member
            obtain ⟨original,oldMember,rfl⟩ := List.mem_map.mp member
            exact staticHead_lift (savedSafe original oldMember))
            ⟨by trivial,by intro h; cases h⟩)
        refine ⟨target,by simpa only [List.reverse_cons,List.map_append,List.map_cons,List.map_nil,List.append_assoc,
          List.cons_append,List.nil_append] using result, StateLinks.cons links ?_ ?_,?_⟩
        · intro n same
          simp only [List.length_cons]
          rw [closure_open bound]
          change LeanBindings.rename Nat.succ ((closureSubstitution capture ctx.length captured saved).reference n) = p.lift.s
          rw [same]
          rfl
        · intro impossible
          cases impossible
        · exact ⟨.scalar annotation::path,hctx,hinputs,finalSafe⟩
  
end IRComparison.WordFrontend.OrdinarySource
