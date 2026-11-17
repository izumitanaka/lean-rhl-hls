import IRComparison.Frontend.WordOrdinarySource

/-! Original-source State-use conditions. These decorate OrdinarySource.Body;
they are not a second executable language and contain no transformed body,
compiler environment, CastTyping or parsing-success premise.

A summary lists original lexical State variables that must designate the
current State at entry. A helper declaration computes its summary from its
one original body. Calling the helper consults that summary; merely declaring
an unused helper does not demand that its captured State be current.

This file defines the static obligations. Their interpretation into the
compiler's substitution/closure invariants remains a separate proof. -/
namespace IRComparison.WordFrontend.OrdinarySource

/-- Free variable positions, independent of compiler substitution and typing. -/
def freeVariables (depth : Nat) : Lean.Expr → List Nat
  | .bvar n => if n < depth then [] else [n-depth]
  | .app f a => freeVariables depth f ++ freeVariables depth a
  | .lam _ ty body _ | .forallE _ ty body _ =>
      freeVariables depth ty ++ freeVariables (depth+1) body
  | .letE _ ty value body _ =>
      freeVariables depth ty ++ freeVariables depth value ++ freeVariables (depth+1) body
  | .mdata _ body | .proj _ _ body => freeVariables depth body
  | _ => []

/-- Scalar references are values saved at their original binding point;
only variables of State type contribute State-use requirements. -/
def stateVariables (Γ : Context) (raw : Lean.Expr) : List Nat :=
  (freeVariables 0 raw).filter (fun n => Γ[n]? == some (.value .state))

theorem freeVariables_succ (raw : Lean.Expr) (depth : Nat) :
    freeVariables (depth+1) raw =
      (freeVariables depth raw).filterMap (fun i => if i = 0 then none else some (i-1)) := by
  induction raw generalizing depth with
  | bvar n =>
    by_cases below : n < depth
    · simp [freeVariables,below,show n < depth+1 by omega]
    · by_cases atBinder : n = depth
      · subst n; simp [freeVariables]
      · simp [freeVariables,below,show ¬ n < depth+1 by omega,
          show n-depth ≠ 0 by omega,Nat.sub_sub]
  | app f a ihf iha => simp [freeVariables,ihf,iha,List.filterMap_append]
  | lam name ty body info iht ihb | forallE name ty body info iht ihb =>
    simp [freeVariables,iht,ihb,List.filterMap_append]
  | letE name ty value body flag iht ihv ihb =>
    simp [freeVariables,iht,ihv,ihb,List.filterMap_append]
  | mdata data body ih | proj name field body ih => exact ih depth
  | _ => rfl

/-- A source lexical slot optionally carries a helper's capture requirements.
No value or generated code is stored here. -/
abbrev EffectScope := List (Option (List Nat))

def liftEffects (n : Nat) (scope : EffectScope) : EffectScope :=
  scope.map (Option.map (List.map (fun i => i+n)))

def bindEffects (scope : EffectScope) : EffectScope := none :: liftEffects 1 scope

def bindFunctionEffects (requires : List Nat) (scope : EffectScope) : EffectScope :=
  some (requires.map Nat.succ) :: liftEffects 1 scope

def parameterEffects (n : Nat) (scope : EffectScope) : EffectScope :=
  List.replicate n none ++ liftEffects n scope

/-- Remove original formal parameters from a helper's free capture demands. -/
def outerDemands (n : Nat) (requires : List Nat) : List Nat :=
  requires.filterMap (fun i => if n ≤ i then some (i-n) else none)

/-- Under an ordinary value/Unit binder, requirements are shifted lexical
positions. State bindings instead replace the current State, see the rules. -/
def outsideValue (requires : List Nat) : List Nat := requires.map Nat.pred

/-- Removing a non-State source binder shifts only the outer demands.
This fact applies equally to scalar let/beta, read and Unit binders. -/
theorem stateVariables_underValue {Γ : Context} (slot : Slot)
    (notState : slot ≠ .value .state) (raw : Lean.Expr) :
    (freeVariables 1 raw).filter (fun i => Γ[i]? == some (.value .state)) =
      outsideValue (stateVariables (slot::Γ) raw) := by
  rw [freeVariables_succ raw 0]
  unfold outsideValue stateVariables
  generalize freeVariables 0 raw = positions
  induction positions with
  | nil => rfl
  | cons n rest ih =>
    cases n with
    | zero => simpa [List.filter_cons,notState] using ih
    | succ n =>
      simp only [Nat.succ_ne_zero,if_false,List.filterMap_cons,List.filterMap_some,Nat.add_sub_cancel,
        List.filter_cons,List.getElem?_cons_succ]
      split <;> simp_all

theorem stateVariables_letScalar (Γ : Context) (annotation : WordBinder.Annotation)
    (binder : Lean.Name) (value body : Lean.Expr) (flag : Bool) :
    stateVariables Γ (WordBinder.letSource annotation binder value body flag) =
      stateVariables Γ value ++ outsideValue (stateVariables (.value (.scalar annotation)::Γ) body) := by
  rw [← stateVariables_underValue (.value (.scalar annotation)) (by simp)]
  cases annotation <;> simp [stateVariables,freeVariables,WordBinder.letSource,WordBinder.Annotation.native,
    Arithmetic.nativeWidth,WordFrontend.word,app,List.filter_append]

theorem stateVariables_betaScalar (Γ : Context) (annotation : WordBinder.Annotation)
    (binder : Lean.Name) (value body : Lean.Expr) (info : Lean.BinderInfo) :
    stateVariables Γ (.app (.lam binder annotation.native body info) value) =
      outsideValue (stateVariables (.value (.scalar annotation)::Γ) body) ++ stateVariables Γ value := by
  rw [← stateVariables_underValue (.value (.scalar annotation)) (by simp)]
  cases annotation <;> simp [stateVariables,freeVariables,WordBinder.Annotation.native,
    Arithmetic.nativeWidth,WordFrontend.word,app,List.filter_append]

def currentOnly (position : Nat) (requires : List Nat) : Prop :=
  ∀ i ∈ requires, i = position

def valueBound (requires : List Nat) : Prop := ∀ i ∈ requires, 0 < i

def rangeStatePosition : NaturalLoop.Kind → Nat
  | .forIn => 0
  | .fold => 1

mutual
inductive Function.Flow (ds : FixedMemory.Declarations) :
    {Γ : Context} → {raw : Lean.Expr} → {signature : Signature} →
    Function ds Γ raw signature → EffectScope → List Nat → Prop where
  | variable {Γ : Context} {index : Nat} (source : Γ[index]? = some (.function signature))
      (found : effects[index]? = some (some requires)) :
      Function.Flow ds (.variable source) effects requires
  | lambda {body : Lean.Expr} (head : Parameter) (tail : List Parameter) (result : Result)
      (shape : StructuralBody.LambdaSource raw ((head::tail).map Parameter.native) body)
      (source : Body ds ((head::tail).reverse.map Slot.value ++ Γ) result body)
      (flow : Body.Flow ds source (parameterEffects (head::tail).length effects) requires) :
      Function.Flow ds (.lambda head tail result shape source) effects
        (outerDemands (head::tail).length requires)
inductive Body.Flow (ds : FixedMemory.Declarations) :
    {Γ : Context} → {result : Result} → {raw : Lean.Expr} →
    Body ds Γ result raw → EffectScope → List Nat → Prop where
  | returns (tag : Certificate.Return.Form) (value : StateValue Γ st) :
      Body.Flow ds (.returns tag value) effects (stateVariables Γ st)
  | yield (value : StateValue Γ st) :
      Body.Flow ds (.yield value) effects (stateVariables Γ st)
  | write (state : StateRef Γ st) (array : Nat) (an : NatNotation)
      (declared : (FixedMemory.lookup ds array).isSome = true)
      (index : Scalar Γ k ka) (value : Scalar Γ v va) :
      Body.Flow ds (.write state array an declared index value) effects
        (stateVariables Γ st ++ stateVariables Γ k ++ stateVariables Γ v)
  | copy (state : StateRef Γ st) (destination origin count : Nat) (dn sn cn : NatNotation)
      (target : FixedMemory.lookup ds destination = some count)
      (source : FixedMemory.lookup ds origin = some count) :
      Body.Flow ds (.copy state destination origin count dn sn cn target source) effects (stateVariables Γ st)
  | letScalar (result : Result) (annotation : WordBinder.Annotation) (value : Scalar Γ v actual)
      (next : Body ds (.value (.scalar annotation)::Γ) result b)
      (binder : Lean.Name) (flag : Bool)
      (flow : Body.Flow ds next (bindEffects effects) requires) :
      Body.Flow ds (.letScalar result annotation value next binder flag) effects
        (stateVariables Γ v ++ outsideValue requires)
  | letState (result : Result) (value : StateValue Γ v)
      (next : Body ds (.value .state::Γ) result b) (binder : Lean.Name) (flag : Bool)
      (flow : Body.Flow ds next (bindEffects effects) requires) (latest : currentOnly 0 requires) :
      Body.Flow ds (.letState result value next binder flag) effects (stateVariables Γ v)
  | bindState (result : Result) (first : Body ds Γ .body a)
      (next : Body ds (.value .state::Γ) result b) (binder : Lean.Name) (info : Lean.BinderInfo)
      (firstFlow : Body.Flow ds first effects before)
      (nextFlow : Body.Flow ds next (bindEffects effects) after) (latest : currentOnly 0 after) :
      Body.Flow ds (.bindState result first next binder info) effects before
  | bindRead (result : Result) (annotation : WordBinder.Annotation) (read : Read ds Γ v actual)
      (next : Body ds (.value (.scalar annotation)::Γ) result b) (binder : Lean.Name) (info : Lean.BinderInfo)
      (flow : Body.Flow ds next (bindEffects effects) requires) :
      Body.Flow ds (.bindRead result annotation read next binder info) effects
        (stateVariables Γ v ++ outsideValue requires)
  | branch (result : Result) (annotation : WordBinder.Annotation) (guard : Scalar Γ v actual)
      (yes : Body ds Γ result a) (no : Body ds Γ result b)
      (yesFlow : Body.Flow ds yes effects yesRequires) (noFlow : Body.Flow ds no effects noRequires) :
      Body.Flow ds (.branch result annotation guard yes no) effects
        (stateVariables Γ v ++ yesRequires ++ noRequires)
  | staticRange (state : StateRef Γ st)
      (start : FixedSequenceCompleteness.StaticBound a av)
      (stop : FixedSequenceCompleteness.StaticBound b bv)
      (stride : FixedSequenceCompleteness.StaticBound c cv)
      (body : Body ds (.value .state::.value (.scalar .word)::Γ) .step raw)
      (kn tn : Lean.Name) (ki ti : Lean.BinderInfo)
      (flow : Body.Flow ds body (parameterEffects 2 effects) requires) (latest : currentOnly 0 requires) :
      Body.Flow ds (.staticRange state start stop stride body kn tn ki ti) effects (stateVariables Γ st)
  | naturalRange (kind : NaturalLoop.Kind) (state : StateRef Γ st) (count : Scalar Γ n actual)
      (body : Body ds (rangeContext kind Γ) (rangeResult kind) raw)
      (kn tn : Lean.Name) (ki ti : Lean.BinderInfo)
      (flow : Body.Flow ds body (parameterEffects 2 effects) requires)
      (latest : currentOnly (rangeStatePosition kind) requires) :
      Body.Flow ds (.naturalRange kind state count body kn tn ki ti) effects
        (stateVariables Γ st ++ stateVariables Γ n)
  | unitSequence (result : Result) (next : Body ds (.value .unit::Γ) result b)
      (binder : Lean.Name) (info : Lean.BinderInfo)
      (flow : Body.Flow ds next (bindEffects effects) requires) :
      Body.Flow ds (.unitSequence result next binder info) effects (outsideValue requires)
  | call (fn : Function ds Γ f ⟨head::tail,result⟩)
      (arguments : Arguments Γ (head::tail) (first::rest))
      (flow : Function.Flow ds fn effects requires) :
      Body.Flow ds (.call fn arguments) effects
        (requires ++ (first::rest).flatMap (stateVariables Γ))
  | letFunction (spelling : Signature.Spelling signature ty) (value : Function ds Γ v signature)
      (next : Body ds (.function signature::Γ) result b) (binder : Lean.Name) (flag : Bool)
      (valueFlow : Function.Flow ds value effects captureRequires)
      (nextFlow : Body.Flow ds next (bindFunctionEffects captureRequires effects) requires)
      :
      Body.Flow ds (.letFunction spelling value next binder flag) effects (outsideValue requires)
end

/-- Capture summaries name State slots in the original lexical context. -/
def DemandsTyped (Γ : Context) (requires : List Nat) : Prop :=
  ∀ i ∈ requires, Γ[i]? = some (.value .state)

def EffectsTyped (Γ : Context) (effects : EffectScope) : Prop :=
  ∀ requires, some requires ∈ effects → DemandsTyped Γ requires

theorem stateVariables_typed (Γ : Context) (raw : Lean.Expr) :
    DemandsTyped Γ (stateVariables Γ raw) := by
  intro i hi
  exact eq_of_beq (List.mem_filter.mp hi).2

theorem DemandsTyped.append (left : DemandsTyped Γ a) (right : DemandsTyped Γ b) :
    DemandsTyped Γ (a ++ b) := by
  intro i hi
  exact (List.mem_append.mp hi).elim (left i) (right i)

theorem DemandsTyped.shift (typed : DemandsTyped Γ requires) (front : Context) :
    DemandsTyped (front ++ Γ) (requires.map (fun i => i + front.length)) := by
  intro i hi
  obtain ⟨j,member,rfl⟩ := List.mem_map.mp hi
  rw [List.getElem?_append_right (by omega)]
  simpa using typed j member

theorem DemandsTyped.outer (typed : DemandsTyped (front ++ Γ) requires) :
    DemandsTyped Γ (outerDemands front.length requires) := by
  intro i hi
  obtain ⟨j,member,eq⟩ := List.mem_filterMap.mp hi
  split at eq
  next bound =>
    cases Option.some.inj eq
    have lookup := typed j member
    rwa [List.getElem?_append_right bound] at lookup
  next => contradiction

theorem DemandsTyped.outside (typed : DemandsTyped (slot :: Γ) requires)
    (notState : slot ≠ .value .state) : DemandsTyped Γ (outsideValue requires) := by
  intro i hi
  obtain ⟨j,member,rfl⟩ := List.mem_map.mp hi
  have lookup := typed j member
  cases j with
  | zero => exact False.elim (notState (Option.some.inj lookup))
  | succ j => exact lookup

theorem DemandsTyped.valueBound (typed : DemandsTyped (slot :: Γ) requires)
    (notState : slot ≠ .value .state) : valueBound requires := by
  intro i hi
  cases i with
  | zero => exact False.elim (notState (Option.some.inj (typed 0 hi)))
  | succ i => omega

theorem EffectsTyped.parameters (typed : EffectsTyped Γ effects) (front : Context) :
    EffectsTyped (front ++ Γ) (parameterEffects front.length effects) := by
  intro requires member
  rcases List.mem_append.mp member with fresh | outer
  · have := List.eq_of_mem_replicate fresh
    contradiction
  · obtain ⟨old,oldMember,eq⟩ := List.mem_map.mp outer
    cases old with
    | none => contradiction
    | some old =>
      have same := Option.some.inj eq
      rw [← same]
      exact (typed old oldMember).shift front

theorem EffectsTyped.bind (typed : EffectsTyped Γ effects) (slot : Slot) :
    EffectsTyped (slot::Γ) (bindEffects effects) := by
  exact typed.parameters [slot]

theorem EffectsTyped.bindFunction (typed : EffectsTyped Γ effects)
    (captures : DemandsTyped Γ requires) (signature : Signature) :
    EffectsTyped (.function signature::Γ) (bindFunctionEffects requires effects) := by
  intro rs member
  rcases List.mem_cons.mp member with head | tail
  · cases Option.some.inj head
    simpa [Nat.succ_eq_add_one] using captures.shift [.function signature]
  · exact typed.bind (.function signature) rs (List.mem_cons_of_mem _ tail)

private theorem flowTyped :
    (∀ {Γ raw signature} {source : Function ds Γ raw signature} {effects requires},
      Function.Flow ds source effects requires → EffectsTyped Γ effects → DemandsTyped Γ requires) ∧
    (∀ {Γ result raw} {source : Body ds Γ result raw} {effects requires},
      Body.Flow ds source effects requires → EffectsTyped Γ effects → DemandsTyped Γ requires) := by
  refine ⟨@Function.Flow.rec ds
    (fun {Γ _ _} _ effects requires _ => EffectsTyped Γ effects → DemandsTyped Γ requires)
    (fun {Γ _ _} _ effects requires _ => EffectsTyped Γ effects → DemandsTyped Γ requires)
    ?«variable» ?lambda ?returns ?yield ?write ?copy ?letScalar ?letState ?bindState ?bindRead ?branch ?staticRange ?naturalRange ?unitSequence ?call ?letFunction,
    @Body.Flow.rec ds
    (fun {Γ _ _} _ effects requires _ => EffectsTyped Γ effects → DemandsTyped Γ requires)
    (fun {Γ _ _} _ effects requires _ => EffectsTyped Γ effects → DemandsTyped Γ requires)
    ?«variable» ?lambda ?returns ?yield ?write ?copy ?letScalar ?letState ?bindState ?bindRead ?branch ?staticRange ?naturalRange ?unitSequence ?call ?letFunction⟩
  all_goals first
  | (case «variable» =>
    intro signature effects requires Γ index source found typed
    exact typed requires (List.mem_of_getElem? found))
  | (case lambda =>
    intro raw Γ effects requires b head tail result shape source flow ih typed
    have frame := typed.parameters ((head::tail).reverse.map Slot.value)
    simp only [List.length_map,List.length_reverse] at frame
    simpa only [List.length_map,List.length_reverse] using (ih frame).outer)
  | (case returns => intro Γ st effects tag value typed; exact stateVariables_typed _ _)
  | (case yield => intro Γ st effects value typed; exact stateVariables_typed _ _)
  | (case write => intro Γ st k ka v va effects state array an declared index value typed; exact ((stateVariables_typed _ _).append (stateVariables_typed _ _)).append (stateVariables_typed _ _))
  | (case copy => intro Γ st effects state d o n dn sn cn target source typed; exact stateVariables_typed _ _)
  | (case letScalar =>
    intro Γ v actual b effects requires result annotation value next binder flag flow ih typed
    exact (stateVariables_typed _ _).append ((ih (typed.bind _)).outside (by simp)))
  | (case letState => intro Γ v b effects requires result value next binder flag flow latest ih typed; exact stateVariables_typed _ _)
  | (case bindState =>
    intro Γ a b effects before after result first next binder info ff nf latest ihf ihn typed
    exact ihf typed)
  | (case bindRead =>
    intro Γ v actual b effects requires result annotation read next binder info flow ih typed
    exact (stateVariables_typed _ _).append ((ih (typed.bind _)).outside (by simp)))
  | (case branch =>
    intro Γ v actual a b effects yr nr result annotation guard yes no yf nf iy ino typed
    exact ((stateVariables_typed _ _).append (iy typed)).append (ino typed))
  | (case staticRange => intro Γ st a av b bv c cv raw effects requires state start stop stride body kn tn ki ti flow latest ih typed; exact stateVariables_typed _ _)
  | (case naturalRange => intro Γ st n actual raw effects requires kind state count body kn tn ki ti flow latest ih typed; exact (stateVariables_typed _ _).append (stateVariables_typed _ _))
  | (case unitSequence =>
    intro Γ b effects requires result next binder info flow ih typed
    exact (ih (typed.bind _)).outside (by simp))
  | (case call =>
    intro Γ f head tail result first rest effects requires fn arguments flow ih typed
    apply (ih typed).append
    intro i member
    obtain ⟨raw,_,member⟩ := List.mem_flatMap.mp member
    exact stateVariables_typed Γ raw i member)
  | (case letFunction =>
    intro signature ty Γ v result b effects captureRequires requires spelling value next binder flag vf nf iv ine typed
    exact (ine (typed.bindFunction (iv typed) signature)).outside (by simp))

/-- All helper capture positions refer to original State variables. -/
theorem Function.Flow.demandsTyped {source : Function ds Γ raw signature} (flow : Function.Flow ds source effects requires)
    (typed : EffectsTyped Γ effects) : DemandsTyped Γ requires := flowTyped.1 flow typed

/-- A single induction handles arbitrary nesting of calls, State/read bindings,
branches and loops. In particular the non-State binder cannot contribute a
State demand; users need not supply that internal bound condition. -/
theorem Body.Flow.demandsTyped {source : Body ds Γ result raw} (flow : Body.Flow ds source effects requires)
    (typed : EffectsTyped Γ effects) : DemandsTyped Γ requires := flowTyped.2 flow typed

/-- Independent source-side current-State obligation at the State-only
ordinary entry. This does not yet constitute a generation-success theorem. -/
def Body.Current (source : Body ds [.value .state] .body raw) : Prop :=
  ∃ requires, Body.Flow ds source [none] requires ∧ currentOnly 0 requires

end IRComparison.WordFrontend.OrdinarySource
