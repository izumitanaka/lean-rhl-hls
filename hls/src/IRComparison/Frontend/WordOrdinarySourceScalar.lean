import IRComparison.Frontend.WordOrdinarySourceConnection

/-! Internal scalar-reference environment for interpreting the original
source judgment. These conditions are established by lexical bindings, not
added to the public source grammar. In particular, scalar lets use the same
original body under an opened binder; no substituted-body family is supplied. -/
namespace IRComparison.WordFrontend.OrdinarySource
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic StructuralBody ScalarSyntax
set_option maxHeartbeats 2400000

/-- The runtime frontend keeps scalar values as references. Helpers may map
to closures, so this invariant applies only to original value slots. -/
structure ScalarFrame (env : VEnv) (Γ : Context) (ctx : List VExpr) (p : Inputs)
    (σ : Substitution) (τ : Nat → VExpr) : Prop where
  typed : TypedMapping env Γ.core ctx τ
  represented : ∀ n, Represents (σ.reference n) (τ n)
  valueReference : ∀ n parameter, Γ[n]? = some (.value parameter) → parameter ≠ .unit →
    ∃ index, σ.reference n = .bvar index
  scalar : ∀ n annotation, Γ[n]? = some (.value (.scalar annotation)) →
    LexicalScalarSyntax.Form env ctx p [] (σ.reference n)
  natural : ∀ n, Γ[n]? = some (.value .natural) →
    LexicalScalarSyntax.Form env ctx p [] (NaturalScope.nativeIndex (σ.reference n))

private theorem Signature.notScalar (signature : Signature) (annotation : WordBinder.Annotation) :
    signature.core ≠ annotation.core := by
  rcases signature with ⟨domains,result⟩
  cases domains <;> cases annotation <;> cases result <;>
    simp [Signature.core,WordBinder.Annotation.core,optionType,wordType,bitvecType,Result.core]

theorem ScalarFrame.scalarShape {annotation : WordBinder.Annotation} (frame : ScalarFrame env Γ ctx p σ τ)
    (found : Lookup Γ.core n annotation.core) :
    LexicalScalarSyntax.ValueShape env ctx (τ n) annotation.core := by
  obtain ⟨slot,selected,same⟩ := Context.lookup_origin found
  cases slot with
  | function signature => exact False.elim (signature.notScalar annotation same.symm)
  | value parameter =>
    obtain ⟨index,equal⟩ := frame.valueReference n parameter selected (by
      cases parameter <;> cases annotation <;> simp_all [Slot.core,Parameter.core,WordBinder.Annotation.core,wordType,bitvecType,UnitStep.unitType])
    have rep := frame.represented n
    rw [equal] at rep
    rw [rep.unique Represents.bvar]
    exact .bound

theorem StateRef.mappedReference (source : StateRef Γ raw) (related : Context.Related Γ Δ)
    (frame : ScalarFrame env Δ ctx p σ τ) : ∃ index, σ.apply raw = .bvar index := by
  cases source with
  | «variable» found =>
    obtain ⟨slot,selected,same⟩ := related.lookup found
    cases same
    simpa only [Substitution.apply_eq,LeanBindings.substitute] using frame.valueReference _ .state selected (by simp)

/-- Operand annotations are inferred from the mapped source context. The
source body is not re-supplied for each Word/BV32 annotation layout. -/
theorem ScalarFrame.evidence (frame : ScalarFrame env Δ ctx p σ τ)
    (source : Scalar Γ raw annotation) (related : Context.Related Γ Δ)
    (library : ScopedSyntax.Library env) (closed : ClosedConstantTypes env) :
    LexicalScalarCode.Evidence env ctx (σ.apply raw) := by
  obtain ⟨actual,retyped⟩ := source.retag related
  obtain ⟨core,rep,typed,shape⟩ := retyped.evidenceMapped library closed frame.typed
    frame.represented (fun _ _ found => frame.scalarShape found)
  exact ⟨core,actual,by simpa only [Substitution.apply_eq] using rep,typed,shape⟩

/-- Restrict an interpreted lexical environment to its outer slots. This is
used both when retaining an argument and when recovering captured variables;
it does not create a second source-body derivation. -/
theorem ScalarFrame.tail (frame : ScalarFrame env (slot::Γ) ctx p σ τ) :
    ScalarFrame env Γ ctx p (.bindings (fun n => σ.reference (n+1))) (fun n => τ (n+1)) := by
  refine ⟨?_,fun n => frame.represented (n+1),?_,?_,?_⟩
  · intro n ty found
    obtain ⟨value,selected,rfl⟩ := Context.lookup_origin found
    have lookup : Lookup (Context.core (slot::Γ)) (n+1) value.core := by
      simpa only [Context.core,List.map_cons,value.closed.lift_eq] using
        (Lookup.succ (A := slot.core) found)
    simpa only [substitute_closed value.closed] using frame.typed _ _ lookup
  · intro n parameter found notUnit
    exact frame.valueReference (n+1) parameter found notUnit
  · intro n annotation found
    exact frame.scalar (n+1) annotation found
  · intro n found
    exact frame.natural (n+1) found

/-- Bind a value already retained at the call site. This changes only the
source-variable environment, not the target context or the current State. -/
theorem ScalarFrame.bindHeld (frame : ScalarFrame env Γ ctx p σ τ)
    (parameter : Parameter) (represented : Represents value core)
    (typed : CastTyping env 0 (SourceCasts env) ctx core parameter.core)
    (reference : parameter ≠ .unit → ∃ index, value = .bvar index)
    (scalar : ∀ annotation, parameter = .scalar annotation → LexicalScalarSyntax.Form env ctx p [] value)
    (natural : parameter = .natural → LexicalScalarSyntax.Form env ctx p [] (NaturalScope.nativeIndex value)) :
    ScalarFrame env (.value parameter::Γ) ctx p
      (.bindings (fun n => match n with | 0 => value | n+1 => σ.reference n))
      (fun n => match n with | 0 => core | n+1 => τ n) := by
  refine ⟨frame.typed.consClosed typed parameter.closed,?_,?_,?_,?_⟩
  · intro n; cases n with
    | zero => exact represented
    | succ n => exact frame.represented n
  · intro n actual found notUnit
    cases n with
    | zero =>
      have same : parameter = actual := by simpa using found
      subst actual
      exact reference notUnit
    | succ n => exact frame.valueReference n actual found notUnit
  · intro n annotation found
    cases n with
    | zero => exact scalar annotation (by simpa using found)
    | succ n => exact frame.scalar n annotation found
  · intro n found
    cases n with
    | zero => exact natural (by simpa using found)
    | succ n => exact frame.natural n found

/-- The ordinary State-only entrance supplies the environment automatically. -/
theorem ScalarFrame.initial : ScalarFrame env [.value .state] context parameters .identity VExpr.bvar := by
  refine ⟨initialMapping,fun _ => .bvar,?_,?_,?_⟩
  · intro n parameter found notUnit
    cases n with
    | zero => exact ⟨0,rfl⟩
    | succ n => simp at found
  · intro n annotation found
    cases n <;> simp at found
  · intro n found
    cases n <;> simp at found

/-- Reuse the established scalar cache substitution proof to open a body.
The cache reference and the new retained variable denote the same value. -/
theorem openScalarForm (form : LexicalScalarSyntax.Form env ctx p [] raw)
    (references : ReferenceScope p) :
    LexicalScalarSyntax.Form env ctx p (LexicalScalarCode.sources (LexicalScalarCode.openValues []))
      (LexicalScalarCode.openBody [] raw) := by
  have mapped := form.substituteCache references
    (target := [.bvar 0]) (σ := fun n => .bvar (if n < 1 then n else n+1))
    (by intro n value found; simp at found)
    (by
      intro n
      cases n with
      | zero => rfl
      | succ n => simp [LexicalScalarSyntax.expand,LeanBindings.substitute,LexicalScalarSyntax.sourceReference])
  simpa only [LeanBindings.substitute_bvars,LexicalScalarCode.openBody,
    List.length_nil,Nat.zero_add,LexicalScalarCode.sources,LexicalScalarCode.openValues,List.map_nil,List.map_cons]
    using mapped

private theorem reference_lift_notZero (shape : ReferenceShape raw) :
    sameTerm (.bvar 0) (LeanBindings.rename Nat.succ raw) = false := by
  obtain ⟨n,rfl|rfl⟩ := shape
  · rfl
  · rfl

/-- A fresh retained scalar is the first local; old scalar references are
lifted using the existing common scalar-form transport. -/
theorem ScalarFrame.underScalar (frame : ScalarFrame env Γ ctx p σ τ)
    (closed : ClosedConstantTypes env) (inputs : InputsTyped env ctx p)
    (typing : LexicalScalarCode.ScopeTyped env ctx p) (references : ReferenceScope p)
    (annotation : WordBinder.Annotation) :
    ScalarFrame env (.value (.scalar annotation)::Γ) (annotation.core::ctx)
      {p.lift with locals := .bvar 0::p.lift.locals} (under σ) (coreUnder τ) := by
  refine ⟨frame.typed.underClosed closed _ annotation.closed,
    by simpa only [under_reference] using mappingUnderRepresented frame.represented,?_,?_,?_⟩
  · intro n parameter found notUnit
    cases n with
    | zero => exact ⟨0,by simp [under_reference,LeanBindings.underSubst]⟩
    | succ n =>
      obtain ⟨index,equal⟩ := frame.valueReference n parameter found notUnit
      exact ⟨index+1,by simp [under_reference,LeanBindings.underSubst,equal,LeanBindings.rename]⟩
  · intro n actual found
    cases n with
    | zero =>
      rw [under_reference]
      exact .localValue ⟨(by intros; intro h; cases h),(by intros; intro h; cases h)⟩ 0 rfl
        (reference_lift_notZero references.index) (reference_lift_notZero references.left)
        (reference_lift_notZero references.right) (by omega)
    | succ n =>
      simpa only [under_reference,LeanBindings.underSubst,List.map_nil,List.length_nil,
        liftVar,Nat.not_lt_zero,ite_false,Nat.add_comm] using
        (frame.scalar n actual found).liftScalar closed inputs typing references annotation.core
  · intro n found
    cases n with
    | zero => simp at found
    | succ n =>
      have lifted := (frame.natural n found).liftScalar closed inputs typing references annotation.core
      simpa only [under_reference,LeanBindings.underSubst,List.map_nil,List.length_nil,
        liftVar,Nat.not_lt_zero,ite_false,Nat.add_comm] using lifted

private theorem referenceOccurrence (shape : ReferenceShape raw) : LocalOccurrence raw := by
  obtain ⟨n,rfl|rfl⟩ := shape
  all_goals exact ⟨(by intros; intro h; cases h),(by intros; intro h; cases h)⟩

private theorem referenceNoHead (shape : ReferenceShape raw)
    (head : raw.getAppFn.constName? = some name) (different : name ≠ ``BitVec.ofNat) : False := by
  obtain ⟨n,rfl|rfl⟩ := shape
  · cases head
  · exact different (Option.some.inj head).symm

/-- State and Unit binders move existing value references without adding a
scalar local. This is reference transport; register expressions are rebuilt
against the current State by the original-source induction. -/
theorem liftReferenceForm (form : LexicalScalarSyntax.Form env ctx p [] raw)
    (shape : ReferenceShape raw) (inputs : InputsTyped env ctx p)
    (typing : LexicalScalarCode.ScopeTyped env ctx p) (binder : VExpr) (nextState : Lean.Expr) :
    LexicalScalarSyntax.Form env (binder::ctx) {p.lift with s := nextState} []
      (LeanBindings.rename Nat.succ raw) := by
  cases form with
  | reference found => simp at found
  | index occurrence same =>
    apply LexicalScalarSyntax.Form.index (referenceOccurrence shape.lift)
    simpa only [LexicalScalarSyntax.expand_nil,Inputs.lift] using congrArg (LeanBindings.rename Nat.succ) same
  | parameter side occurrence same ni nl =>
    have sideLift : side.source {p.lift with s := nextState} = LeanBindings.rename Nat.succ (side.source p) := by
      cases side <;> rfl
    refine .parameter side (referenceOccurrence shape.lift) ?_ ?_ ?_
    · simpa only [LexicalScalarSyntax.expand_nil,sideLift] using congrArg (LeanBindings.rename Nat.succ) same
    · change sameTerm (side.source {p.lift with s := nextState}) (LeanBindings.rename Nat.succ p.i) = false
      rw [sideLift,LexicalScalarSyntax.sameTerm_lift (side.representation inputs).property inputs.i.property]
      exact ni
    · intro sideEq
      change sameTerm (side.source {p.lift with s := nextState}) (LeanBindings.rename Nat.succ p.x) = false
      rw [sideLift,LexicalScalarSyntax.sameTerm_lift (side.representation inputs).property inputs.x.property]
      exact nl sideEq
  | localValue occurrence k selected ni nl nr first =>
    simp only [LexicalScalarSyntax.expand_nil] at selected ni nl nr first
    obtain ⟨core,a,rep,typed,vf⟩ := typing.locals _ (List.mem_of_getElem? selected)
    refine .localValue (referenceOccurrence shape.lift) k ?_ ?_ ?_ ?_ ?_
    · simpa only [Inputs.lift,List.getElem?_map,selected,Option.map_some,LexicalScalarSyntax.expand_nil]
    · simpa only [LexicalScalarSyntax.expand_nil,Inputs.lift,LexicalScalarSyntax.sameTerm_lift rep inputs.i.property] using ni
    · simpa only [LexicalScalarSyntax.expand_nil,Inputs.lift,LexicalScalarSyntax.sameTerm_lift rep inputs.x.property] using nl
    · simpa only [LexicalScalarSyntax.expand_nil,Inputs.lift,LexicalScalarSyntax.sameTerm_lift rep inputs.y.property] using nr
    · intro j hj
      change (((p.locals.map (LeanBindings.rename Nat.succ))[j]?).map (sameTerm _)).getD false = false
      rw [List.getElem?_map]
      cases found : p.locals[j]? with
      | none => rfl
      | some e =>
        obtain ⟨other,oa,er,et,ef⟩ := typing.locals e (List.mem_of_getElem? found)
        simpa only [found,Option.map_some,Option.getD_some,LexicalScalarSyntax.expand_nil,
          LexicalScalarSyntax.sameTerm_lift rep er] using first j hj
  | literal => exact False.elim (referenceNoHead shape rfl (by decide))
  | annotatedLiteral annotation n scope => exact False.elim (referenceNoHead shape rfl (by decide))
  | binary op left right scope => exact False.elim (referenceNoHead shape rfl (by cases op <;> decide))
  | annotatedBinary op aa ab ac ad oa ob left right lr rr lt rt lf rf scope =>
    exact False.elim (referenceNoHead shape rfl (by cases op <;> decide))
  | neg => exact False.elim (referenceNoHead shape rfl (by decide))
  | annotatedNeg => exact False.elim (referenceNoHead shape rfl (by decide))
  | register => exact False.elim (referenceNoHead shape rfl (by decide))
  | select => exact False.elim (referenceNoHead shape rfl (by decide))
  | annotatedSelect => exact False.elim (referenceNoHead shape rfl (by decide))
  | letValue => exact False.elim ((referenceOccurrence shape).notLet _ _ _ _ _ rfl)
  | beta => exact False.elim ((referenceOccurrence shape).notBeta _ _ _ _ _ rfl)

/-- Add a distinct retained reference without reinterpreting any old value.
This is shared by natural loop counters and other retained parameter layouts. -/
theorem prependReferenceForm (form : LexicalScalarSyntax.Form env ctx p [] raw)
    (shape : ReferenceShape raw) (apart : sameTerm raw value = false) :
    LexicalScalarSyntax.Form env ctx {p with locals := value::p.locals} [] raw := by
  cases form with
  | reference found => simp at found
  | index occurrence same => exact .index occurrence same
  | parameter side occurrence same ni nl => exact .parameter side occurrence same ni nl
  | localValue occurrence k selected ni nl nr first =>
    refine .localValue occurrence (k+1) selected ni nl nr ?_
    intro j hj
    cases j with
    | zero => simpa only [List.getElem?_cons_zero,Option.map_some,Option.getD_some,
        LexicalScalarSyntax.expand_nil] using apart
    | succ j => exact first j (by omega)
  | literal => exact False.elim (referenceNoHead shape rfl (by decide))
  | annotatedLiteral annotation n scope => exact False.elim (referenceNoHead shape rfl (by decide))
  | binary op left right scope => exact False.elim (referenceNoHead shape rfl (by cases op <;> decide))
  | annotatedBinary op aa ab ac ad oa ob left right lr rr lt rt lf rf scope =>
    exact False.elim (referenceNoHead shape rfl (by cases op <;> decide))
  | neg => exact False.elim (referenceNoHead shape rfl (by decide))
  | annotatedNeg => exact False.elim (referenceNoHead shape rfl (by decide))
  | register => exact False.elim (referenceNoHead shape rfl (by decide))
  | select => exact False.elim (referenceNoHead shape rfl (by decide))
  | annotatedSelect => exact False.elim (referenceNoHead shape rfl (by decide))
  | letValue => exact False.elim ((referenceOccurrence shape).notLet _ _ _ _ _ rfl)
  | beta => exact False.elim ((referenceOccurrence shape).notBeta _ _ _ _ _ rfl)

private theorem naturalZero_apart_lift (shape : ReferenceShape raw) :
    sameTerm (NaturalScope.nativeIndex (.bvar 0)) (LeanBindings.rename Nat.succ raw) = false := by
  obtain ⟨n,rfl|rfl⟩ := shape
  · rfl
  · change sameTerm (NaturalScope.nativeIndex (.bvar 0)) (NaturalScope.nativeIndex (.bvar (n+1))) = false
    cases eq : sameTerm (NaturalScope.nativeIndex (.bvar 0)) (NaturalScope.nativeIndex (.bvar (n+1))) with
    | false => rfl
    | true =>
      have h := sameTerm_sound (NaturalScope.index_represents (Represents.bvar (n := 0)))
        (NaturalScope.index_represents (Represents.bvar (n := n+1))) eq
      simp [NaturalScope.index,applications] at h

private theorem lift_apart_naturalZero (shape : ReferenceShape raw) :
    sameTerm (LeanBindings.rename Nat.succ raw) (NaturalScope.nativeIndex (.bvar 0)) = false := by
  obtain ⟨n,rfl|rfl⟩ := shape
  · rfl
  · change sameTerm (NaturalScope.nativeIndex (.bvar (n+1))) (NaturalScope.nativeIndex (.bvar 0)) = false
    cases eq : sameTerm (NaturalScope.nativeIndex (.bvar (n+1))) (NaturalScope.nativeIndex (.bvar 0)) with
    | false => rfl
    | true =>
      have h := sameTerm_sound (NaturalScope.index_represents (Represents.bvar (n := n+1)))
        (NaturalScope.index_represents (Represents.bvar (n := 0))) eq
      simp [NaturalScope.index,applications] at h

/-- A natural counter remains Nat in the source environment. Its conversion
to BV32 is a retained scalar reference, exactly as in the existing frontend. -/
theorem ScalarFrame.underNatural (frame : ScalarFrame env Γ ctx p σ τ)
    (closed : ClosedConstantTypes env) (inputs : InputsTyped env ctx p)
    (typing : LexicalScalarCode.ScopeTyped env ctx p) (references : ReferenceScope p) :
    ScalarFrame env (.value .natural::Γ) (natType::ctx)
      {p.lift with locals := NaturalScope.nativeIndex (.bvar 0)::p.lift.locals}
      (under σ) (coreUnder τ) := by
  obtain ⟨types,reps⟩ := openParameterMapping frame.typed frame.represented closed .natural
  refine ⟨types,reps,?_,?_,?_⟩
  · intro n parameter found notUnit
    cases n with
    | zero => exact ⟨0,by cases σ <;> rfl⟩
    | succ n =>
      obtain ⟨index,equal⟩ := frame.valueReference n parameter found notUnit
      exact ⟨index+1,by simp [under_reference,LeanBindings.underSubst,equal,LeanBindings.rename]⟩
  · intro n annotation found
    cases n with
    | zero => simp at found
    | succ n =>
      obtain ⟨index,equal⟩ := frame.valueReference n (.scalar annotation) found (by simp)
      have shape : ReferenceShape (σ.reference n) := ⟨index,Or.inl equal⟩
      have lifted := liftReferenceForm (frame.scalar n annotation found) shape inputs typing natType p.lift.s
      simpa only [under_reference,LeanBindings.underSubst] using
        prependReferenceForm lifted shape.lift (lift_apart_naturalZero shape)
  · intro n found
    cases n with
    | zero =>
      have eq : (under σ).reference 0 = .bvar 0 := by cases σ <;> rfl
      rw [eq]
      exact .localValue (referenceOccurrence ⟨0,Or.inr rfl⟩) 0 rfl
        (naturalZero_apart_lift references.index) (naturalZero_apart_lift references.left)
        (naturalZero_apart_lift references.right) (by omega)
    | succ n =>
      obtain ⟨index,equal⟩ := frame.valueReference n .natural found (by simp)
      have shape : ReferenceShape (NaturalScope.nativeIndex (σ.reference n)) := by
        rw [equal]; exact ⟨index,Or.inr rfl⟩
      have lifted := liftReferenceForm (frame.natural n found) shape inputs typing natType p.lift.s
      simpa only [under_reference,LeanBindings.underSubst] using
        prependReferenceForm lifted shape.lift (lift_apart_naturalZero shape)

/-- State and administrative Unit bindings reuse reference transport. In
particular, held scalar values survive a change of the current State. -/
theorem ScalarFrame.underAdministrative (frame : ScalarFrame env Γ ctx p σ τ)
    (closed : ClosedConstantTypes env) (inputs : InputsTyped env ctx p)
    (typing : LexicalScalarCode.ScopeTyped env ctx p) (parameter : Parameter)
    (administrative : parameter = .state ∨ parameter = .unit) (nextState : Lean.Expr) :
    ScalarFrame env (.value parameter::Γ) (parameter.core::ctx)
      {p.lift with s := nextState} (under σ) (coreUnder τ) := by
  obtain ⟨types,reps⟩ := openParameterMapping frame.typed frame.represented closed parameter
  refine ⟨types,reps,?_,?_,?_⟩
  · intro n parameter found notUnit
    cases n with
    | zero => exact ⟨0,by cases σ <;> rfl⟩
    | succ n =>
      obtain ⟨index,equal⟩ := frame.valueReference n parameter found notUnit
      exact ⟨index+1,by simp [under_reference,LeanBindings.underSubst,equal,LeanBindings.rename]⟩
  · intro n annotation found
    cases n with
    | zero => rcases administrative with rfl | rfl <;> simp at found
    | succ n =>
      obtain ⟨index,equal⟩ := frame.valueReference n (.scalar annotation) found (by simp)
      have shape : ReferenceShape (σ.reference n) := ⟨index,Or.inl equal⟩
      simpa only [under_reference,LeanBindings.underSubst] using
        liftReferenceForm (frame.scalar n annotation found) shape inputs typing parameter.core nextState
  · intro n found
    cases n with
    | zero => rcases administrative with rfl | rfl <;> simp at found
    | succ n =>
      obtain ⟨index,equal⟩ := frame.valueReference n .natural found (by simp)
      have shape : ReferenceShape (NaturalScope.nativeIndex (σ.reference n)) := by
        rw [equal]; exact ⟨index,Or.inr rfl⟩
      simpa only [under_reference,LeanBindings.underSubst] using
        liftReferenceForm (frame.natural n found) shape inputs typing parameter.core nextState

theorem ScalarFrame.underState (frame : ScalarFrame env Γ ctx p σ τ)
    (closed : ClosedConstantTypes env) (inputs : InputsTyped env ctx p)
    (typing : LexicalScalarCode.ScopeTyped env ctx p) :
    ScalarFrame env (.value .state::Γ) (stateType::ctx)
      {p.lift with s := .bvar 0} (under σ) (coreUnder τ) :=
  frame.underAdministrative closed inputs typing .state (Or.inl rfl) (.bvar 0)

theorem ScalarFrame.underUnit (frame : ScalarFrame env Γ ctx p σ τ)
    (closed : ClosedConstantTypes env) (inputs : InputsTyped env ctx p)
    (typing : LexicalScalarCode.ScopeTyped env ctx p) :
    ScalarFrame env (.value .unit::Γ) (UnitStep.unitType::ctx)
      p.lift (under σ) (coreUnder τ) :=
  frame.underAdministrative closed inputs typing .unit (Or.inr rfl) p.lift.s

/-- Static range loops compose the already established scalar and State
bindings; no extra rule for a normalized or expanded loop body is needed. -/
theorem ScalarFrame.underStaticRange (frame : ScalarFrame env Γ ctx p σ τ)
    (library : ScopedSyntax.Library env) (closed : ClosedConstantTypes env)
    (inputs : InputsTyped env ctx p) (typing : LexicalScalarCode.ScopeTyped env ctx p)
    (references : ReferenceScope p) :
    ScalarFrame env (.value .state::.value (.scalar .word)::Γ) (stateType::wordType::ctx)
      (For.parameters p) (under (under σ)) (coreUnder (coreUnder τ)) := by
  simpa only [For.parameters,Inputs.lift,List.map_cons,LeanBindings.rename] using
    (frame.underScalar closed inputs typing references .word).underState closed
      (WordBinder.Annotation.word.nextInputs inputs closed library.scalars.toSignatures library.cons)
      (typing.nextWord closed .word)

/-- The two iterator forms differ only in the order of their native Nat and
State binders. Both use the same source environment construction. -/
theorem ScalarFrame.underNaturalRange (frame : ScalarFrame env Γ ctx p σ τ)
    (library : ScopedSyntax.Library env) (closed : ClosedConstantTypes env)
    (inputs : InputsTyped env ctx p) (typing : LexicalScalarCode.ScopeTyped env ctx p)
    (references : ReferenceScope p) (kind : NaturalLoop.Kind) :
    ScalarFrame env (rangeContext kind Γ) (kind.context ctx) (kind.parameters p)
      (under (under σ)) (coreUnder (coreUnder τ)) := by
  cases kind with
  | forIn =>
    have natInputs := NaturalScope.retain (inputs.lift closed natType)
      library.scalars.toSignatures library.naturalLoops.ofNat library.cons
      (Represents.bvar (n := 0)) (DirectTyping.bvar Lookup.zero)
    have natTyping := (typing.lift closed natType).withLocal
      (LexicalScalarCode.Evidence.naturalIndex library.scalars.toSignatures
        library.naturalLoops.ofNat (Represents.bvar (n := 0)) (DirectTyping.bvar Lookup.zero))
    simpa only [rangeContext,NaturalLoop.Kind.context,NaturalLoop.Kind.first,NaturalLoop.Kind.second,
      NaturalLoop.Kind.parameters,NaturalScope.forInParameters,Inputs.lift,List.map_cons,
      NaturalScope.nativeIndex,app,LeanBindings.rename,List.foldl_cons,List.foldl_nil] using
      (frame.underNatural closed inputs typing references).underState closed natInputs natTyping
  | fold =>
    simpa only [rangeContext,NaturalLoop.Kind.context,NaturalLoop.Kind.first,NaturalLoop.Kind.second,
      NaturalLoop.Kind.parameters,NaturalScope.foldParameters,Inputs.lift] using
      (frame.underState closed inputs typing).underNatural closed
        (inputs.nextState closed) (typing.nextState closed) references.state

/-- Existing binder layouts, used only to track later lexical bindings of a
captured helper. This does not add a runtime IR or a source construct. -/
def Parameter.extendInputs (parameter : Parameter) (p : Inputs) : Inputs :=
  match parameter with
  | .scalar _ => {p.lift with locals := .bvar 0::p.lift.locals}
  | .state => {p.lift with s := .bvar 0}
  | .natural => {p.lift with locals := NaturalScope.nativeIndex (.bvar 0)::p.lift.locals}
  | .unit => p.lift

theorem ScalarFrame.openParameter (frame : ScalarFrame env Γ ctx p σ τ)
    (closed : ClosedConstantTypes env) (inputs : InputsTyped env ctx p)
    (typing : LexicalScalarCode.ScopeTyped env ctx p) (references : ReferenceScope p)
    (parameter : Parameter) :
    ScalarFrame env (.value parameter::Γ) (parameter.core::ctx)
      (parameter.extendInputs p) (under σ) (coreUnder τ) := by
  cases parameter with
  | scalar a => exact frame.underScalar closed inputs typing references a
  | state => exact frame.underState closed inputs typing
  | natural => exact frame.underNatural closed inputs typing references
  | unit => exact frame.underUnit closed inputs typing

/-- Retaining an actual argument extends the target context, but leaves the
original captured source context unchanged. This reuses ordinary binder
extension followed by the shared restriction to outer slots. -/
theorem ScalarFrame.shiftTarget (frame : ScalarFrame env Γ ctx p σ τ)
    (closed : ClosedConstantTypes env) (inputs : InputsTyped env ctx p)
    (typing : LexicalScalarCode.ScopeTyped env ctx p) (references : ReferenceScope p)
    (parameter : Parameter) :
    ScalarFrame env Γ (parameter.core::ctx) (parameter.extendInputs p)
      (.bindings (fun n => LeanBindings.rename Nat.succ (σ.reference n)))
      (fun n => (τ n).lift) := by
  simpa only [under_reference,LeanBindings.underSubst,coreUnder] using
    (frame.openParameter closed inputs typing references parameter).tail

theorem Parameter.extendTyped (parameter : Parameter) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (inputs : InputsTyped env ctx p)
    (typing : LexicalScalarCode.ScopeTyped env ctx p) (references : ReferenceScope p) :
    Nonempty (InputsTyped env (parameter.core::ctx) (parameter.extendInputs p)) ∧
      LexicalScalarCode.ScopeTyped env (parameter.core::ctx) (parameter.extendInputs p) ∧
      ReferenceScope (parameter.extendInputs p) := by
  cases parameter with
  | scalar a => exact ⟨⟨a.nextInputs inputs closed library.scalars.toSignatures library.cons⟩,
      typing.nextWord closed a,references.scalar⟩
  | state => exact ⟨⟨inputs.nextState closed⟩,typing.nextState closed,references.state⟩
  | unit => exact ⟨⟨inputs.lift closed UnitStep.unitType⟩,typing.lift closed UnitStep.unitType,references.lift⟩
  | natural =>
    refine ⟨⟨NaturalScope.retain (inputs.lift closed natType) library.scalars.toSignatures
      library.naturalLoops.ofNat library.cons (Represents.bvar (n := 0)) (.bvar .zero)⟩,
      (typing.lift closed natType).withLocal
        (.naturalIndex library.scalars.toSignatures library.naturalLoops.ofNat
          (Represents.bvar (n := 0)) (.bvar .zero)),?_⟩
    refine ⟨references.lift.index,references.lift.left,references.lift.right,?_⟩
    intro e member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨0,Or.inr rfl⟩
    · exact references.lift.locals e member

/-- Function lets extend the original lexical context without creating a
runtime value binder. The mapped function type is derived from its source. -/
theorem ScalarFrame.bindFunction (frame : ScalarFrame env Δ ctx p σ τ)
    (source : Function ds Γ raw signature) (related : Context.Related Γ Δ)
    (library : ScopedSyntax.Library env) (closed : ClosedConstantTypes env) :
    ∃ next, ScalarFrame env (.function signature::Δ) ctx p (letSubstitution σ raw) next := by
  obtain ⟨next,types,reps⟩ := (source.retag related).bindMapping library closed frame.typed frame.represented
  refine ⟨next,types,reps,?_,?_,?_⟩
  · intro n parameter found notUnit
    cases n with
    | zero => simp at found
    | succ n => exact frame.valueReference n parameter found notUnit
  · intro n annotation found
    cases n with
    | zero => simp at found
    | succ n => exact frame.scalar n annotation found
  · intro n found
    cases n with
    | zero => simp at found
    | succ n => exact frame.natural n found

/-- The existing let/beta rule consumes one opened-body family. The family
is the induction hypothesis for a single original body, not a source input.
The cache-specific body forms are derived here by the shared transport. -/
theorem scalarBindingFromRetained
    (library : ScopedSyntax.Library env) (closed : ClosedConstantTypes env)
    (inputs : InputsTyped env ctx p) (typing : LexicalScalarCode.ScopeTyped env ctx p)
    (references : ReferenceScope p) (annotation : WordBinder.Annotation)
    (value : LexicalScalarSyntax.Form env ctx p [] v)
    (valueStatic : LexicalScalarSyntax.StaticRegisters v)
    (body : ∀ a : WordBinder.Annotation,
      LexicalScalarSyntax.Form env (a.core::ctx) {p.lift with locals := .bvar 0::p.lift.locals} [] rest)
    (bodyStatic : LexicalScalarSyntax.StaticRegisters rest) :
    (∀ binder flag, LexicalScalarSyntax.Form env ctx p [] (.letE binder annotation.native v rest flag)) ∧
    (∀ binder info, LexicalScalarSyntax.Form env ctx p [] (.app (.lam binder annotation.native rest info) v)) := by
  have opened : ∀ a : WordBinder.Annotation,
      LexicalScalarSyntax.Form env (a.core::ctx) {p.lift with locals := .bvar 0::p.lift.locals}
        (LexicalScalarCode.sources (LexicalScalarCode.openValues [])) (LexicalScalarCode.openBody [] rest) :=
    fun a => openScalarForm (body a) references.scalar
  obtain ⟨next,openTyped⟩ := value.bindingFromOpen library.scalars library.decisions closed inputs typing references
    (vs := []) (by intro value member; cases member) annotation valueStatic opened bodyStatic
  exact ⟨fun binder flag => value.letFromTyping library.scalars library.decisions inputs typing
      (by intro value member; cases member) annotation valueStatic next bodyStatic openTyped binder flag,
    fun binder info => value.betaFromTyping library.scalars library.decisions inputs typing
      (by intro value member; cases member) annotation valueStatic next bodyStatic openTyped binder info⟩

/-- Interpret one original scalar derivation. The induction constructs all
opened let/beta bodies itself, including every compatible annotation layout. -/
theorem Scalar.forms (source : Scalar Γ raw annotation) :
    ∀ {Δ : Context} {ctx : List VExpr} {p : Inputs} {σ : Substitution} {τ : Nat → VExpr},
      Context.Related Γ Δ → ScalarFrame env Δ ctx p σ τ →
      (library : ScopedSyntax.Library env) → ClosedConstantTypes env →
      InputsTyped env ctx p → LexicalScalarCode.ScopeTyped env ctx p → ReferenceScope p →
      CurrentMapping σ p (stateVariables Γ raw) →
      LexicalScalarSyntax.Form env ctx p [] (σ.apply raw) ∧
        LexicalScalarSyntax.StaticRegisters (σ.apply raw) := by
  induction source with
  | «variable» found =>
    intro Δ ctx p σ τ related frame library closed inputs typing refs current
    obtain ⟨slot,selected,same⟩ := related.lookup found
    cases same with
    | scalar a b =>
      obtain ⟨index,reference⟩ := frame.valueReference _ (.scalar b) selected (by simp)
      refine ⟨by simpa only [Substitution.apply_eq,LeanBindings.substitute] using frame.scalar _ b selected,?_⟩
      simp only [Substitution.apply_eq,LeanBindings.substitute,reference,LexicalScalarSyntax.StaticRegisters]
  | literal a n =>
    intro Δ ctx p σ τ related frame library closed inputs typing refs current
    have mapped : σ.apply (AnnotatedLiteral.native a n) = AnnotatedLiteral.native a n := by cases σ <;> cases a <;> rfl
    rw [mapped]
    refine ⟨.annotatedLiteral a n (refs.separated rfl (by decide)),?_⟩
    cases a <;> trivial
  | @register Γ st state register rn =>
    intro Δ ctx p σ τ related frame library closed inputs typing refs current
    have stCurrent := state.current current.appLeft.appRight
    obtain ⟨position,stRef⟩ := state.mappedReference related frame
    have pRef : p.s = .bvar position := stCurrent.symm.trans stRef
    have mapped : σ.apply (app ``HybridWord.State.regs [st,rn.native register]) =
        app ``HybridWord.State.regs [p.s,rn.native register] := by
      have eq := congrArg (fun s => app ``HybridWord.State.regs [s,rn.native register]) stCurrent
      cases σ <;> cases rn <;> simpa only [Substitution.apply,app,List.foldl_cons,List.foldl_nil,
        LeanBindings.substitute,NatNotation.native,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB] using eq
    rw [mapped]
    refine ⟨.register (by simp) (by simpa using rn.argument library.scalars.toSignatures register)
      (by simpa using refs.separated (e := app ``HybridWord.State.regs [p.s,rn.native register]) rfl (by decide)),?_⟩
    change Nonempty (NatNotation.View (rn.native register)) ∧ LexicalScalarSyntax.StaticRegisters p.s
    exact ⟨⟨⟨register,rn,rfl⟩⟩,by rw [pRef]; trivial⟩
  | @natural Γ originalIndex found =>
    intro Δ ctx p σ τ related frame library closed inputs typing refs current
    obtain ⟨slot,selected,same⟩ := related.lookup found
    cases same
    obtain ⟨index,reference⟩ := frame.valueReference _ .natural selected (by simp)
    have mapped : σ.apply (NaturalScope.nativeIndex (.bvar originalIndex)) = NaturalScope.nativeIndex (σ.reference originalIndex) := by cases σ <;> rfl
    rw [mapped]
    exact ⟨frame.natural _ selected,by rw [reference]; trivial⟩
  | @binary Γ a leftType b rightType op aa ab ac ad left right il ir =>
    intro Δ ctx p σ τ related frame library closed inputs typing refs current
    obtain ⟨lf,ls⟩ := il related frame library closed inputs typing refs current.appLeft.appRight
    obtain ⟨rf,rs⟩ := ir related frame library closed inputs typing refs current.appRight
    obtain ⟨lc,la,lr,lt,lshape⟩ := frame.evidence left related library closed
    obtain ⟨rc,ra,rr,rt,rshape⟩ := frame.evidence right related library closed
    have mapped : σ.apply (Lean.mkApp2 (AnnotatedBinary.nativeHeader op aa ab ac ad) a b) =
        Lean.mkApp2 (AnnotatedBinary.nativeHeader op aa ab ac ad) (σ.apply a) (σ.apply b) := by
      cases σ <;> cases aa <;> cases ab <;> cases ac <;> cases ad <;> rfl
    rw [mapped]
    refine ⟨.annotatedBinary op aa ab ac ad la ra lf rf (by simpa using lr) (by simpa using rr) lt rt lshape rshape
      (by simpa using refs.separated (e := Lean.mkApp2 (AnnotatedBinary.nativeHeader op aa ab ac ad) (σ.apply a) (σ.apply b)) rfl (by cases op <;> decide)),?_⟩
    cases op <;> cases aa <;> cases ab <;> cases ac <;> cases ad <;> exact ⟨⟨by trivial,ls⟩,rs⟩
  | @neg Γ v actual a value ih =>
    intro Δ ctx p σ τ related frame library closed inputs typing refs current
    obtain ⟨vf,vs⟩ := ih related frame library closed inputs typing refs current.appRight
    obtain ⟨vc,va,vr,vt,vshape⟩ := frame.evidence value related library closed
    have mapped : σ.apply (.app (AnnotatedNeg.nativeHeader a) v) = .app (AnnotatedNeg.nativeHeader a) (σ.apply v) := by
      cases σ <;> cases a <;> rfl
    rw [mapped]
    refine ⟨.annotatedNeg a va vf (by simpa using vr) vt vshape
      (by simpa using refs.separated (e := .app (AnnotatedNeg.nativeHeader a) (σ.apply v)) rfl (by decide)),?_⟩
    cases a <;> exact ⟨by trivial,vs⟩
  | @select Γ v va a aa b ba ra ca guard yes no ig iy ino =>
    intro Δ ctx p σ τ related frame library closed inputs typing refs current
    obtain ⟨gf,gs⟩ := ig related frame library closed inputs typing refs
      current.appLeft.appLeft.appLeft.appRight.appLeft.appRight.appLeft.appRight
    obtain ⟨af,ast⟩ := iy related frame library closed inputs typing refs current.appLeft.appRight
    obtain ⟨bf,bst⟩ := ino related frame library closed inputs typing refs current.appRight
    obtain ⟨gc,ga,gr,gt,gshape⟩ := frame.evidence guard related library closed
    obtain ⟨ac,aa,ar,at_,ashape⟩ := frame.evidence yes related library closed
    obtain ⟨bc,ba,br,bt,bshape⟩ := frame.evidence no related library closed
    have mapped : σ.apply (AnnotatedCondition.scalarSource ra ca v (AnnotatedCondition.nativeDecision ca v) a b) =
        AnnotatedCondition.scalarSource ra ca (σ.apply v) (AnnotatedCondition.nativeDecision ca (σ.apply v)) (σ.apply a) (σ.apply b) := by
      cases σ <;> cases ra <;> cases ca <;> rfl
    rw [mapped]
    refine ⟨.annotatedSelect ra ca ga aa ba gf af bf (by simpa using gr) (by simpa using ar) (by simpa using br)
      gt at_ bt gshape ashape bshape
      (by simpa using refs.separated (e := AnnotatedCondition.scalarSource ra ca (σ.apply v) (AnnotatedCondition.nativeDecision ca (σ.apply v)) (σ.apply a) (σ.apply b)) rfl (by decide)),?_⟩
    cases ra <;> cases ca <;> exact ⟨⟨⟨⟨by trivial,⟨⟨by trivial,⟨⟨by trivial,gs⟩,by trivial⟩⟩,by trivial⟩⟩,
      ⟨⟨by trivial,⟨⟨by trivial,gs⟩,by trivial⟩⟩,by trivial⟩⟩,ast⟩,bst⟩
  | @letValue Γ v actual b result annotation value body binder flag iv ib =>
    intro Δ ctx p σ τ related frame library closed inputs typing refs current
    rw [stateVariables_letScalar] at current
    obtain ⟨vf,vs⟩ := iv related frame library closed inputs typing refs current.left
    have childCurrent := current.right.underValue (stateVariables_typed (.value (.scalar annotation)::Γ) b) (by simp)
    have bodyForms (a : WordBinder.Annotation) := ib (.cons (.scalar annotation a) related)
      (frame.underScalar closed inputs typing refs a) library closed
      (a.nextInputs inputs closed library.scalars.toSignatures library.cons)
      (typing.nextWord closed a) refs.scalar childCurrent
    have mapped : σ.apply (WordBinder.letSource annotation binder v b flag) =
      .letE binder annotation.native (σ.apply v) ((under σ).apply b) flag := by
      exact FunctionSyntax.substitute_annotated_let σ annotation
    rw [mapped]
    exact ⟨(scalarBindingFromRetained library closed inputs typing refs annotation vf vs
      (fun a => (bodyForms a).1) (bodyForms annotation).2).1 binder flag,⟨vs,(bodyForms annotation).2⟩⟩
  | @beta Γ v actual b result annotation value body binder info iv ib =>
    intro Δ ctx p σ τ related frame library closed inputs typing refs current
    rw [stateVariables_betaScalar] at current
    obtain ⟨vf,vs⟩ := iv related frame library closed inputs typing refs current.right
    have childCurrent := current.left.underValue (stateVariables_typed (.value (.scalar annotation)::Γ) b) (by simp)
    have bodyForms (a : WordBinder.Annotation) := ib (.cons (.scalar annotation a) related)
      (frame.underScalar closed inputs typing refs a) library closed
      (a.nextInputs inputs closed library.scalars.toSignatures library.cons)
      (typing.nextWord closed a) refs.scalar childCurrent
    have mapped : σ.apply (.app (.lam binder annotation.native b info) v) =
      .app (.lam binder annotation.native ((under σ).apply b) info) (σ.apply v) := by
      simp only [Substitution.apply_eq,LeanBindings.substitute,WordBinder.Annotation.substitute_native,under_reference]
    rw [mapped]
    exact ⟨(scalarBindingFromRetained library closed inputs typing refs annotation vf vs
      (fun a => (bodyForms a).1) (bodyForms annotation).2).2 binder info,⟨(bodyForms annotation).2,vs⟩⟩

end IRComparison.WordFrontend.OrdinarySource
