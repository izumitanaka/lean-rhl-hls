import IRComparison.Frontend.WordOrdinarySourceTyping

/-! Annotation changes of lexical scalar slots preserve the original source
judgment. In particular, a helper body is not supplied once per Word/BV32
argument front. This is proof transport, not a rewrite of the Lean program. -/
namespace IRComparison.WordFrontend.OrdinarySource
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic
set_option maxHeartbeats 2400000

inductive Slot.Related : Slot → Slot → Prop where
  | scalar (a b : WordBinder.Annotation) : Related (.value (.scalar a)) (.value (.scalar b))
  | state : Related (.value .state) (.value .state)
  | natural : Related (.value .natural) (.value .natural)
  | unit : Related (.value .unit) (.value .unit)
  | function (s : Signature) : Related (.function s) (.function s)

abbrev Context.Related (Γ Δ : Context) := List.Forall₂ Slot.Related Γ Δ

theorem Slot.Related.refl (slot : Slot) : Related slot slot := by
  cases slot with
  | function s => exact .function s
  | value p => cases p with
    | scalar a => exact .scalar a a
    | state => exact .state
    | natural => exact .natural
    | unit => exact .unit

theorem Context.Related.refl (Γ : Context) : Related Γ Γ := by
  induction Γ with
  | nil => exact .nil
  | cons s Γ ih => exact .cons (Slot.Related.refl s) ih

theorem Context.Related.lookup {index : Nat} {slot : Slot} (related : Related Γ Δ) (found : Γ[index]? = some slot) :
    ∃ other, Δ[index]? = some other ∧ Slot.Related slot other := by
  induction related generalizing index with
  | nil => simp at found
  | cons same rest ih =>
    cases index with
    | zero => cases Option.some.inj found; exact ⟨_,rfl,same⟩
    | succ index => exact ih found

theorem Context.Related.prepend (related : Related Γ Δ) (front : Context) :
    Related (front ++ Γ) (front ++ Δ) := by
  induction front with
  | nil => exact related
  | cons s rest ih => exact .cons (Slot.Related.refl s) ih

theorem StateRef.retag (source : StateRef Γ raw) (related : Context.Related Γ Δ) : StateRef Δ raw := by
  cases source with
  | «variable» found =>
    obtain ⟨other,there,same⟩ := Context.Related.lookup related found
    cases same
    exact .variable there

theorem Scalar.retag (source : Scalar Γ raw annotation) (related : Context.Related Γ Δ) :
    ∃ actual, Scalar Δ raw actual := by
  induction source generalizing Δ with
  | «variable» found =>
    obtain ⟨other,there,same⟩ := Context.Related.lookup related found
    cases same with
    | scalar a b => exact ⟨b,.variable there⟩
  | literal a n => exact ⟨_,.literal a n⟩
  | register state register rn => exact ⟨_,.register (state.retag related) register rn⟩
  | natural found =>
    obtain ⟨other,there,same⟩ := Context.Related.lookup related found
    cases same
    exact ⟨_,.natural there⟩
  | binary op aa ab ac ad left right il ir =>
    obtain ⟨_,l⟩ := il related
    obtain ⟨_,r⟩ := ir related
    exact ⟨_,.binary op aa ab ac ad l r⟩
  | neg a value ih => obtain ⟨_,v⟩ := ih related; exact ⟨_,.neg a v⟩
  | select ra ca guard yes no ig iy ino =>
    obtain ⟨_,v⟩ := ig related
    obtain ⟨_,a⟩ := iy related
    obtain ⟨_,b⟩ := ino related
    exact ⟨_,.select ra ca v a b⟩
  | letValue a value body binder flag iv ib =>
    obtain ⟨_,v⟩ := iv related
    obtain ⟨_,b⟩ := ib (.cons (.scalar a a) related)
    exact ⟨_,.letValue a v b binder flag⟩
  | beta a value body binder info iv ib =>
    obtain ⟨_,v⟩ := iv related
    obtain ⟨_,b⟩ := ib (.cons (.scalar a a) related)
    exact ⟨_,.beta a v b binder info⟩

theorem StateValue.retag (source : StateValue Γ raw) (related : Context.Related Γ Δ) : StateValue Δ raw := by
  cases source with
  | reference state => exact .reference (state.retag related)
  | set state register rn value =>
    obtain ⟨_,v⟩ := value.retag related
    exact .set (state.retag related) register rn v

theorem Read.retag (source : Read ds Γ raw annotation) (related : Context.Related Γ Δ) : Read ds Δ raw annotation := by
  cases source with
  | natural a state array index an nn declared => exact .natural annotation (state.retag related) array index an nn declared
  | word a state array an declared index =>
    obtain ⟨_,k⟩ := index.retag related
    exact .word annotation (state.retag related) array an declared k

theorem Argument.retag (source : Argument Γ parameter raw) (related : Context.Related Γ Δ) : Argument Δ parameter raw := by
  cases source with
  | scalar value => obtain ⟨_,v⟩ := value.retag related; exact .scalar v
  | state value => exact .state (value.retag related)
  | unit => exact .unit
  | unitVariable found =>
    obtain ⟨other,there,same⟩ := Context.Related.lookup related found
    cases same; exact .unitVariable there

theorem Arguments.retag (source : Arguments Γ domains raws) (related : Context.Related Γ Δ) : Arguments Δ domains raws := by
  induction source with
  | nil => exact .nil
  | cons arg rest ih => exact .cons (arg.retag related) ih

private theorem sourceRetag :
    (∀ {Γ raw signature}, Function ds Γ raw signature → ∀ {Δ}, Context.Related Γ Δ → Function ds Δ raw signature) ∧
    (∀ {Γ result raw}, Body ds Γ result raw → ∀ {Δ}, Context.Related Γ Δ → Body ds Δ result raw) := by
  refine ⟨@Function.rec ds (fun Γ raw signature _ => ∀ {Δ}, Context.Related Γ Δ → Function ds Δ raw signature) (fun Γ result raw _ => ∀ {Δ}, Context.Related Γ Δ → Body ds Δ result raw)
    ?«variable» ?lambda ?returns ?yield ?write ?copy ?letScalar ?letState ?bindState ?bindRead ?branch ?staticRange ?naturalRange ?unitSequence ?call ?letFunction,
    @Body.rec ds (fun Γ raw signature _ => ∀ {Δ}, Context.Related Γ Δ → Function ds Δ raw signature) (fun Γ result raw _ => ∀ {Δ}, Context.Related Γ Δ → Body ds Δ result raw)
    ?«variable» ?lambda ?returns ?yield ?write ?copy ?letScalar ?letState ?bindState ?bindRead ?branch ?staticRange ?naturalRange ?unitSequence ?call ?letFunction⟩
  all_goals first
    | (case «variable» =>
      intro Γ index signature found
      intro Δ related
      obtain ⟨other,there,same⟩ := Context.Related.lookup related found
      cases same
      exact .variable there)
    | (case lambda =>
      intro raw Γ original head tail result shape body ih
      intro Δ related
      exact .lambda head tail result shape (ih (Context.Related.prepend related _)))
    | (case returns =>
      intro Γ st tag value Δ related; exact .returns tag (value.retag related))
    | (case yield =>
      intro Γ st value Δ related; exact .yield (value.retag related))
    | (case write =>
      intro Γ st k ka v va state array an declared index value
      intro Δ related
      obtain ⟨_,k⟩ := index.retag related
      obtain ⟨_,v⟩ := value.retag related
      exact .write (state.retag related) array an declared k v)
    | (case copy =>
      intro Γ st state d s n dn sn nn hd hs
      intro Δ related; exact .copy (state.retag related) d s n dn sn nn hd hs)
    | (case letScalar =>
      intro Γ v actual b result a value body binder flag ih
      intro Δ related
      obtain ⟨_,v⟩ := value.retag related
      exact .letScalar result a v (ih (.cons (.scalar a a) related)) binder flag)
    | (case letState =>
      intro Γ v b result value body binder flag ih
      intro Δ related
      exact .letState result (value.retag related) (ih (.cons .state related)) binder flag)
    | (case bindState =>
      intro Γ a b result first next binder info ihf ihn
      intro Δ related
      exact .bindState result (ihf related) (ihn (.cons .state related)) binder info)
    | (case bindRead =>
      intro Γ v actual b result a read next binder info ih
      intro Δ related
      exact .bindRead result a (read.retag related) (ih (.cons (.scalar a a) related)) binder info)
    | (case branch =>
      intro Γ v actual a0 b0 result a guard yes no iy ino
      intro Δ related
      obtain ⟨_,v⟩ := guard.retag related
      exact .branch result a v (iy related) (ino related))
    | (case staticRange =>
      intro Γ st a av b bv c cv raw state start stop stride body kn tn ki ti ih
      intro Δ related
      exact .staticRange (state.retag related) start stop stride
        (ih (.cons .state (.cons (.scalar .word .word) related))) kn tn ki ti)
    | (case unitSequence =>
      intro Γ b result body binder info ih
      intro Δ related; exact .unitSequence result (ih (.cons .unit related)) binder info)
    | (case call =>
      intro Γ f head tail result first rest fn args ih Δ related; exact .call (ih related) (args.retag related))
    | (case letFunction =>
      intro signature ty Γ v result b spelling value next binder flag iv ine
      intro Δ related
      exact .letFunction spelling (iv related) (ine (.cons (.function _) related)) binder flag)
    | (case naturalRange =>
      intro Γ st n actual raw kind state count body kn tn ki ti ih
      intro Δ related
      obtain ⟨_,n⟩ := count.retag related
      have frame : Context.Related (rangeContext kind Γ) (rangeContext kind Δ) := by
        cases kind
        · exact .cons .state (.cons .natural related)
        · exact .cons .natural (.cons .state related)
      exact .naturalRange kind (state.retag related) n (ih frame) kn tn ki ti)

theorem Function.retag (source : Function ds Γ raw signature) (related : Context.Related Γ Δ) : Function ds Δ raw signature :=
  sourceRetag.1 source related

theorem Body.retag (source : Body ds Γ result raw) (related : Context.Related Γ Δ) : Body ds Δ result raw :=
  sourceRetag.2 source related

/-- The same core has a type at every compatible scalar annotation layout.
The only source-body premise is its original derivation. -/
theorem Body.typingRetagged (source : Body ds Γ result raw)
    (library : ScopedSyntax.Library env) (closed : ClosedConstantTypes env) :
    ∃ core, Represents raw core ∧ ∀ {Δ}, Context.Related Γ Δ →
      CastTyping env 0 (SourceCasts env) Δ.core core (optionType result.core) := by
  obtain ⟨core,rep,typed⟩ := source.typing library closed
  refine ⟨core,rep,?_⟩
  intro Δ related
  obtain ⟨other,repOther,typedOther⟩ := (source.retag related).typing library closed
  exact repOther.unique rep ▸ typedOther

abbrev Parameter.Related (a b : Parameter) : Prop := Slot.Related (.value a) (.value b)

theorem Context.Related.append (front : Related Γ Δ) (tail : Related Γ' Δ') :
    Related (Γ ++ Γ') (Δ ++ Δ') := by
  induction front with
  | nil => exact tail
  | cons same rest ih => exact .cons same ih

theorem Context.Related.appendSame (related : Related Γ Δ) (suffix : Context) :
    Related (Γ ++ suffix) (Δ ++ suffix) := related.append (Context.Related.refl suffix)

/-- Every intermediate argument prefix changes only scalar annotations.
State and all captured slots retain their original lexical types. -/
theorem parameterPrefixRelated (parameters : List.Forall₂ Parameter.Related declared actual) (n : Nat) :
    Context.Related (declared.map Slot.value) ((actual.take n ++ declared.drop n).map Slot.value) := by
  induction parameters generalizing n with
  | nil => simpa using (List.Forall₂.nil : Context.Related [] [])
  | cons same rest ih =>
    cases n with
    | zero => exact Context.Related.refl _
    | succ n => exact .cons same (ih n)

/-- Produce all prefix-body type obligations of the existing retained-call
rule from one original source derivation. Neither a prefix family nor an
expanded body is an input requirement here. -/
theorem Body.typingPrefixes
    (source : Body ds (declared.reverse.map Slot.value ++ Γ) result raw)
    (parameters : List.Forall₂ Parameter.Related declared actual)
    (library : ScopedSyntax.Library env) (closed : ClosedConstantTypes env) :
    ∃ core, Represents raw core ∧ ∀ n,
      CastTyping env 0 (SourceCasts env)
        (((actual.take n ++ declared.drop n).map Parameter.core).reverse ++ Γ.core)
        core (optionType result.core) := by
  obtain ⟨core,rep,types⟩ := source.typingRetagged library closed
  refine ⟨core,rep,?_⟩
  intro n
  have relation := Context.Related.appendSame
    (List.Forall₂.reverse.mpr (parameterPrefixRelated parameters n)) Γ
  have mapped : Context.Related (declared.reverse.map Slot.value ++ Γ)
      ((actual.take n ++ declared.drop n).reverse.map Slot.value ++ Γ) := by
    simpa only [List.map_reverse] using relation
  have typed := types mapped
  simpa [Context.core,List.map_append,List.map_reverse,List.map_map,Slot.core] using typed

/-- Both inferred and declared argument types are derived. The inferred
annotation determines letValue storage; the declared annotation checks the
original call. State, Nat and Unit remain exact. -/
theorem Argument.evidence (source : Argument Γ declared raw) (library : ScopedSyntax.Library env) :
    ∃ (actual : Parameter) (core : VExpr), Parameter.Related declared actual ∧ Represents raw core ∧
      CastTyping env 0 (SourceCasts env) Γ.core core actual.core ∧
      CheckedTyping env 0 (SourceCasts env) Γ.core core declared.core := by
  cases source with
  | scalar value =>
    obtain ⟨vc,vr,vt,_⟩ := value.typing library
    exact ⟨.scalar _,vc,.scalar _ _,vr,vt,WordBinder.Annotation.argument _ (WordBinder.Annotation.result _ vt)⟩
  | state value =>
    obtain ⟨vc,vr,vt⟩ := value.typing (env := env)
    exact ⟨.state,vc,.state,vr,vt.withCasts _,.exact (vt.withCasts _)⟩
  | unit => exact ⟨.unit,_,.unit,.constant rfl,library.units.value_typed.withCasts _,.exact (library.units.value_typed.withCasts _)⟩
  | unitVariable found => exact ⟨.unit,_,.unit,.bvar,.bvar (Context.lookup found),.exact (.bvar (Context.lookup found))⟩

theorem Arguments.evidence (source : Arguments Γ declared raws) (library : ScopedSyntax.Library env) :
    ∃ actual cores, List.Forall₂ Parameter.Related declared actual ∧
      List.Forall₂ Represents raws cores ∧
      List.Forall₂ (fun parameter core => CastTyping env 0 (SourceCasts env) Γ.core core parameter.core) actual cores ∧
      List.Forall₂ (fun parameter core => CheckedTyping env 0 (SourceCasts env) Γ.core core parameter.core) declared cores := by
  induction source with
  | nil => exact ⟨[],[],.nil,.nil,.nil,.nil⟩
  | cons argument rest ih =>
    obtain ⟨a,c,shape,rep,typed,checked⟩ := argument.evidence library
    obtain ⟨aa,cc,shapes,reps,types,checks⟩ := ih
    exact ⟨a::aa,c::cc,.cons shape shapes,.cons rep reps,.cons typed types,.cons checked checks⟩

end IRComparison.WordFrontend.OrdinarySource
