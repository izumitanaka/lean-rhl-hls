import IRComparison.Frontend.WordScalarEnvironment

/-! Invariant for lexical scalar bindings. The environment stores already
constructed child certificates; it is not a success predicate on the enclosing
source or a new source language. Matching references reuse those certificates. -/
namespace IRComparison.WordFrontend.ScalarEnvironment
open Lean4Lean LeanTyped LeanTypeInference Certificate
variable {env : VEnv} {ctx : List VExpr} {p : Inputs}
  {inputs : InputsTyped env ctx p} {casts proofCasts : TypeCasts}

/-- Independent typing invariant supplied by the source induction for each
previously bound value. No lookup success is required. -/
def BindingTypes (inputs : InputsTyped env ctx p)
    (casts : TypeCasts) (bindings : Bindings env ctx p)
    (proofCasts : TypeCasts := casts) : Prop :=
  ∀ b ∈ bindings, Nonempty (ScalarCasts inputs b.piece casts proofCasts)

theorem BindingTypes.empty (inputs : InputsTyped env ctx p) (casts : TypeCasts) :
    BindingTypes inputs casts [] proofCasts := by simp [BindingTypes]

theorem BindingTypes.cons {piece : Piece env ctx p source scalarExpected}
    (bindings : BindingTypes inputs casts bs proofCasts)
    (value : ScalarCasts inputs piece casts proofCasts) :
    BindingTypes inputs casts (⟨source,piece⟩ :: bs) proofCasts := by
  intro b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact ⟨value⟩
  · exact bindings b hb

/-- An identical represented type needs no conversion search, whatever its
size or lexical nesting. This is the fast path actually used by retarget. -/
theorem retarget_same_complete (artifact : Artifact env ctx previous)
    (represented : Represents expected artifact.core.val) (conv : Conversion env) :
    ∃ result, artifact.retarget conv expected = some result ∧
      result.proofCore.val = artifact.proofCore.val ∧ result.core.val = artifact.core.val := by
  obtain ⟨translated,found,same⟩ := represented.translate_complete
  simp only [Artifact.retarget,found,bind,Option.bind]
  simp only [same,dif_pos rfl,pure,Option.pure_def]
  exact ⟨_,rfl,rfl,same⟩

/-- Whether a source occurrence is outside the lexical scalar bindings. This
is a bound-variable scope condition, independent of the parser. -/
def Unbound (raw : Lean.Expr) (depth : Nat) : Prop :=
  ∀ n, raw = .bvar n → depth ≤ n

@[simp] theorem Unbound.empty (raw : Lean.Expr) : Unbound raw 0 := fun _ _ => Nat.zero_le _

theorem Unbound.lookup_none (outside : Unbound raw bindings.length) (conv : Conversion env) :
    lookup (ctx := ctx) (p := p) conv raw bindings = none := by
  cases raw <;> try rfl
  rename_i n
  have missing : bindings[n]? = none := List.getElem?_eq_none (outside n rfl)
  simp [lookup,missing]

/-- Explicit proof transport has the exact requested inferred type. The
cast premise is a syntactic conversion rule covered by the converter, never
an assumption that retarget or the enclosing parser succeeds. -/
theorem retarget_cast_complete (artifact : Artifact env ctx previous)
    (represented : Represents expected core)
    (proofTyped : CastTyping env 0 proofCasts ctx artifact.proofCore.val artifact.core.val)
    (typeTyped : CastTyping env 0 proofCasts ctx core (.sort u))
    (castRule : proofCasts ctx artifact.core.val core)
    (coverage : Conversion.Covers conv 0 proofCasts) :
    ∃ result, artifact.retarget conv expected = some result ∧
      CastTyping env 0 proofCasts ctx result.proofCore.val result.core.val := by
  obtain ⟨⟨actual,rep⟩,found,sameCore⟩ := represented.translate_complete
  dsimp only at sameCore
  subst actual
  unfold Artifact.retarget
  simp only [found,bind,Option.bind]
  by_cases same : artifact.core.val = core
  · simp only [dif_pos same,pure,Option.pure_def]
    exact ⟨_,rfl,same ▸ proofTyped⟩
  · obtain ⟨cast,accepted⟩ := coverage ctx artifact.core.val core castRule
    simp only [dif_neg same,accepted,bind,Option.bind,pure,Option.pure_def]
    refine ⟨_,rfl,?_⟩
    have identity : CastTyping env 0 proofCasts ctx (.lam core (.bvar 0)) (.forallE core core.lift) :=
      .lambda typeTyped (.bvar .zero)
    simpa only [VExpr.inst_lift] using CastTyping.convertedApplication identity proofTyped castRule

/-- A selected lexical binding preserves its generated code as well as its
typing. The lookup cannot silently choose another equal-looking source term. -/
theorem lookup_selected_complete (types : BindingTypes inputs casts bindings proofCasts)
    (selected : bindings[n]? = some bound) (conv : Conversion env) :
    ∃ piece, lookup conv (.bvar n) bindings = some piece ∧
      Nonempty (ScalarCasts inputs piece casts proofCasts) ∧ piece.code = bound.piece.code := by
  obtain ⟨typed⟩ := types bound (List.mem_of_getElem? selected)
  have sourceSame : materialize bindings (.bvar n) = bound.source := by
    rw [materialize_eq_substitute]
    simp only [LeanBindings.substitute,reference,selected]
  have represented : Represents (materialize bindings (.bvar n)) typed.sourceCore.val :=
    sourceSame.symm ▸ typed.sourceCore.property
  have expectedRep := scalarExpected_represents inputs bound.piece.represented.property represented
  have previousRep := scalarExpected_represents inputs bound.piece.represented.property typed.sourceCore.property
  have eqCore := bound.piece.checked.core.property.unique previousRep
  rw [← eqCore] at expectedRep
  obtain ⟨artifact,checked,proofSame,typeSame⟩ := retarget_same_complete bound.piece.checked expectedRep conv
  let result : Piece env ctx p (materialize bindings (.bvar n)) scalarExpected :=
    ⟨bound.piece.code,artifact,bound.piece.closed,bound.piece.represented⟩
  refine ⟨result,?_,⟨⟨⟨_,represented⟩,typed.value,typed.target,?_⟩⟩,rfl⟩
  · simp only [lookup,selected,checked,bind,Option.bind,pure,Option.pure_def]
    rfl
  · change CastTyping env 0 proofCasts ctx artifact.proofCore.val artifact.core.val
    rw [proofSame,typeSame]
    exact typed.proof

/-- Lookup is total for every well-typed binding environment. A miss merely
selects ordinary syntax traversal; it is not a source-language rejection. -/
theorem lookup_typed (types : BindingTypes inputs casts bindings proofCasts)
    (raw : Lean.Expr) (conv : Conversion env) :
    lookup conv raw bindings = none ∨
      ∃ piece, lookup conv raw bindings = some piece ∧
        Nonempty (ScalarCasts inputs piece casts proofCasts) := by
  cases raw <;> try exact Or.inl rfl
  rename_i n
  cases selected : bindings[n]? with
  | none => exact Or.inl (by simp [lookup,selected])
  | some bound =>
    obtain ⟨piece,found,typed,_⟩ := lookup_selected_complete types selected conv
    exact Or.inr ⟨piece,found,typed⟩

/-- In-scope lexical variables always retrieve an earlier binding, including
shadowed names and arbitrarily distant de Bruijn indices. -/
theorem reference_complete_code (types : BindingTypes inputs casts bindings proofCasts)
    (selected : bindings[n]? = some bound) (conv : Conversion env) (exposure : Exposure env) :
    ∃ piece, visit env conv exposure ctx p (.bvar n) bindings = some piece ∧
      Nonempty (ScalarCasts inputs piece casts proofCasts) ∧ piece.code = bound.piece.code := by
  obtain ⟨piece,found,typed,code⟩ := lookup_selected_complete types selected conv
  refine ⟨piece,?_,typed,code⟩
  rw [visit] <;> try (solve | intros; contradiction)
  simp only [found]

theorem reference_complete (types : BindingTypes inputs casts bindings proofCasts)
    (selected : bindings[n]? = some bound) (conv : Conversion env) (exposure : Exposure env) :
    ∃ piece, visit env conv exposure ctx p (.bvar n) bindings = some piece ∧
      Nonempty (ScalarCasts inputs piece casts proofCasts) := by
  obtain ⟨piece,found,typed,_⟩ := reference_complete_code types selected conv exposure
  exact ⟨piece,found,typed⟩

theorem materialize_closed (bindings : Bindings env ctx p) (closed : isClosed e = true) :
    materialize bindings e = e := by
  rw [materialize_eq_substitute]
  exact LeanBindings.substitute_closed e closed _

end IRComparison.WordFrontend.ScalarEnvironment
