import IRComparison.Frontend.WordFunctionReads

/-! Latest-State bindings in a lexical function environment. These rules
preserve the existing latest-State condition; old State snapshots are not added. -/
namespace IRComparison.WordFrontend.FunctionSyntax
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic StructuralBody StructuralSyntax
set_option maxHeartbeats 1800000

/-- Value-mode updates use only the normalized operands; lexical closures
are not consulted and no State expression is evaluated during analysis. -/
theorem valueAssign_congr (σ : Substitution) :
    HEq (visit env conv exposure (app ``HybridWord.State.set [st,r,v]) ctx p .value σ fs)
      (visit env conv exposure (app ``HybridWord.State.set [σ.apply st,σ.apply r,σ.apply v])
        ctx p .value .identity (fun _ => none)) := by
  rw [visit,visit]
  cases σ <;> rfl

theorem substitute_valueAssign (σ : Substitution) :
    σ.apply (app ``HybridWord.State.set [st,r,v]) =
      app ``HybridWord.State.set [σ.apply st,σ.apply r,σ.apply v] := by
  cases σ <;> rfl

theorem stateAlias_complete_code (setup : AliasSetup env) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (fresh : ScopedSyntax.Fresh setup) (exposure : Exposure env)
    (inputs : InputsTyped env ctx p)
    {b : Piece env (stateType::ctx) {p.lift with s := .bvar 0} ((under σ).apply next) bodyExpected}
    (right : BodyCasts (inputs.nextState closed) b (SourceCasts env) (For.Casts setup))
    (form : ValueForm setup (stateType::ctx) right.sourceCore.val (optionType stateType))
    (current : σ.apply st = p.s)
    (parsed : visit env setup.conversion exposure next (stateType::ctx) {p.lift with s := .bvar 0}
      .body (under σ) (underFunctions fs) = some b)
    (binder : Lean.Name) (flag : Bool) :
    ∃ result, visit env setup.conversion exposure (.letE binder state st next flag) ctx p .body σ fs = some result ∧
      ∃ typed : BodyCasts inputs result (SourceCasts env) (For.Casts setup),
        ValueForm setup ctx typed.sourceCore.val (optionType stateType) ∧ result.code = b.code := by
  have coverage := For.Casts.covered setup library.scalars.toSignatures library.steps closed
    library.cons library.eq library.eval fresh.state fresh.eq fresh.lift
  obtain ⟨target,_,_⟩ := sequence_next_typed inputs closed SourceCasts.closed library.steps.state right
  have assembled := StateAlias.alias_certificate inputs closed SourceCasts.closed
    (fun _ _ _ h => For.Casts.base (.base (.source h))) library.steps.state right
    (.base (.base (.stateContinuation inputs target right.value form))) library.stateAlias coverage exposure binder flag
  have sourceSame := StructuralStep.Alias.substitute_latest_let (binder := binder) (st := st) (nextBody := next) (nondep := flag) σ
  rw [current] at sourceSame
  rw [← sourceSame] at assembled
  obtain ⟨artifact,checked,typed,same⟩ := assembled
  let result : Piece env ctx p (σ.apply (.letE binder state st next flag)) bodyExpected :=
    ⟨b.code,artifact,b.closed,b.represented⟩
  refine ⟨result,?_,typed,?_,rfl⟩
  · have typeSame := sameTerm_complete (a := state) (b := state) (Represents.constant rfl) (Represents.constant rfl)
    have valueSame := sameTerm_complete inputs.s.property inputs.s.property
    have translated : translate state = some ⟨stateType,Represents.constant rfl⟩ := rfl
    have modeValue : (Mode.body == Mode.value) = false := rfl
    have modeStep : (Mode.body == Mode.step) = false := rfl
    cases σ
    all_goals
      rw [visit]
      simp only [node,letParts,modeValue,modeStep,Substitution.apply,LeanBindings.substitute,under,
        state,WordFrontend.state] at current parsed checked typeSame translated ⊢
      simp only [current,typeSame,valueSame,translated,Bool.false_eq_true,ite_false,Bool.true_and,
        Bool.true_eq_false,Bool.and_self,Bool.and_true,ite_true,bind,Option.bind,pure,Option.pure_def]
      rw [parsed]
      dsimp only
      simp only [finishBody,Mode.expected,result,Piece.closedTerm,app,ClosedTerm.const,
        List.map_cons,List.map_nil,List.foldl_cons,List.foldl_nil,Substitution.apply,LeanBindings.substitute,
        state,WordFrontend.state] at checked ⊢
      simp only [Inputs.args,List.cons_append,List.nil_append,List.foldl_cons,List.foldl_nil] at checked ⊢
      rw [checked]
      all_goals rfl
  · rw [same]; exact .beta right.value

theorem stepAlias_complete_code (setup : AliasSetup env) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (fresh : ScopedSyntax.Fresh setup) (exposure : Exposure env)
    (inputs : InputsTyped env ctx p)
    {b : Piece env (stateType::ctx) {p.lift with s := .bvar 0} ((under σ).apply next) Mode.step.expected}
    (right : StructuralLoop.StepCasts (inputs.nextState closed) b (SourceCasts env) (For.Casts setup))
    (form : ValueForm setup (stateType::ctx) right.sourceCore.val (optionType Step.stepState))
    (current : σ.apply st = p.s)
    (parsed : visit env setup.conversion exposure next (stateType::ctx) {p.lift with s := .bvar 0}
      .step (under σ) (underFunctions fs) = some b)
    (binder : Lean.Name) (flag : Bool) :
    ∃ result, visit env setup.conversion exposure (.letE binder state st next flag) ctx p .step σ fs = some result ∧
      ∃ typed : StructuralLoop.StepCasts inputs result (SourceCasts env) (For.Casts setup),
        ValueForm setup ctx typed.sourceCore.val (optionType Step.stepState) ∧ result.code = b.code := by
  have coverage := For.Casts.covered setup library.scalars.toSignatures library.steps closed
    library.cons library.eq library.eval fresh.state fresh.eq fresh.lift
  have eval := eval_cast_typed (inputs.nextState closed) library.eval right.target
  have direct := For.Casts.directContinuation (setup := setup) .state eval right.value form
  have codeClosed := b.represented.property.closed 0 b.closed
  have beta : For.Casts setup ctx (StructuralStep.sequenceNextActual inputs b.represented.val right.sourceCore.val)
      (StructuralStep.sequenceContinuationType inputs b.represented.val (.lam stateType right.sourceCore.val)) := by
    simpa only [StructuralStep.sequenceNextActual,StructuralStep.sequenceContinuationType,
      InputsTyped.nextState,InputsTyped.lift,Step.Binder.core,Arithmetic.continuationValue,
      VExpr.lift,VExpr.liftN,stateType,codeClosed.liftN_eq (Nat.zero_le _)] using direct
  obtain ⟨piece,success,⟨typed⟩,code⟩ := StructuralStep.Alias.mapped_alias_complete_code inputs closed SourceCasts.closed
    (fun _ _ _ h => For.Casts.base (.base (.source h))) library.steps.state right beta library.stepAlias
    coverage exposure binder flag current parsed
  refine ⟨piece,success,typed,?_,code⟩
  have represented : Represents (σ.apply (.letE binder state st next flag))
      (.app (.lam stateType right.sourceCore.val) inputs.s.val) := by
    rw [StructuralStep.Alias.substitute_latest_let,current]
    exact .letE (.constant rfl) inputs.s.property right.sourceCore.property
  rw [typed.sourceCore.property.unique represented]
  exact .beta right.value

end IRComparison.WordFrontend.FunctionSyntax
