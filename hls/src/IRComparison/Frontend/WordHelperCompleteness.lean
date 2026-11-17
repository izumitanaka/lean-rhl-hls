import IRComparison.Frontend.WordMappedTraversal
import IRComparison.Frontend.WordForConversion

/-! Compositional completeness for ordinary local helper applications.
The recursive body premise is discharged by the source syntax induction. -/
namespace IRComparison.WordFrontend.StructuralSyntax
open Lean4Lean LeanTyped LeanTypeInference Certificate StructuralBody
set_option maxHeartbeats 1200000

/-- Finish the same body certificate at a native helper call. The beta spine,
argument typing and representation conditions are independent of parsing;
the child certificate is supplied by the current body/argument construction. -/
private theorem helper_retarget_complete_transport {sourceCore : VExpr}
    (setup : Arithmetic.AliasSetup env)
    (stateDeclared : env.constants ``HybridWord.State = some ⟨0,.sort (.succ .zero)⟩)
    (optionDeclared : env.constants ``Option = some optionSignature)
    (eqDeclared : env.constants ``Eq = some eqSignature)
    (evalDeclared : env.constants ``HybridWord.Cmd.eval = some ⟨0,evalSignature⟩)
    (coverage : Conversion.Covers setup.conversion 0 (For.Casts setup))
    (inputs : InputsTyped env ctx p)
    {piece : Piece env ctx p reduced bodyExpected}
    (child : BodyCasts inputs piece (Arithmetic.SourceCasts env) (For.Casts setup))
    (sourceRep : Represents source sourceCore)
    (sourceTyped : CastTyping env 0 (Arithmetic.SourceCasts env) ctx sourceCore (optionType stateType))
    (transport : ∀ lhs,
      CastTyping env 0 (Arithmetic.SourceCasts env) ctx
        (.app (.app (.const ``Eq [.succ .zero]) (optionType stateType)) lhs)
        (.forallE (optionType stateType) (.sort .zero)) →
      For.Casts setup ctx (equalValues (optionType stateType) lhs child.sourceCore.val)
        (equalValues (optionType stateType) lhs sourceCore)) :
    ∃ result, retargetPiece setup.conversion .body source piece = some result ∧
      result.code = piece.code ∧
      Nonempty (BodyCasts inputs result (Arithmetic.SourceCasts env) (For.Casts setup)) := by
  have evaluation := eval_cast_typed inputs evalDeclared child.target
  have prefixTyped := CastTyping.application
    ((equality_head_typed stateDeclared optionDeclared eqDeclared).withCasts
      (Arithmetic.SourceCasts env)) evaluation
  simp only [WordFrontend.optionState,stateType,VExpr.inst] at prefixTyped
  have expectedRep := bodyExpected_represents inputs piece.represented.property sourceRep
  have actualRep := bodyExpected_represents inputs piece.represented.property child.sourceCore.property
  have actualSame := piece.checked.core.property.unique actualRep
  have cast : For.Casts setup ctx piece.checked.core.val
      (equalValues (optionType stateType)
        (bodyValue inputs.i.val inputs.x.val inputs.y.val piece.represented.val inputs.s.val inputs.ls.val)
        sourceCore) := by
    rw [actualSame]
    exact transport _ prefixTyped

  have typeTyped := CastTyping.application prefixTyped sourceTyped
  obtain ⟨checked,success,proofTyped⟩ := ScalarEnvironment.retarget_cast_complete piece.checked expectedRep
    child.proof (typeTyped.mono (fun _ _ _ h => .base (.base (.source h)))) cast
    coverage
  refine ⟨⟨piece.code,checked,piece.closed,piece.represented⟩,?_,rfl,?_⟩
  · simp only [retargetPiece,Mode.expected,success,bind,Option.bind,pure,Option.pure_def]
  · exact ⟨⟨⟨_,sourceRep⟩,sourceTyped,child.target,proofTyped⟩⟩

theorem helper_retarget_complete {body : VExpr}
    (setup : Arithmetic.AliasSetup env)
    (stateDeclared : env.constants ``HybridWord.State = some ⟨0,.sort (.succ .zero)⟩)
    (optionDeclared : env.constants ``Option = some optionSignature)
    (eqDeclared : env.constants ``Eq = some eqSignature)
    (evalDeclared : env.constants ``HybridWord.Cmd.eval = some ⟨0,evalSignature⟩)
    (coverage : Conversion.Covers setup.conversion 0 (For.Casts setup))
    (inputs : InputsTyped env ctx p)
    {piece : Piece env ctx p reduced bodyExpected}
    (child : BodyCasts inputs piece (Arithmetic.SourceCasts env) (For.Casts setup))
    (domainTyped : CastTyping env 0 (Arithmetic.SourceCasts env) ctx domain (.sort u))
    (bodyTyped : CastTyping env 0 (Arithmetic.SourceCasts env) (domain::ctx) body bodyType)
    (argument : CastTyping env 0 (Arithmetic.SourceCasts env) ctx arg domain)
    (arguments : LeanTypeReduction.ArgumentsCasts env 0 (Arithmetic.SourceCasts env) ctx
      (bodyType.inst arg) args (optionType stateType))
    (reducedRep : Represents reduced (args.foldl LeanTypeReduction.applyReduced (body.inst arg)))
    (sourceRep : Represents source (applications (.app (.lam domain body) arg) args))
    (form : Arithmetic.ValueForm setup ctx
      (args.foldl LeanTypeReduction.applyReduced (body.inst arg)) (optionType stateType)) :
    ∃ result, retargetPiece setup.conversion .body source piece = some result ∧
      result.code = piece.code ∧
      Nonempty (BodyCasts inputs result (Arithmetic.SourceCasts env) (For.Casts setup)) := by
  have sourceTyped : CastTyping env 0 (Arithmetic.SourceCasts env) ctx
      (applications (.app (.lam domain body) arg) args) (optionType stateType) :=
    arguments.application_typed (.application (.lambda domainTyped bodyTyped) argument)
  have reducedSame := child.sourceCore.property.unique reducedRep
  exact helper_retarget_complete_transport setup stateDeclared optionDeclared eqDeclared evalDeclared coverage inputs child sourceRep sourceTyped (fun lhs prefixTyped => by
    rw [reducedSame]
    exact .helperEquality prefixTyped bodyTyped argument arguments (reducedSame ▸ child.value) form
      (by intro u; simp [optionType]))

/-- Retained scalar arguments use the shared administrative conversion rule.
The returned certificate keeps the invariant needed by enclosing constructs. -/
theorem helper_retained_retarget_complete {body : VExpr}
    (setup : Arithmetic.AliasSetup env)
    (stateDeclared : env.constants ``HybridWord.State = some ⟨0,.sort (.succ .zero)⟩)
    (optionDeclared : env.constants ``Option = some optionSignature)
    (eqDeclared : env.constants ``Eq = some eqSignature)
    (evalDeclared : env.constants ``HybridWord.Cmd.eval = some ⟨0,evalSignature⟩)
    (coverage : Conversion.Covers setup.conversion 0 (For.Casts setup))
    (inputs : InputsTyped env ctx p)
    {piece : Piece env ctx p reduced bodyExpected}
    (child : BodyCasts inputs piece (Arithmetic.SourceCasts env) (For.Casts setup))
    (domainTyped : CastTyping env 0 (Arithmetic.SourceCasts env) ctx domain (.sort u))
    (bodyTyped : CastTyping env 0 (Arithmetic.SourceCasts env) (domain::ctx) body (domains.foldr VExpr.forallE (optionType stateType)))
    (argument : CheckedTyping env 0 (Arithmetic.SourceCasts env) ctx arg domain)
    (arguments : List.Forall₂ (fun domain arg =>
      CheckedTyping env 0 (Arithmetic.SourceCasts env) ctx arg domain) domains args)
    (typesClosed : ∀ n, ((domains.drop n).foldr VExpr.forallE (optionType stateType)).ClosedN 0)
    (prefixTypes : ∀ before after, args = before ++ after → after ≠ [] →
      CastTyping env 0 (Arithmetic.SourceCasts env) ctx
        (before.foldl LeanTypeReduction.applyReduced (body.inst arg))
        ((domains.drop before.length).foldr VExpr.forallE (optionType stateType)))
    (sourceRep : Represents source (applications (.app (.lam domain body) arg) args))
    (chain : RetainedConversion.Prefix env 0 (Arithmetic.SourceCasts env) (optionType stateType)
      ctx child.sourceCore.val (args.foldl LeanTypeReduction.applyReduced (body.inst arg)) count) :
    ∃ result, retargetPiece setup.conversion .body source piece = some result ∧
      result.code = piece.code ∧
      Nonempty (BodyCasts inputs result (Arithmetic.SourceCasts env) (For.Casts setup)) := by
  have initialClosed := typesClosed 0
  simp only [List.drop_zero] at initialClosed
  have sourceTyped : CastTyping env 0 (Arithmetic.SourceCasts env) ctx
      (applications (.app (.lam domain body) arg) args) (optionType stateType) :=
    LeanTypeReduction.checked_spine_typed arguments typesClosed (by
      simpa only [initialClosed.instN_eq (Nat.zero_le _)] using
        CastTyping.checkedApplication (.lambda domainTyped bodyTyped) argument)
  exact helper_retarget_complete_transport setup stateDeclared optionDeclared eqDeclared evalDeclared coverage inputs child sourceRep sourceTyped (fun lhs prefixTyped => by
    exact .retainedEquality prefixTyped bodyTyped argument arguments typesClosed prefixTypes chain (by trivial))


theorem incompatible_of_conversion_none {conv : Conversion env} (left : Represents a ac) (right : Represents b bc)
    (different : ac ≠ bc) (rejected : conv 0 ctx ac bc = none) :
    compatible env conv ctx a b = false := by
  have differentTerm : sameTerm a b = false := Bool.eq_false_iff.mpr
    (fun same => different (sameTerm_sound left right same))
  obtain ⟨aCore,ha,sa⟩ := left.translate_complete
  obtain ⟨bCore,hb,sb⟩ := right.translate_complete
  simp only [compatible,differentTerm,Bool.false_eq_true,ite_false,ha,hb,bind,Option.bind]
  change ((conv 0 ctx aCore.val bCore.val).bind (fun _ => some ())).isSome = false
  rw [sa,sb,rejected]
  rfl

/-- The original lexical body is visited under a captured function binding.
The recursive premise is for that strict source child, not a substituted-body
reparse. Certificate transport preserves the generated command. -/
theorem function_let_step_complete {sourceBody functionValue : VExpr}
    (setup : Arithmetic.AliasSetup env)
    (stateDeclared : env.constants ``HybridWord.State = some ⟨0,.sort (.succ .zero)⟩)
    (optionDeclared : env.constants ``Option = some optionSignature)
    (eqDeclared : env.constants ``Eq = some eqSignature)
    (evalDeclared : env.constants ``HybridWord.Cmd.eval = some ⟨0,evalSignature⟩)
    (stateFresh : ∀ r ∈ setup.rules, ``HybridWord.State ≠ r.name)
    (coverage : Conversion.Covers setup.conversion 0 (For.Casts setup))
    (exposure : Exposure env) (binder : Lean.Name) (ty value next : Lean.Expr) (flag : Bool)
    (inputs : InputsTyped env ctx p)
    (typeRep : Represents (σ.apply ty) (.forallE domain codomain))
    (typeTyped : CastTyping env 0 (Arithmetic.SourceCasts env) ctx (.forallE domain codomain) (.sort u))
    (bodyTyped : CastTyping env 0 (Arithmetic.SourceCasts env) ((.forallE domain codomain)::ctx)
      sourceBody (optionType stateType))
    (valueTyped : CastTyping env 0 (Arithmetic.SourceCasts env) ctx functionValue (.forallE domain codomain))
    (reducedRep : Represents ((letSubstitution σ value).apply next) (sourceBody.inst functionValue))
    (sourceRep : Represents (σ.apply (.letE binder ty value next flag))
      (.app (.lam (.forallE domain codomain) sourceBody) functionValue))
    {piece : Piece env ctx p ((letSubstitution σ value).apply next) bodyExpected}
    (typed : BodyCasts inputs piece (Arithmetic.SourceCasts env) (For.Casts setup))
    (form : Arithmetic.ValueForm setup ctx typed.sourceCore.val (optionType stateType))
    (parsed :
      let raw := Lean.Expr.letE binder ty value next flag
      let recursor : Recursor env raw := fun nextCtx nextInputs nextMode bindings functions child =>
        visit env setup.conversion exposure child.val nextCtx nextInputs nextMode bindings functions
      let child : Child raw := ⟨value,by dsimp only [raw]; simp only [syntaxSize]; omega⟩
      visit env setup.conversion exposure next ctx p .body (letSubstitution σ value)
        (letContinuations fs (makeContinuation recursor ctx.length σ fs child)) = some piece) :
    ∃ result, visit env setup.conversion exposure (.letE binder ty value next flag) ctx p .body σ fs = some result ∧
      result.code = piece.code ∧
      ∃ typed : BodyCasts inputs result (Arithmetic.SourceCasts env) (For.Casts setup),
        Arithmetic.ValueForm setup ctx typed.sourceCore.val (optionType stateType) := by
  have notState : sameTerm (σ.apply ty) state = false := Bool.eq_false_iff.mpr (by
    intro same
    have impossible := sameTerm_sound typeRep (Represents.constant rfl : Represents state stateType) same
    cases impossible)
  have notWord : compatible env setup.conversion ctx (σ.apply ty) word = false := incompatible_of_conversion_none typeRep
    (Represents.constant rfl : Represents word wordType) (by intro h; cases h)
    (setup.function_word_none (ctx := ctx))
  have notStateCompatible : compatible env setup.conversion ctx (σ.apply ty) state = false := incompatible_of_conversion_none typeRep
    (Represents.constant rfl : Represents state stateType) (by intro h; cases h)
    (setup.function_state_none (ctx := ctx) stateFresh)
  have sameCore := typed.sourceCore.property.unique reducedRep
  obtain ⟨result,retargeted,codeSame,⟨resultTyped⟩⟩ := helper_retarget_complete setup
    stateDeclared optionDeclared eqDeclared evalDeclared coverage inputs typed typeTyped bodyTyped
    valueTyped (args := []) .nil reducedRep sourceRep (sameCore ▸ form)
  dsimp only at parsed
  refine ⟨result,?_,codeSame,resultTyped,?_⟩
  · rw [visit]
    have modeValue : (Mode.body == Mode.value) = false := rfl
    simp only [node,modeValue,Bool.false_eq_true,ite_false,letParts,notState,notWord,
      notStateCompatible,Bool.false_and,Bool.true_and,Bool.not_false,Bool.and_false,
      parsed,retargeted,bind,Option.bind,pure,Option.pure_def]
  · rw [resultTyped.sourceCore.property.unique sourceRep]
    exact .beta bodyTyped

end IRComparison.WordFrontend.StructuralSyntax
