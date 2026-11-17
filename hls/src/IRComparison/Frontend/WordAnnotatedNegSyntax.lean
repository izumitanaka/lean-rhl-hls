import IRComparison.Frontend.WordAnnotatedBinarySyntax

namespace IRComparison.WordFrontend.AnnotatedNeg
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic ScalarEnvironment ScalarSyntax
set_option maxHeartbeats 1800000

theorem materialize_neg (bindings : Bindings env ctx p) (annotation : WordBinder.Annotation) (v : Lean.Expr) :
    materialize bindings (.app (nativeHeader annotation) v) = .app (nativeHeader annotation) (materialize bindings v) := by
  rw [materialize_app,materialize_closed bindings (by cases annotation <;> rfl)]

theorem visit_complete_code (setup : AliasSetup env) (scalarLibrary : ScalarConversion.Signatures env)
    (inputs : InputsTyped env ctx p) (library : ScalarSyntax.Library env)
    (types : BindingTypes inputs (SourceCasts env) bindings (ScalarConversion.Casts setup))
    {a : Piece env ctx p (materialize bindings v) scalarExpected}
    (value : ScalarCasts inputs a (SourceCasts env) (ScalarConversion.Casts setup))
    (annotation operand : WordBinder.Annotation)
    (operandTyped : CastTyping env 0 (SourceCasts env) ctx value.sourceCore.val operand.core)
    (form : ValueForm setup ctx value.sourceCore.val operand.core)
    (fresh : ∀ r ∈ setup.rules, ``Neg.neg ≠ r.name)
    (coverage : Conversion.Covers conv 0 (ScalarConversion.Casts setup)) (exposure : Exposure env)
    (parsed : visit env conv exposure ctx p v bindings = some a)
    (scope : Separated p (materialize bindings (.app (nativeHeader annotation) v))) :
    ∃ piece, visit env conv exposure ctx p (.app (nativeHeader annotation) v) bindings = some piece ∧
      Nonempty (ScalarCasts inputs piece (SourceCasts env) (ScalarConversion.Casts setup)) ∧
      (piece.code = app ``HybridWord.Expr.neg [a.code]) := by
  have rep : Represents (materialize bindings (.app (nativeHeader annotation) v)) (.app (header annotation) value.sourceCore.val) := by
    rw [materialize_neg]
    exact .app (represented annotation) value.sourceCore.property
  rcases lookup_typed types (.app (nativeHeader annotation) v) conv with miss | ⟨cached,hit,typed⟩
  · obtain ⟨artifact,checked,typed,_⟩ := ScalarConversion.annotated_neg_finish setup inputs library.toSignatures scalarLibrary
      value annotation operand operandTyped form fresh library.negFact library.negConstructor coverage exposure
    let code := ClosedTerm.app ``HybridWord.Expr.neg [a.closedTerm]
    let art : Artifact env ctx (scalarExpected p code.val (materialize bindings (.app (nativeHeader annotation) v))) := by
      simpa only [materialize_neg,code,ClosedTerm.app,Piece.closedTerm] using artifact
    let piece : Piece env ctx p (materialize bindings (.app (nativeHeader annotation) v)) scalarExpected :=
      ⟨code.val,art,code.closed,code.represented⟩
    have sourceTyped := value_typed library.toSignatures annotation value.value
    refine ⟨piece,?_,⟨⟨⟨_,rep⟩,sourceTyped,?_,?_⟩⟩,rfl⟩
    · have head : (Lean.Expr.app (nativeHeader annotation) v).getAppFn.constName? = some ``Neg.neg := rfl
      apply eq_of_heq
      rw [visit] <;> try (solve | intro name ty value next flag h; cases h)
      simp only [miss,node,head]
      simp [-heq_eq_eq,List.forIn_cons,scope.index,scope.left,scope.right,scope.locals]
      simp only [forIn_constant_yield]
      have smaller : syntaxSize v < syntaxSize (.app (nativeHeader annotation) v) := by simp only [syntaxSize]; omega
      have last : (arguments (.app (nativeHeader annotation) v)).getLast? = some ⟨v,smaller⟩ := by cases annotation <;> rfl
      simp only [last,parsed,Option.bind_some,Option.bind_assoc,Option.bind_fun_some]
      apply heq_of_eq
      cases bindings <;> cases annotation <;> simp [materialize,LeanBindings.substitute,nativeHeader,WordBinder.Annotation.native,nativeWidth,word,
        finishScalar,ClosedTerm.app,Piece.closedTerm,code,piece,art,app,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB] at checked ⊢
      all_goals exact ⟨a,parsed,artifact,checked,rfl,HEq.rfl,HEq.rfl⟩
    · have fact : CastTyping env 0 (SourceCasts env) ctx (.const ``HybridWord.Expr.neg []) (.forallE exprType exprType) :=
        .constant library.negConstructor (by simp) rfl
      exact .application fact value.target
    · cases bindings <;> cases annotation <;> simpa [piece,art,materialize,LeanBindings.substitute,nativeHeader,WordBinder.Annotation.native,nativeWidth,
        app,Lean.mkApp2,Lean.mkApp,Lean.mkAppB] using typed
  · simp [ScalarEnvironment.lookup] at hit

end IRComparison.WordFrontend.AnnotatedNeg
