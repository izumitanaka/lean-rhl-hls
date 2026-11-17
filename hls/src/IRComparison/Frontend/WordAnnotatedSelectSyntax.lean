import IRComparison.Frontend.WordAnnotatedNegSyntax

namespace IRComparison.WordFrontend.AnnotatedSelect
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic ScalarEnvironment ScalarSyntax
set_option maxHeartbeats 2400000

theorem materialize_source (bindings : Bindings env ctx p) :
    materialize bindings (AnnotatedCondition.scalarSource resultAnnotation annotation v d a b) =
      AnnotatedCondition.scalarSource resultAnnotation annotation (materialize bindings v)
        (materialize bindings d) (materialize bindings a) (materialize bindings b) := by
  cases bindings <;> cases resultAnnotation <;> cases annotation <;> rfl

theorem finish_complete (setup : AliasSetup env) (library : ScalarSyntax.Library env)
    (scalarLibrary : ScalarConversion.Signatures env) (inputs : InputsTyped env ctx p)
    (resultAnnotation annotation : WordBinder.Annotation)
    {e : Piece env ctx p v scalarExpected} (value : ScalarCasts inputs e (SourceCasts env) (ScalarConversion.Casts setup))
    {a : Piece env ctx p yes scalarExpected} (left : ScalarCasts inputs a (SourceCasts env) (ScalarConversion.Casts setup))
    {b : Piece env ctx p no scalarExpected} (right : ScalarCasts inputs b (SourceCasts env) (ScalarConversion.Casts setup))
    (decisionRep : Represents d dc)
    (premises : AnnotatedCondition.ScalarConditions setup ctx value.sourceCore.val dc left.sourceCore.val right.sourceCore.val annotation)
    (freshEq : ∀ r ∈ setup.rules, ``Eq ≠ r.name)
    (coverage : Conversion.Covers conv 0 (ScalarConversion.Casts setup)) (exposure : Exposure env) :
    ∃ result, finish env conv exposure ctx
      (scalarExpected p (app ``HybridWord.Expr.select [e.code,a.code,b.code])
        (AnnotatedCondition.scalarSource resultAnnotation annotation v d yes no))
      (app ``HybridWord.Expr.select [e.code,a.code,b.code])
      (app ``WordFrontendFacts.select ([e.code,a.code,b.code] ++ p.args ++
        [v,d,yes,no,e.checked.proof,a.checked.proof,b.checked.proof]))
      (e.checked.known.orElse (a.checked.known.orElse b.checked.known)) = some result ∧
      CastTyping env 0 (ScalarConversion.Casts setup) ctx result.proofCore.val result.core.val ∧
      result.code = app ``HybridWord.Expr.select [e.code,a.code,b.code] := by
  have embed : ∀ scope a b, SourceCasts env scope a b → ScalarConversion.Casts setup scope a b := fun _ _ _ h => .source h
  have targetRep := app_represents (f := Lean.Expr.const ``HybridWord.Expr.select []) (.constant rfl)
    (.cons e.represented.property (.cons a.represented.property (.cons b.represented.property .nil)))
  have srcRep := AnnotatedCondition.scalarSource_represents resultAnnotation annotation
    value.sourceCore.property decisionRep left.sourceCore.property right.sourceCore.property
  have proofRep := app_represents (f := Lean.Expr.const ``WordFrontendFacts.select []) (.constant rfl)
    (.cons e.represented.property (.cons a.represented.property (.cons b.represented.property
      (.cons inputs.i.property (.cons inputs.x.property (.cons inputs.y.property
        (.cons inputs.s.property (.cons inputs.ls.property
          (.cons value.sourceCore.property (.cons decisionRep (.cons left.sourceCore.property
            (.cons right.sourceCore.property (.cons e.checked.proofCore.property
              (.cons a.checked.proofCore.property (.cons b.checked.proofCore.property .nil)))))))))))))))
  have decCast : ScalarConversion.Casts setup ctx
      (.app (.const ``Decidable []) (AnnotatedCondition.condition annotation value.sourceCore.val))
      (.app (.const ``Decidable []) (Branch.condition value.sourceCore.val)) :=
    .condition (.decision premises.library annotation .word premises.operand premises.value premises.form
      premises.fresh premises.freshLiteral freshEq premises.freshDecision)
  have fact := Branch.Select.fact_typed inputs (value.inProofCasts embed) (left.inProofCasts embed)
    (right.inProofCasts embed) (.converted (premises.decisionTyped.mono embed) decCast) library.selectFact
  have constructor : CastTyping env 0 (SourceCasts env) ctx (.const ``HybridWord.Expr.select []) Branch.Select.constructorSignature :=
    .constant library.selectConstructor (by simp) rfl
  have target := CastTyping.application (CastTyping.application (CastTyping.application constructor value.target) left.target) right.target
  have lhs := ScalarConversion.eval_typed scalarLibrary inputs target
  have srcTyped := AnnotatedCondition.scalarSource_typed premises.library library.toSignatures
    resultAnnotation annotation value.value premises.decisionTyped left.value right.value library.ite
  exact finish_checked_complete (scalarExpected_represents inputs targetRep srcRep) proofRep
    (.converted fact (.selectAnnotation resultAnnotation premises lhs))
    ((ScalarConversion.expected_typed scalarLibrary lhs srcTyped).mono embed)
    ((known_casts e.checked value.proof).orElse ((known_casts a.checked left.proof).orElse (known_casts b.checked right.proof)))
    coverage exposure _


theorem visit_complete_code (setup : AliasSetup env) (library : ScalarSyntax.Library env)
    (scalarLibrary : ScalarConversion.Signatures env) (inputs : InputsTyped env ctx p)
    (resultAnnotation annotation : WordBinder.Annotation)
    (types : BindingTypes inputs (SourceCasts env) bindings (ScalarConversion.Casts setup))
    {e : Piece env ctx p (materialize bindings v) scalarExpected} (value : ScalarCasts inputs e (SourceCasts env) (ScalarConversion.Casts setup))
    {a : Piece env ctx p (materialize bindings yes) scalarExpected} (left : ScalarCasts inputs a (SourceCasts env) (ScalarConversion.Casts setup))
    {b : Piece env ctx p (materialize bindings no) scalarExpected} (right : ScalarCasts inputs b (SourceCasts env) (ScalarConversion.Casts setup))
    (decisionRep : Represents (materialize bindings d) dc)
    (premises : AnnotatedCondition.ScalarConditions setup ctx value.sourceCore.val dc left.sourceCore.val right.sourceCore.val annotation)
    (freshEq : ∀ r ∈ setup.rules, ``Eq ≠ r.name)
    (coverage : Conversion.Covers conv 0 (ScalarConversion.Casts setup)) (exposure : Exposure env)
    (valueParsed : visit env conv exposure ctx p v bindings = some e)
    (leftParsed : visit env conv exposure ctx p yes bindings = some a)
    (rightParsed : visit env conv exposure ctx p no bindings = some b)
    (scope : Separated p (materialize bindings (AnnotatedCondition.scalarSource resultAnnotation annotation v d yes no))) :
    ∃ result, visit env conv exposure ctx p (AnnotatedCondition.scalarSource resultAnnotation annotation v d yes no) bindings = some result ∧
      Nonempty (ScalarCasts inputs result (SourceCasts env) (ScalarConversion.Casts setup)) ∧
      (result.code = app ``HybridWord.Expr.select [e.code,a.code,b.code]) := by
  have rep : Represents (materialize bindings (AnnotatedCondition.scalarSource resultAnnotation annotation v d yes no))
      (AnnotatedCondition.choice resultAnnotation.core annotation value.sourceCore.val dc left.sourceCore.val right.sourceCore.val) := by
    rw [materialize_source]
    exact AnnotatedCondition.scalarSource_represents resultAnnotation annotation value.sourceCore.property decisionRep left.sourceCore.property right.sourceCore.property
  rcases lookup_typed types (AnnotatedCondition.scalarSource resultAnnotation annotation v d yes no) conv with miss | ⟨cached,hit,typed⟩
  ·
    obtain ⟨artifact,checked,proofTyped,_⟩ := finish_complete setup library scalarLibrary inputs resultAnnotation annotation
      value left right decisionRep premises freshEq coverage exposure
    let code := ClosedTerm.app ``HybridWord.Expr.select [e.closedTerm,a.closedTerm,b.closedTerm]
    let art : Artifact env ctx (scalarExpected p code.val (materialize bindings (AnnotatedCondition.scalarSource resultAnnotation annotation v d yes no))) := by
      simpa only [materialize_source,code,ClosedTerm.app,Piece.closedTerm] using artifact
    let result : Piece env ctx p (materialize bindings (AnnotatedCondition.scalarSource resultAnnotation annotation v d yes no)) scalarExpected := ⟨code.val,art,code.closed,code.represented⟩
    refine ⟨result,?_,⟨⟨⟨_,rep⟩,?_,?_,?_⟩⟩,rfl⟩
    · have head : (AnnotatedCondition.scalarSource resultAnnotation annotation v d yes no).getAppFn.constName? = some ``ite := rfl
      apply eq_of_heq
      rw [visit] <;> try (solve | intro name ty value next flag h; cases h)
      simp only [miss,node,head]
      simp [-heq_eq_eq,List.forIn_cons,scope.index,scope.left,scope.right,scope.locals]
      simp only [forIn_constant_yield]
      cases resultAnnotation <;> cases annotation <;>
        simp [arguments,conditionValue,below,AnnotatedCondition.scalarSource,AnnotatedCondition.nativeCondition,AnnotatedCondition.nativeTest,AnnotatedCondition.nativeHeader,
        AnnotatedLiteral.native,WordBinder.Annotation.native,Arithmetic.nativeWidth,
        Lean.mkApp5,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB,
        List.map_cons,List.map_nil,Lean.Expr.getAppFn,Lean.Expr.constName?]
      all_goals try apply heq_of_eq
      all_goals cases bindings <;> simp [finishScalar,ClosedTerm.app,Piece.closedTerm,code,result,art,
        materialize,LeanBindings.substitute,AnnotatedCondition.scalarSource,AnnotatedCondition.nativeCondition,AnnotatedCondition.nativeTest,AnnotatedCondition.nativeHeader,
        AnnotatedLiteral.native,WordBinder.Annotation.native,Arithmetic.nativeWidth,word,app,
        Lean.mkApp5,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB] at checked ⊢
      all_goals exact ⟨e,valueParsed,a,leftParsed,b,rightParsed,artifact,checked,⟨⟨rfl,rfl⟩,rfl⟩,HEq.rfl,HEq.rfl⟩
    · exact AnnotatedCondition.scalarSource_typed premises.library library.toSignatures resultAnnotation annotation
        value.value premises.decisionTyped left.value right.value library.ite
    · have h : CastTyping env 0 (SourceCasts env) ctx (.const ``HybridWord.Expr.select []) Branch.Select.constructorSignature :=
        .constant library.selectConstructor (by simp) rfl
      have a1 := CastTyping.application h value.target
      simp only [Branch.Select.constructorSignature,exprType,VExpr.inst] at a1
      have a2 := CastTyping.application a1 left.target
      simp only [VExpr.inst] at a2
      exact .application a2 right.target
  
    · cases bindings <;> cases resultAnnotation <;> cases annotation <;> simpa [result,art,materialize,LeanBindings.substitute,
        AnnotatedCondition.scalarSource,AnnotatedCondition.nativeCondition,AnnotatedCondition.nativeTest,AnnotatedCondition.nativeHeader,
        AnnotatedLiteral.native,WordBinder.Annotation.native,Arithmetic.nativeWidth,word,app,
        Lean.mkApp5,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB] using proofTyped
  · simp [ScalarEnvironment.lookup,AnnotatedCondition.scalarSource,Lean.mkApp5,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2] at hit

end IRComparison.WordFrontend.AnnotatedSelect
