import IRComparison.Frontend.WordScalarConversion

namespace IRComparison.WordFrontend.AnnotatedBinary
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic ScalarEnvironment ScalarSyntax
set_option maxHeartbeats 2400000

theorem materialize_binary (bindings : Bindings env ctx p) (op : Binary)
    (a b c d : WordBinder.Annotation) (u v : Lean.Expr) :
    materialize bindings (Lean.mkApp2 (nativeHeader op a b c d) u v) =
      Lean.mkApp2 (nativeHeader op a b c d) (materialize bindings u) (materialize bindings v) := by
  simp only [materialize_eq_substitute,nativeHeader,nativeDictionary,Lean.mkApp2,Lean.mkApp4,
    Lean.mkApp,Lean.mkAppB,LeanBindings.substitute,WordBinder.Annotation.substitute_native,
    app,nativeWidth,List.foldl_cons,List.foldl_nil,Lean.mkApp3]

theorem visit_complete_code (setup : AliasSetup env) (scalarLibrary : ScalarConversion.Signatures env) (inputs : InputsTyped env ctx p) (library : ScalarSyntax.Library env)
    (types : BindingTypes inputs (SourceCasts env) bindings (ScalarConversion.Casts setup))
    {a : Piece env ctx p (materialize bindings u) scalarExpected}
    {b : Piece env ctx p (materialize bindings v) scalarExpected}
    (left : ScalarCasts inputs a (SourceCasts env) (ScalarConversion.Casts setup)) (right : ScalarCasts inputs b (SourceCasts env) (ScalarConversion.Casts setup))
    (op : Arithmetic.Binary) (aa ab ac ad oa ob : WordBinder.Annotation)
    (leftTyped : CastTyping env 0 (SourceCasts env) ctx left.sourceCore.val oa.core)
    (rightTyped : CastTyping env 0 (SourceCasts env) ctx right.sourceCore.val ob.core)
    (leftForm : ValueForm setup ctx left.sourceCore.val oa.core)
    (rightForm : ValueForm setup ctx right.sourceCore.val ob.core)
    (fresh : ∀ r ∈ setup.rules, op.method ≠ r.name)
    (coverage : Conversion.Covers conv 0 (ScalarConversion.Casts setup))
    (exposure : Exposure env)
    (leftParsed : visit env conv exposure ctx p u bindings = some a)
    (rightParsed : visit env conv exposure ctx p v bindings = some b)
    (scope : ScalarSyntax.Separated p (materialize bindings (Lean.mkApp2 (nativeHeader op aa ab ac ad) u v))) :
    ∃ piece, visit env conv exposure ctx p (Lean.mkApp2 (nativeHeader op aa ab ac ad) u v) bindings = some piece ∧
      Nonempty (ScalarCasts inputs piece (SourceCasts env) (ScalarConversion.Casts setup)) ∧
      (piece.code = app op.target [a.code,b.code]) := by
  have rep : Represents (materialize bindings (Lean.mkApp2 (nativeHeader op aa ab ac ad) u v))
      (.app (.app (header op aa ab ac ad) left.sourceCore.val) right.sourceCore.val) := by
    rw [materialize_binary]
    exact .app (.app (represented op aa ab ac ad) left.sourceCore.property) right.sourceCore.property
  rcases lookup_typed types (Lean.mkApp2 (nativeHeader op aa ab ac ad) u v) conv with miss | ⟨cached,hit,typed⟩
  · obtain ⟨artifact,checked,typed,_⟩ := ScalarConversion.annotated_binary_finish setup inputs library.toSignatures scalarLibrary
      left right op aa ab ac ad oa ob leftTyped rightTyped leftForm rightForm fresh
      (library.binaryFact op) (library.binaryConstructor op) coverage exposure
    let code := ClosedTerm.app op.target [a.closedTerm,b.closedTerm]
    let art : Artifact env ctx
        (scalarExpected p code.val (materialize bindings (Lean.mkApp2 (nativeHeader op aa ab ac ad) u v))) := by
      simpa only [materialize_binary,code,ClosedTerm.app,Piece.closedTerm] using artifact
    let piece : Piece env ctx p (materialize bindings (Lean.mkApp2 (nativeHeader op aa ab ac ad) u v)) scalarExpected :=
      ⟨code.val,art,code.closed,code.represented⟩
    refine ⟨piece,?_,⟨⟨⟨_,rep⟩,value_typed library.toSignatures op aa ab ac ad left.value right.value,?_,?_⟩⟩,rfl⟩
    · have smallerLeft : syntaxSize u < syntaxSize (Lean.mkApp2 (nativeHeader op aa ab ac ad) u v) := by
        change syntaxSize u < syntaxSize (nativeHeader op aa ab ac ad) + syntaxSize u + 1 + syntaxSize v + 1
        omega
      have smallerRight : syntaxSize v < syntaxSize (Lean.mkApp2 (nativeHeader op aa ab ac ad) u v) := by
        change syntaxSize v < syntaxSize (nativeHeader op aa ab ac ad) + syntaxSize u + 1 + syntaxSize v + 1
        omega
      have leftArg : (arguments (Lean.mkApp2 (nativeHeader op aa ab ac ad) u v))[
          (arguments (Lean.mkApp2 (nativeHeader op aa ab ac ad) u v)).length - 2]? = some ⟨u,smallerLeft⟩ := by
        cases op <;> rfl
      have rightArg : (arguments (Lean.mkApp2 (nativeHeader op aa ab ac ad) u v))[
          (arguments (Lean.mkApp2 (nativeHeader op aa ab ac ad) u v)).length - 1]? = some ⟨v,smallerRight⟩ := by
        cases op <;> rfl
      apply eq_of_heq
      rw [visit] <;> try (solve | intro name ty value next flag h; cases h)
      have head : (Lean.mkApp2 (nativeHeader op aa ab ac ad) u v).getAppFn.constName? = some op.method := by cases op <;> rfl
      simp only [miss,node,head]
      simp [-heq_eq_eq,List.forIn_cons,scope.index,scope.left,scope.right,scope.locals]
      cases op <;> simp [-heq_eq_eq,Arithmetic.Binary.method,leftArg,rightArg,forIn_constant_yield]
      all_goals simp only [leftParsed,rightParsed,Option.bind_some]
      all_goals simp only [Option.bind_assoc,Option.bind_some,Option.bind_fun_some]
      all_goals simp only [materialize_binary] at *
      all_goals apply heq_of_eq
      all_goals cases bindings <;> cases aa <;> cases ab <;> cases ac <;> cases ad <;> simpa [materialize,LeanBindings.substitute,nativeHeader,nativeDictionary,WordBinder.Annotation.native,WordBinder.Annotation.substitute_native,
        Arithmetic.nativeWidth,app,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB,finishScalar,ClosedTerm.app,Piece.closedTerm,code,piece,art,
        Arithmetic.Binary.target,Arithmetic.Binary.fact] using
        congrArg (fun h => h.map (fun artifact =>
          (⟨code.val,artifact,code.closed,code.represented⟩ : Piece env ctx p _ scalarExpected))) checked
    · have fact : CastTyping env 0 (SourceCasts env) ctx (.const op.target [])
          (.forallE exprType (.forallE exprType exprType)) :=
        .constant (library.binaryConstructor op) (by simp) rfl
      have first := CastTyping.application fact left.target
      simp only [exprType,VExpr.inst] at first
      exact .application first right.target
    · cases bindings <;> cases op <;> cases aa <;> cases ab <;> cases ac <;> cases ad <;> simpa [piece,art,materialize,LeanBindings.substitute,
        nativeHeader,nativeDictionary,WordBinder.Annotation.native,WordBinder.Annotation.substitute_native,Arithmetic.nativeWidth,app,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB] using typed
  · simp [ScalarEnvironment.lookup,Lean.mkApp2] at hit

end IRComparison.WordFrontend.AnnotatedBinary
