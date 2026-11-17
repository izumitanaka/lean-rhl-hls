import IRComparison.Frontend.WordAnnotatedLet

/-! The BitVec spelling of an Option-valued do-read preserves its actual
binder type. The ordinary Word case uses the existing read-binding rule. -/
namespace IRComparison.WordFrontend.WordBinder
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic StructuralBody
set_option maxHeartbeats 1800000

def readSource (annotation : Annotation) (first next : Lean.Expr) : Lean.Expr :=
  Lean.mkApp2 (bindHead annotation.native state) first next

/-- Reuse the same checked Option conversion in ordinary and loop do-binds. -/
theorem checked_option_bitvec
    (optionDeclared : env.constants ``Option = some optionSignature)
    (value : CheckedTyping env 0 (SourceCasts env) ctx source (optionType wordType)) :
    CheckedTyping env 0 (SourceCasts env) ctx source (optionType bitvecType) := by
  cases value with
  | exact typed => exact .converted typed (.wordOption optionDeclared)
  | converted typed cast =>
    have only {a b : VExpr} (conversion : SourceCasts env ctx a b) (same : b = optionType wordType) :
        a = optionType bitvecType := by
      cases conversion with
      | arithmetic conversion =>
        cases conversion with
        | wordInstance op => cases op <;> simp [optionType,wordType,Binary.className] at same
        | bitvecValue | resultType | negInstance | literalInstance =>
          simp [optionType,wordType,resultParameter,applications] at same
      | bitvecOption => rfl
      | heterogeneous op => cases op <;> simp [Arithmetic.Binary.classApplication,Arithmetic.Binary.heterogeneous,applications,optionType] at same
      | readDictionary => cases (VExpr.app.inj same).1
      | wordValue | wordOption | wordFunction | levelEquality | parameter | decisionInstance | decisionFunction =>
        simp [optionType,wordType,bitvecType,decEqFunction] at same
    rw [only cast rfl] at typed
    exact .exact typed

theorem substitute_readSource (σ : Substitution) (annotation : Annotation) :
    σ.apply (readSource annotation first (.lam binder annotation.native nextBody info)) =
      readSource annotation (σ.apply first) (.lam binder annotation.native ((under σ).apply nextBody) info) := by
  cases annotation <;> cases σ <;> rfl

theorem mapped_bind_bits_complete_code (setup : AliasSetup env) (library : Signatures env)
    (bindLibrary : BindSignatures env) (inputs : InputsTyped env ctx p) (closed : ClosedConstantTypes env)
    (consDeclared : env.constants ``List.cons = some consSignature)
    (stateDeclared : env.constants ``HybridWord.State = some ⟨0,.sort (.succ .zero)⟩)
    (eqDeclared : env.constants ``Eq = some eqSignature)
    (evalDeclared : env.constants ``HybridWord.Cmd.eval = some ⟨0,evalSignature⟩)
    (factDeclared : env.constants ``WordFrontendFacts.bindValue = some ⟨0,bindValueSignature⟩)
    (constructor : env.constants ``HybridWord.Cmd.letValue = some ⟨0,bindValueConstructor⟩)
    (stateFresh : ∀ r ∈ setup.rules, ``HybridWord.State ≠ r.name)
    (bindFresh : ∀ r ∈ setup.rules, ``Bind.bind ≠ r.name)
    (coverage : Conversion.Covers setup.conversion 0 (For.Casts setup)) (exposure : Exposure env)
    {a : Piece env ctx p (σ.apply first) readExpected}
    (left : Read.ReadCasts inputs a (SourceCasts env) (For.Casts setup))
    (firstForm : ValueForm setup ctx left.sourceCore.val (optionType wordType))
    {b : Piece env (bitvecType::ctx) {p.lift with locals := .bvar 0::p.lift.locals} ((under σ).apply nextBody) bodyExpected}
    (right : BodyCasts (Annotation.bitvec.nextInputs inputs closed library consDeclared) b
      (SourceCasts env) (For.Casts setup))
    (form : ValueForm setup (bitvecType::ctx) right.sourceCore.val (optionType stateType))
    (firstParsed : readStep env setup.conversion exposure ctx p
      (ScalarEnvironment.parse env setup.conversion exposure ctx p) (σ.apply first) = some a)
    (nextParsed : visit env setup.conversion exposure nextBody (bitvecType::ctx)
      {p.lift with locals := .bvar 0::p.lift.locals} .body (under σ) (underFunctions fs) = some b)
    (binder : Lean.Name) (info : Lean.BinderInfo) :
    ∃ piece, visit env setup.conversion exposure
      (readSource .bitvec first (.lam binder Annotation.bitvec.native nextBody info)) ctx p .body σ fs = some piece ∧
      ∃ typed : BodyCasts inputs piece (SourceCasts env) (For.Casts setup),
        ValueForm setup ctx typed.sourceCore.val (optionType stateType) ∧ piece.code = app ``HybridWord.Cmd.letValue [a.code,b.code] := by
  have embed : ∀ scope a b, SourceCasts env scope a b → For.Casts setup scope a b :=
    fun _ _ _ h => .base (.base (.source h))
  have targetClosed : b.represented.val.ClosedN 0 := b.represented.property.closed 0 b.closed
  have target := right.target.closed_context SourceCasts.closed targetClosed ctx
  have nextTyped := CastTyping.lambda (Annotation.bitvec.type_typed library |>.withCasts (SourceCasts env)) right.value
  have resultTyped {ctx : List VExpr} : DirectTyping env 0 ctx (optionType stateType) (.sort (.succ .zero)) :=
    .application (.constant bindLibrary.option (by simp [VLevel.WF]) rfl)
      (.constant stateDeclared (by simp) rfl)
  have nextChecked : CheckedTyping env 0 (SourceCasts env) ctx
      (.lam bitvecType right.sourceCore.val) (.forallE wordType (optionType stateType)) :=
    .converted nextTyped (.wordFunction resultTyped)
  have liftedTarget : CastTyping env 0 (SourceCasts env) (bitvecType::ctx) b.represented.val.lift cmdType := by
    simpa only [cmdType,VExpr.lift,VExpr.liftN] using target.lift closed SourceCasts.closed bitvecType
  have evaluation := eval_cast_typed (Annotation.bitvec.nextInputs inputs closed library consDeclared) evalDeclared liftedTarget
  have prefixTyped := CastTyping.application
    ((equality_head_typed (ctx := bitvecType::ctx) stateDeclared bindLibrary.option eqDeclared).withCasts (SourceCasts env)) evaluation
  simp only [WordFrontend.optionState,stateType,VExpr.inst] at prefixTyped
  have beta := For.Casts.annotatedContinuation (setup := setup) Annotation.bitvec
    (resultType := optionType stateType) (by trivial) (by intro u; simp [optionType]) prefixTyped right.value form
  have nextProof := CastTyping.lambda (library.bitvec_typed.withCasts (For.Casts setup)) right.equality
  have bvLift : bitvecType.liftN 1 = bitvecType := (Annotation.closed .bitvec).liftN_eq (Nat.zero_le 0)
  have certificate := bindValue_typed inputs
    (⟨left.sourceCore,left.value.mono embed,left.target.mono embed,left.proof⟩ : Read.ReadCasts inputs a (For.Casts setup))
    (target.mono embed) (nextChecked.mono embed) nextProof (by
      simpa only [bindValueContinuationType,Annotation.nextInputs,InputsTyped.withLocal,InputsTyped.lift,
        continuationValue,targetClosed.lift_eq,VExpr.lift,VExpr.liftN,
        Annotation.core,bvLift] using beta) factDeclared
  obtain ⟨artifact,checked,proofTyped,_,_⟩ := finish_cast_complete
    (expected := bodyExpected p (app ``HybridWord.Cmd.letValue [a.code,b.code])
      (bindValueSource (σ.apply first) (.lam binder Annotation.bitvec.native ((under σ).apply nextBody) info)))
    (proof := app ``WordFrontendFacts.bindValue ([a.code,b.code] ++ p.args ++
      [σ.apply first,.lam binder Annotation.bitvec.native ((under σ).apply nextBody) info,a.checked.proof,
        .lam binder Annotation.bitvec.native b.checked.proof info]))
    (bodyExpected_represents inputs
      (app_represents (.constant rfl) (.cons a.represented.property (.cons b.represented.property .nil)))
      (.app (.app valueBind_represents left.sourceCore.property) (.lam Annotation.bitvec.represented right.sourceCore.property)))
    (app_represents (.constant rfl) (.cons a.represented.property (.cons b.represented.property
      (.cons inputs.i.property (.cons inputs.x.property (.cons inputs.y.property
        (.cons inputs.s.property (.cons inputs.ls.property (.cons left.sourceCore.property
          (.cons (.lam Annotation.bitvec.represented right.sourceCore.property)
            (.cons a.checked.proofCore.property (.cons (.lam Annotation.bitvec.represented b.checked.proofCore.property) .nil))))))))))))
    certificate ((known_casts a.checked left.proof).orElse (known_casts b.checked right.proof)) coverage exposure
    (app ``HybridWord.Cmd.letValue [a.code,b.code])
  let code := ClosedTerm.app ``HybridWord.Cmd.letValue [a.closedTerm,b.closedTerm]
  have head : CastTyping env 0 (SourceCasts env) ctx (.const ``HybridWord.Cmd.letValue []) bindValueConstructor :=
    .constant constructor (by simp) rfl
  have codeTyped := CastTyping.application (CastTyping.application head left.target) target
  have evaluation := eval_cast_typed inputs evalDeclared codeTyped
  have prefixTyped := CastTyping.application
    ((equality_head_typed stateDeclared bindLibrary.option eqDeclared).withCasts (SourceCasts env)) evaluation
  simp only [WordFrontend.optionState,stateType,VExpr.inst] at prefixTyped
  have sourceRep : Represents (readSource .bitvec (σ.apply first) (.lam binder Annotation.bitvec.native ((under σ).apply nextBody) info))
      (bindValueAnnotated bitvecType left.sourceCore.val (.lam bitvecType right.sourceCore.val)) :=
    .app (.app (.app (.app (.app (.app (.constant rfl) (.constant rfl))
      (.app (.app (.constant rfl) (.constant rfl)) (.constant rfl))) Annotation.bitvec.represented) (.constant rfl))
      left.sourceCore.property) (.lam Annotation.bitvec.represented right.sourceCore.property)
  have stateTyped : DirectTyping env 0 ctx stateType (.sort (.succ .zero)) :=
    .constant stateDeclared (by simp) rfl
  have headerTyped := bindLibrary.header_typed (Annotation.bitvec.type_typed library)
    stateTyped Annotation.bitvec.closed (by trivial)
  have firstChecked := checked_option_bitvec bindLibrary.option left.value
  have readApplied := CastTyping.checkedApplication (headerTyped.withCasts (SourceCasts env)) firstChecked
  simp only [Annotation.core, (Annotation.closed .bitvec).instN_eq (Nat.zero_le _),
    optionType,stateType,VExpr.inst] at readApplied
  have bvInst : bitvecType.inst left.sourceCore.val = bitvecType :=
    (Annotation.closed .bitvec).instN_eq (Nat.zero_le 0)
  rw [bvInst] at readApplied
  have sourceTyped := CastTyping.application readApplied nextTyped
  have sourceSame := substitute_readSource (binder := binder) (first := first) (nextBody := nextBody) (info := info) σ .bitvec
  rw [← sourceSame] at sourceRep
  have actualRep := bodyExpected_represents inputs code.represented.property sourceRep
  have cast : For.Casts setup ctx artifact.core.val
      (equalValues (optionType stateType)
        (bodyValue inputs.i.val inputs.x.val inputs.y.val code.represented.val inputs.s.val inputs.ls.val)
        (bindValueAnnotated bitvecType left.sourceCore.val (.lam bitvecType right.sourceCore.val))) := by
    rw [artifact.core.property.unique (bodyExpected_represents inputs code.represented.property
      (Represents.app (.app valueBind_represents left.sourceCore.property) (.lam Annotation.bitvec.represented right.sourceCore.property)))]
    exact .annotatedReadEquality bindLibrary (fun _ => .constant stateDeclared (by simp) rfl)
      (by trivial) rfl stateFresh rfl bindFresh prefixTyped left.value firstForm right.value
  obtain ⟨transported,retargeted,transportTyped⟩ := ScalarEnvironment.retarget_cast_complete artifact actualRep
    proofTyped ((CastTyping.application prefixTyped sourceTyped).mono embed) cast coverage
  let piece : Piece env ctx p (σ.apply (readSource .bitvec first (.lam binder Annotation.bitvec.native nextBody info))) bodyExpected :=
    ⟨code.val,transported,code.closed,code.represented⟩
  let typed : BodyCasts inputs piece (SourceCasts env) (For.Casts setup) :=
    ⟨⟨_,sourceRep⟩,sourceTyped,codeTyped,transportTyped⟩
  refine ⟨piece,?_,typed,?_,rfl⟩
  · have sc := Annotation.bitvec.compatible setup library (ctx := ctx)
    have notState : sameTerm Annotation.bitvec.native state = false := rfl
    have notWord : sameTerm Annotation.bitvec.native word = false := rfl
    have notUnit : sameTerm Annotation.bitvec.native (.const ``PUnit [.succ .zero]) = false := rfl
    have translated : translate Annotation.bitvec.native = some ⟨bitvecType,Annotation.bitvec.represented⟩ := rfl
    have empty : underFunctions (fun _ => (none : Option (Continuation env))) = (fun _ => none) := by funext n; cases n <;> rfl
    have modeValue : (Mode.body == Mode.value) = false := rfl
    have modeStep : (Mode.body == Mode.step) = false := rfl
    have modeBody : (Mode.body == Mode.body) = true := rfl
    have annotationApply : σ.apply Annotation.bitvec.native = Annotation.bitvec.native := by
      rw [Substitution.apply_eq,Annotation.substitute_native]
    have translatedMapped : (translate (σ.apply Annotation.bitvec.native)).unattach = some bitvecType := by
      rw [annotationApply]; rfl
    have lambdaSame : σ.apply (.lam binder Annotation.bitvec.native nextBody info) =
        .lam binder Annotation.bitvec.native ((under σ).apply nextBody) info := by
      cases σ <;> rfl
    rw [visit]
    simp [node,modeValue,modeStep,modeBody,letParts,applicationHead,makeContinuation,continuationParts,lambdaChain,
      ScalarEnvironment.arguments,ScalarEnvironment.below,lambdaParts,annotationApply,
      readSource,bindHead,Lean.mkAppN,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB,
      Lean.Expr.getAppFn,Lean.Expr.constName?,notState,notWord,notUnit,sc,translated]
    simp [firstParsed,nextParsed,finishBody,retargetPiece,Mode.expected,ClosedTerm.app,Piece.closedTerm,
      translatedMapped,lambdaSame,code,piece,bindValueSource,readSource,bindHead,Lean.mkApp2,Lean.mkAppB,Lean.mkApp,app] at checked retargeted ⊢
    refine ⟨first,rfl,a,firstParsed,b,rfl,?_⟩
    have bodyNotValue : (Mode.body != Mode.value) = true := rfl
    simp only [bodyNotValue,ite_true,lambdaSame]
    cases σ
    all_goals
      simp only [Substitution.apply,LeanBindings.substitute,under,Annotation.native,Arithmetic.nativeWidth,
        app,List.foldl_cons,List.foldl_nil,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB] at checked retargeted ⊢
      rw [checked]
      simp only [Option.bind]
      rw [retargeted]
      rfl
  · exact .constant rfl bindFresh (by decide)

theorem bind_bits_complete_code (setup : AliasSetup env) (library : Signatures env)
    (bindLibrary : BindSignatures env) (inputs : InputsTyped env ctx p) (closed : ClosedConstantTypes env)
    (consDeclared : env.constants ``List.cons = some consSignature)
    (stateDeclared : env.constants ``HybridWord.State = some ⟨0,.sort (.succ .zero)⟩)
    (eqDeclared : env.constants ``Eq = some eqSignature)
    (evalDeclared : env.constants ``HybridWord.Cmd.eval = some ⟨0,evalSignature⟩)
    (factDeclared : env.constants ``WordFrontendFacts.bindValue = some ⟨0,bindValueSignature⟩)
    (constructor : env.constants ``HybridWord.Cmd.letValue = some ⟨0,bindValueConstructor⟩)
    (stateFresh : ∀ r ∈ setup.rules, ``HybridWord.State ≠ r.name)
    (bindFresh : ∀ r ∈ setup.rules, ``Bind.bind ≠ r.name)
    (coverage : Conversion.Covers setup.conversion 0 (For.Casts setup)) (exposure : Exposure env)
    {a : Piece env ctx p first readExpected}
    (left : Read.ReadCasts inputs a (SourceCasts env) (For.Casts setup))
    (firstForm : ValueForm setup ctx left.sourceCore.val (optionType wordType))
    {b : Piece env (bitvecType::ctx) {p.lift with locals := .bvar 0::p.lift.locals} nextBody bodyExpected}
    (right : BodyCasts (Annotation.bitvec.nextInputs inputs closed library consDeclared) b
      (SourceCasts env) (For.Casts setup))
    (form : ValueForm setup (bitvecType::ctx) right.sourceCore.val (optionType stateType))
    (firstParsed : readStep env setup.conversion exposure ctx p
      (ScalarEnvironment.parse env setup.conversion exposure ctx p) first = some a)
    (nextParsed : StructuralBody.bodyRetained env setup.conversion exposure (bitvecType::ctx)
      {p.lift with locals := .bvar 0::p.lift.locals} nextBody = some b)
    (binder : Lean.Name) (info : Lean.BinderInfo) :
    ∃ piece, StructuralBody.bodyRetained env setup.conversion exposure ctx p
      (readSource .bitvec first (.lam binder Annotation.bitvec.native nextBody info)) = some piece ∧
      ∃ typed : BodyCasts inputs piece (SourceCasts env) (For.Casts setup),
        ValueForm setup ctx typed.sourceCore.val (optionType stateType) ∧
        piece.code = app ``HybridWord.Cmd.letValue [a.code,b.code] := by
  have empty : underFunctions (fun _ => (none : Option (Continuation env))) = (fun _ => none) := by
    funext n; cases n <;> rfl
  obtain ⟨piece,success,typed,form,code⟩ := mapped_bind_bits_complete_code (σ := .identity) (fs := fun _ => none)
    (first := first) (nextBody := nextBody) setup library bindLibrary inputs closed consDeclared stateDeclared
    eqDeclared evalDeclared factDeclared constructor stateFresh bindFresh coverage exposure
    left firstForm right form firstParsed (by simpa only [under,empty] using nextParsed) binder info
  exact ⟨piece,success,typed,form,code⟩

/-- Projection of the same construction for callers that do not inspect the code. -/
theorem bind_bits_complete (setup : AliasSetup env) (library : Signatures env)
    (bindLibrary : BindSignatures env) (inputs : InputsTyped env ctx p) (closed : ClosedConstantTypes env)
    (consDeclared : env.constants ``List.cons = some consSignature)
    (stateDeclared : env.constants ``HybridWord.State = some ⟨0,.sort (.succ .zero)⟩)
    (eqDeclared : env.constants ``Eq = some eqSignature)
    (evalDeclared : env.constants ``HybridWord.Cmd.eval = some ⟨0,evalSignature⟩)
    (factDeclared : env.constants ``WordFrontendFacts.bindValue = some ⟨0,bindValueSignature⟩)
    (constructor : env.constants ``HybridWord.Cmd.letValue = some ⟨0,bindValueConstructor⟩)
    (stateFresh : ∀ r ∈ setup.rules, ``HybridWord.State ≠ r.name)
    (bindFresh : ∀ r ∈ setup.rules, ``Bind.bind ≠ r.name)
    (coverage : Conversion.Covers setup.conversion 0 (For.Casts setup)) (exposure : Exposure env)
    {a : Piece env ctx p first readExpected}
    (left : Read.ReadCasts inputs a (SourceCasts env) (For.Casts setup))
    (firstForm : ValueForm setup ctx left.sourceCore.val (optionType wordType))
    {b : Piece env (bitvecType::ctx) {p.lift with locals := .bvar 0::p.lift.locals} nextBody bodyExpected}
    (right : BodyCasts (Annotation.bitvec.nextInputs inputs closed library consDeclared) b
      (SourceCasts env) (For.Casts setup))
    (form : ValueForm setup (bitvecType::ctx) right.sourceCore.val (optionType stateType))
    (firstParsed : readStep env setup.conversion exposure ctx p
      (ScalarEnvironment.parse env setup.conversion exposure ctx p) first = some a)
    (nextParsed : StructuralBody.bodyRetained env setup.conversion exposure (bitvecType::ctx)
      {p.lift with locals := .bvar 0::p.lift.locals} nextBody = some b)
    (binder : Lean.Name) (info : Lean.BinderInfo) :
    ∃ piece, StructuralBody.bodyRetained env setup.conversion exposure ctx p
      (readSource .bitvec first (.lam binder Annotation.bitvec.native nextBody info)) = some piece ∧
      ∃ typed : BodyCasts inputs piece (SourceCasts env) (For.Casts setup),
        ValueForm setup ctx typed.sourceCore.val (optionType stateType) := by
  obtain ⟨piece,success,typed,form,_⟩ := bind_bits_complete_code setup library bindLibrary inputs closed
    consDeclared stateDeclared eqDeclared evalDeclared factDeclared constructor stateFresh bindFresh
    coverage exposure left firstForm right form firstParsed nextParsed binder info
  exact ⟨piece,success,typed,form⟩

end IRComparison.WordFrontend.WordBinder
