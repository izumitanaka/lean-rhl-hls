import IRComparison.Frontend.WordBodyCompleteness

/-! The two existing Lean return spellings, `some` and `pure`, share one
successful parser invariant. This tag describes elaboration only; inputs to
the compiler remain ordinary Lean.Expr values. -/
namespace IRComparison.WordFrontend.Certificate.Return
open Lean4Lean LeanTyped LeanTypeInference
variable {casts proofCasts : TypeCasts} [Arithmetic.Includes casts] [Arithmetic.Includes proofCasts]
set_option maxHeartbeats 800000

inductive Form where
  | some | pure

def pureInstance : VExpr := applications (.const ``Applicative.toPure [.zero,.zero])
  [.const ``Option [.zero], applications (.const ``Alternative.toApplicative [.zero,.zero])
    [.const ``Option [.zero],.const ``instAlternativeOption [.zero]]]
def nativePureInstance : Lean.Expr := Lean.mkApp2 (.const ``Applicative.toPure [.zero,.zero])
  (.const ``Option [.zero]) (Lean.mkApp2 (.const ``Alternative.toApplicative [.zero,.zero])
    (.const ``Option [.zero]) (.const ``instAlternativeOption [.zero]))
def Form.header : Form → VExpr
  | .some => .app (.const ``Option.some [.zero]) stateType
  | .pure => applications (.const ``Pure.pure [.zero,.zero]) [.const ``Option [.zero],pureInstance,stateType]
def Form.nativeHeader : Form → Lean.Expr
  | .some => .app (.const ``Option.some [.zero]) state
  | .pure => Lean.mkApp3 (.const ``Pure.pure [.zero,.zero]) (.const ``Option [.zero]) nativePureInstance state

def Form.source (form : Form) (value : Lean.Expr) : Lean.Expr := .app form.nativeHeader value

theorem Form.header_represents (form : Form) : Represents form.nativeHeader form.header := by
  cases form with
  | some => exact .app (.constant rfl) (.constant rfl)
  | pure => exact .app (.app (.app (.constant rfl) (.constant rfl))
      (.app (.app (.constant rfl) (.constant rfl))
        (.app (.app (.constant rfl) (.constant rfl)) (.constant rfl)))) (.constant rfl)

theorem Form.header_inst (form : Form) (v : VExpr) (k : Nat) : form.header.inst v k = form.header := by
  have closed : form.header.ClosedN 0 := form.header_represents.closed 0 (by cases form <;> rfl)
  exact closed.instN_eq (Nat.zero_le k)

def someSignature : VConstant := ⟨1,.forallE (.sort (.succ (.param 0)))
  (.forallE (.bvar 0) (.app (.const ``Option [.param 0]) (.bvar 1)))⟩
def pureSignature : VConstant := ⟨2,
  .forallE (.forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 1))))
    (.forallE (.app (.const ``Pure [.param 0,.param 1]) (.bvar 0))
      (.forallE (.sort (.succ (.param 0))) (.forallE (.bvar 0) (.app (.bvar 3) (.bvar 1)))))⟩
def projectionSignature (parent child : Lean.Name) : VConstant := ⟨2,
  .forallE (.forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 1))))
    (.forallE (.app (.const parent [.param 0,.param 1]) (.bvar 0))
      (.app (.const child [.param 0,.param 1]) (.bvar 1)))⟩
def alternativeSignature : VConstant := ⟨1,
  .app (.const ``Alternative [.param 0,.param 0]) (.const ``Option [.param 0])⟩

structure Signatures (env : VEnv) : Prop where
  state : env.constants ``HybridWord.State = some ⟨0,.sort (.succ .zero)⟩
  option : env.constants ``Option = some optionSignature
  someDecl : env.constants ``Option.some = some someSignature
  pureDecl : env.constants ``Pure.pure = some pureSignature
  applicative : env.constants ``Alternative.toApplicative = some (projectionSignature ``Alternative ``Applicative)
  projectPure : env.constants ``Applicative.toPure = some (projectionSignature ``Applicative ``Pure)
  alternative : env.constants ``instAlternativeOption = some alternativeSignature

def Form.headerFor (form : Form) (ty : VExpr) : VExpr := match form with
  | .some => .app (.const ``Option.some [.zero]) ty
  | .pure => applications (.const ``Pure.pure [.zero,.zero]) [.const ``Option [.zero],pureInstance,ty]

theorem Signatures.headerFor_typed (signatures : Signatures env) (form : Form)
    (typed : DirectTyping env 0 ctx ty (.sort (.succ .zero))) (closed : ty.ClosedN 0) :
    DirectTyping env 0 ctx (form.headerFor ty) (.forallE ty (optionType ty)) := by
  cases form with
  | some =>
    have h : DirectTyping env 0 ctx (.const ``Option.some [.zero]) (someSignature.type.instL [.zero]) :=
      .constant signatures.someDecl (by simp [VLevel.WF]) rfl
    simpa only [VExpr.instL,VLevel.inst,VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower,
      Nat.reduceAdd,List.map_nil,closed.lift_eq,closed.liftN_eq (Nat.zero_le _),VExpr.lift,VExpr.liftN,
      Form.headerFor,optionType,liftVar,Nat.reduceLT,ite_true,ite_false] using DirectTyping.application h typed
  | pure =>
    have ot : DirectTyping env 0 ctx (.const ``Option [.zero])
        (.forallE (.sort (.succ .zero)) (.sort (.succ .zero))) :=
      .constant signatures.option (by simp [VLevel.WF]) rfl
    have alt : DirectTyping env 0 ctx (.const ``instAlternativeOption [.zero])
        (.app (.const ``Alternative [.zero,.zero]) (.const ``Option [.zero])) :=
      .constant signatures.alternative (by simp [VLevel.WF]) rfl
    have ap : DirectTyping env 0 ctx (.const ``Alternative.toApplicative [.zero,.zero])
        ((projectionSignature ``Alternative ``Applicative).type.instL [.zero,.zero]) :=
      .constant signatures.applicative (by simp [VLevel.WF]) rfl
    have ap1 := DirectTyping.application ap ot
    simp only [projectionSignature,VExpr.instL,VLevel.inst,VExpr.inst,VExpr.instVar_zero,
      VExpr.instVar_succ,VExpr.lift,VExpr.liftN,liftVar,Nat.reduceAdd,Nat.reduceLT,ite_true,ite_false] at ap1
    have ap2 := DirectTyping.application ap1 alt
    simp only [VExpr.inst,VExpr.instVar_zero,VExpr.lift,VExpr.liftN] at ap2
    have pp : DirectTyping env 0 ctx (.const ``Applicative.toPure [.zero,.zero])
        ((projectionSignature ``Applicative ``Pure).type.instL [.zero,.zero]) :=
      .constant signatures.projectPure (by simp [VLevel.WF]) rfl
    have pp1 := DirectTyping.application pp ot
    simp only [projectionSignature,VExpr.instL,VLevel.inst,VExpr.inst,VExpr.instVar_zero,
      VExpr.instVar_succ,VExpr.lift,VExpr.liftN,liftVar,Nat.reduceAdd,Nat.reduceLT,ite_true,ite_false] at pp1
    have pp2 := DirectTyping.application pp1 ap2
    simp only [VExpr.inst,VExpr.instVar_zero,VExpr.lift,VExpr.liftN] at pp2
    have h : DirectTyping env 0 ctx (.const ``Pure.pure [.zero,.zero]) (pureSignature.type.instL [.zero,.zero]) :=
      .constant signatures.pureDecl (by simp [VLevel.WF]) rfl
    have h1 := DirectTyping.application h ot
    simp only [pureSignature,VExpr.instL,VLevel.inst,VExpr.inst,VExpr.instVar_zero,
      VExpr.instVar_succ,VExpr.lift,VExpr.liftN,liftVar,Nat.reduceAdd,Nat.reduceLT,ite_true,ite_false] at h1
    have h2 := DirectTyping.application h1 pp2
    simp only [VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.lift,VExpr.liftN] at h2
    simpa only [VExpr.instL,VLevel.inst,VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower,
      Nat.reduceAdd,List.map_nil,closed.lift_eq,closed.liftN_eq (Nat.zero_le _),VExpr.lift,VExpr.liftN,
      Form.headerFor,optionType,liftVar,Nat.reduceLT,ite_true,ite_false] using DirectTyping.application h2 typed

/-- State-return specialization of the common Option-return typing. -/
theorem Signatures.header_typed (signatures : Signatures env) (form : Form) :
    DirectTyping env 0 ctx form.header (.forallE stateType (optionType stateType)) := by
  have typed : DirectTyping env 0 ctx stateType (.sort (.succ .zero)) :=
    .constant signatures.state (by simp) rfl
  exact signatures.headerFor_typed form typed (by trivial)

def Form.fact : Form → Lean.Name
  | .some => ``WordFrontendFacts.skip
  | .pure => ``WordFrontendFacts.skipPure
def Form.result (form : Form) : VExpr := equalValues (optionType stateType)
  (bodyValue (.bvar 4) (.bvar 3) (.bvar 2) (.const ``HybridWord.Cmd.skip []) (.bvar 1) (.bvar 0))
  (.app form.header (.bvar 1))
def Form.signature (form : Form) : VExpr := inputsType form.result

theorem skip_typed (inputs : InputsTyped env ctx p) (form : Form)
    (registered : env.constants form.fact = some ⟨0,form.signature⟩) :
    CastTyping env 0 casts ctx (applications (.const form.fact []) inputs.args)
      (equalValues (optionType stateType)
        (bodyValue inputs.i.val inputs.x.val inputs.y.val (.const ``HybridWord.Cmd.skip []) inputs.s.val inputs.ls.val)
        (.app form.header inputs.s.val)) := by
  have fact : CastTyping env 0 casts ctx (.const form.fact []) form.signature :=
    by cases form <;> exact .constant (levels := []) registered (by simp) rfl
  simpa only [Form.signature,InputsTyped.instantiate,Form.result,bodyValue,equalValues,optionType,stateType,
    applications,Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst_lift,Form.header_inst,VExpr.inst,
    VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] using inputs.apply_casts fact

theorem body_skip_invariant_complete_code (signatures : Signatures env) (inputs : InputsTyped env ctx p)
    (form : Form) (registered : env.constants form.fact = some ⟨0,form.signature⟩)
    (constructor : env.constants ``HybridWord.Cmd.skip = some ⟨0,cmdType⟩)
    (conv : Conversion env) (exposure : Exposure env) (casts : TypeCasts) [Arithmetic.Includes casts] (coverage : conv.Covers 0 casts) :
    ∃ piece, bodyStep env conv exposure (fun _ _ _ => none) (fun _ _ _ => none)
        (fun _ _ => none) (fun _ _ _ => none) ctx p (form.source p.s) = some piece ∧
      Nonempty (BodyCasts inputs piece casts) ∧ piece.code = .const ``HybridWord.Cmd.skip [] := by
  have sourceRep := Represents.app form.header_represents inputs.s.property
  obtain ⟨artifact,checked,proofTyped,_,_⟩ := finish_cast_complete
    (bodyExpected_represents inputs (code := Lean.Expr.const ``HybridWord.Cmd.skip []) (.constant rfl) sourceRep)
    (app_represents (f := Lean.Expr.const form.fact []) (.constant rfl) inputs.arguments) (skip_typed inputs form registered)
    (known := noKnownTypes env 0) (by intro _ _ _ h; cases h) coverage exposure (.const ``HybridWord.Cmd.skip [])
  let code := ClosedTerm.const ``HybridWord.Cmd.skip
  let piece : Piece env ctx p (form.source p.s) bodyExpected := ⟨code.val,artifact,code.closed,code.represented⟩
  refine ⟨piece,?_,⟨⟨⟨_,sourceRep⟩,?_,?_,proofTyped⟩⟩,rfl⟩
  · have same := sameTerm_complete inputs.s.property inputs.s.property
    have reduced : leadingLet (form.source p.s) = none := by cases form <;> rfl
    have head : (form.source p.s).getAppFn.constName? =
        some (match form with | .some => ``Option.some | .pure => ``Pure.pure) := by cases form <;> rfl
    have last : (form.source p.s).getAppArgs.toList.getLast? = some p.s := by cases form <;> rfl
    cases form <;>
      simp only [bodyStep,reduced,head,last] <;>
      simp [same,code,piece,ClosedTerm.const,Form.source,Form.fact] at checked ⊢ <;>
      exact checked
  · exact (DirectTyping.application (signatures.header_typed form) inputs.hs).withCasts casts
  · exact (DirectTyping.constant constructor (by simp) rfl).withCasts casts

theorem body_skip_invariant_complete (signatures : Signatures env) (inputs : InputsTyped env ctx p)
    (form : Form) (registered : env.constants form.fact = some ⟨0,form.signature⟩)
    (constructor : env.constants ``HybridWord.Cmd.skip = some ⟨0,cmdType⟩)
    (conv : Conversion env) (exposure : Exposure env) (casts : TypeCasts) [Arithmetic.Includes casts] (coverage : conv.Covers 0 casts) :
    ∃ piece, bodyStep env conv exposure (fun _ _ _ => none) (fun _ _ _ => none)
        (fun _ _ => none) (fun _ _ _ => none) ctx p (form.source p.s) = some piece ∧
      Nonempty (BodyCasts inputs piece casts) := by
  obtain ⟨piece,success,typed,_⟩ := body_skip_invariant_complete_code signatures inputs form registered
    constructor conv exposure casts coverage
  exact ⟨piece,success,typed⟩

def Form.assignFact : Form → Lean.Name
  | .some => ``WordFrontendFacts.assign
  | .pure => ``WordFrontendFacts.assignPure

def assignConstructor : VExpr := .forallE (.const ``Nat []) (.forallE exprType cmdType)
def setterSignature : VExpr := .forallE stateType (.forallE (.const ``Nat []) (.forallE wordType stateType))

theorem assign_typed (inputs : InputsTyped env ctx p) (form : Form)
    {piece : Piece env ctx p source scalarExpected}
    (register : NatArgument env ctx r) (child : ScalarCasts inputs piece casts)
    (registered : env.constants form.assignFact = some ⟨0,assignSignatureWith form.header⟩) :
    CastTyping env 0 casts ctx
      (applications (.const form.assignFact [])
        ([register.represented.val,piece.represented.val] ++ inputs.args ++
          [child.sourceCore.val,piece.checked.proofCore.val]))
      (equalValues (optionType stateType)
        (bodyValue inputs.i.val inputs.x.val inputs.y.val
          (applications (.const ``HybridWord.Cmd.assign []) [register.represented.val,piece.represented.val])
          inputs.s.val inputs.ls.val)
        (.app form.header (applications (.const ``HybridWord.State.set [])
          [inputs.s.val,register.represented.val,child.sourceCore.val]))) := by
  apply assign_fact_typed inputs register child form.header
    (form.header_represents.closed 0 (by cases form <;> rfl))
  cases form <;> exact .constant registered (by simp) rfl

theorem assign_finish (inputs : InputsTyped env ctx p) (form : Form)
    {piece : Piece env ctx p source scalarExpected}
    (register : NatArgument env ctx r) (child : ScalarCasts inputs piece casts)
    (registered : env.constants form.assignFact = some ⟨0,assignSignatureWith form.header⟩)
    (coverage : Conversion.Covers conv 0 casts) (exposure : Exposure env) :
    ∃ result, finish env conv exposure ctx
      (bodyExpected p (app ``HybridWord.Cmd.assign [r,piece.code])
        (form.source (app ``HybridWord.State.set [p.s,r,source])))
      (app ``HybridWord.Cmd.assign [r,piece.code])
      (app form.assignFact ([r,piece.code] ++ p.args ++ [source,piece.checked.proof]))
      piece.checked.known = some result ∧
      CastTyping env 0 casts ctx result.proofCore.val result.core.val ∧
      result.code = app ``HybridWord.Cmd.assign [r,piece.code] ∧
      result.proof = app form.assignFact ([r,piece.code] ++ p.args ++ [source,piece.checked.proof]) := by
  have targetRep := app_represents (f := Lean.Expr.const ``HybridWord.Cmd.assign []) (.constant rfl)
    (.cons register.represented.property (.cons piece.represented.property .nil))
  have sourceRep := app_represents (f := Lean.Expr.const ``HybridWord.State.set []) (.constant rfl)
    (.cons inputs.s.property (.cons register.represented.property (.cons child.sourceCore.property .nil)))
  have proofRep := app_represents (f := Lean.Expr.const form.assignFact []) (.constant rfl)
    (.cons register.represented.property (.cons piece.represented.property
      (.cons inputs.i.property (.cons inputs.x.property (.cons inputs.y.property
        (.cons inputs.s.property (.cons inputs.ls.property
          (.cons child.sourceCore.property (.cons piece.checked.proofCore.property .nil)))))))))
  exact finish_cast_complete (bodyExpected_represents inputs targetRep
    (.app form.header_represents sourceRep)) proofRep (assign_typed inputs form register child registered)
    (known_casts piece.checked child.proof) coverage exposure _

theorem assign_step_split_complete_code (signatures : Signatures env) (inputs : InputsTyped env ctx p)
    (form : Form) {piece : Piece env ctx p source scalarExpected}
    (register : NatArgument env ctx r) (child : ScalarCasts inputs piece casts proofCasts)
    (registered : env.constants form.assignFact = some ⟨0,assignSignatureWith form.header⟩)
    (constructor : env.constants ``HybridWord.Cmd.assign = some ⟨0,assignConstructor⟩)
    (setter : env.constants ``HybridWord.State.set = some ⟨0,setterSignature⟩)
    (embeds : ∀ scope a b, casts scope a b → proofCasts scope a b)
    (coverage : Conversion.Covers conv 0 proofCasts) (exposure : Exposure env)
    (scalarCall : PieceParser env scalarExpected) (readCall : PieceParser env readExpected)
    (stepCall : StepParser env) (bodyCall : PieceParser env bodyExpected)
    (parsed : scalarCall ctx p source = some piece) :
    ∃ result, bodyStep env conv exposure scalarCall readCall stepCall bodyCall ctx p
      (form.source (app ``HybridWord.State.set [p.s,r,source])) = some result ∧
      Nonempty (BodyCasts inputs result casts proofCasts) ∧
      result.code = app ``HybridWord.Cmd.assign [r,piece.code] := by
  obtain ⟨artifact,checked,proofTyped,_,_⟩ := assign_finish inputs form register (child.inProofCasts embeds) registered coverage exposure
  obtain ⟨rc,translated,rcSame⟩ := register.represented.property.translate_complete
  let registerCode : ClosedTerm := ⟨r,register.closed,rc⟩
  let code := ClosedTerm.app ``HybridWord.Cmd.assign [registerCode,piece.closedTerm]
  let result : Piece env ctx p (form.source (app ``HybridWord.State.set [p.s,r,source])) bodyExpected :=
    ⟨code.val,artifact,code.closed,code.represented⟩
  have setRep := app_represents (f := Lean.Expr.const ``HybridWord.State.set []) (.constant rfl)
    (.cons inputs.s.property (.cons register.represented.property (.cons child.sourceCore.property .nil)))
  refine ⟨result,?_,⟨⟨⟨_,.app form.header_represents setRep⟩,?_,?_,proofTyped⟩⟩,rfl⟩
  · have same := sameTerm_complete inputs.s.property inputs.s.property
    have different : sameTerm (app ``HybridWord.State.set [p.s,r,source]) p.s = false := by
      cases found : sameTerm (app ``HybridWord.State.set [p.s,r,source]) p.s with
      | false => rfl
      | true =>
        have sizes := congrArg sizeOf (sameTerm_sound setRep inputs.s.property found)
        simp [applications] at sizes
        omega
    have reduced : leadingLet (form.source (app ``HybridWord.State.set [p.s,r,source])) = none := by cases form <;> rfl
    have head : (form.source (app ``HybridWord.State.set [p.s,r,source])).getAppFn.constName? =
        some (match form with | .some => ``Option.some | .pure => ``Pure.pure) := by cases form <;> rfl
    have last : (form.source (app ``HybridWord.State.set [p.s,r,source])).getAppArgs.toList.getLast? =
        some (app ``HybridWord.State.set [p.s,r,source]) := by cases form <;> rfl
    have setHead : (app ``HybridWord.State.set [p.s,r,source]).getAppFn.constName? = some ``HybridWord.State.set := rfl
    have setArgs : (app ``HybridWord.State.set [p.s,r,source]).getAppArgs.toList = [p.s,r,source] := rfl
    simp only [app,List.foldl_cons,List.foldl_nil] at different setHead setArgs
    cases form <;>
      simp only [bodyStep,reduced,head,last] <;>
      simp [different,setHead,setArgs,same,parsed,closedTerm,register.closed,translated,
        ClosedTerm.app,ClosedTerm.const,Piece.closedTerm,registerCode,code,result,Form.source,Form.assignFact,
        app] at checked ⊢ <;>
      exact checked
  · have h : CastTyping env 0 casts ctx (.const ``HybridWord.State.set []) setterSignature :=
      .constant setter (by simp) rfl
    have a1 := CastTyping.application h (inputs.hs.withCasts casts)
    simp only [setterSignature,stateType,wordType,VExpr.inst] at a1
    have a2 := CastTyping.application a1 (register.typed.withCasts casts)
    simp only [VExpr.inst] at a2
    exact .application ((signatures.header_typed form).withCasts casts) (.checkedApplication a2 child.value)
  · have h : CastTyping env 0 casts ctx (.const ``HybridWord.Cmd.assign []) assignConstructor :=
      .constant constructor (by simp) rfl
    have a1 := CastTyping.application h (register.typed.withCasts casts)
    simp only [assignConstructor,cmdType,exprType,VExpr.inst] at a1
    change CastTyping env 0 casts ctx
      (applications (.const ``HybridWord.Cmd.assign []) [rc.val,piece.represented.val]) cmdType
    rw [rcSame]
    exact .application a1 child.target


theorem assign_step_split_complete (signatures : Signatures env) (inputs : InputsTyped env ctx p)
    (form : Form) {piece : Piece env ctx p source scalarExpected}
    (register : NatArgument env ctx r) (child : ScalarCasts inputs piece casts proofCasts)
    (registered : env.constants form.assignFact = some ⟨0,assignSignatureWith form.header⟩)
    (constructor : env.constants ``HybridWord.Cmd.assign = some ⟨0,assignConstructor⟩)
    (setter : env.constants ``HybridWord.State.set = some ⟨0,setterSignature⟩)
    (embeds : ∀ scope a b, casts scope a b → proofCasts scope a b)
    (coverage : Conversion.Covers conv 0 proofCasts) (exposure : Exposure env)
    (scalarCall : PieceParser env scalarExpected) (readCall : PieceParser env readExpected)
    (stepCall : StepParser env) (bodyCall : PieceParser env bodyExpected)
    (parsed : scalarCall ctx p source = some piece) :
    ∃ result, bodyStep env conv exposure scalarCall readCall stepCall bodyCall ctx p
      (form.source (app ``HybridWord.State.set [p.s,r,source])) = some result ∧
      Nonempty (BodyCasts inputs result casts proofCasts) := by
  obtain ⟨result,success,typed,_⟩ := assign_step_split_complete_code signatures inputs form register child
    registered constructor setter embeds coverage exposure scalarCall readCall stepCall bodyCall parsed
  exact ⟨result,success,typed⟩


theorem assign_step_complete (signatures : Signatures env) (inputs : InputsTyped env ctx p)
    (form : Form) {piece : Piece env ctx p source scalarExpected}
    (register : NatArgument env ctx r) (child : ScalarCasts inputs piece casts)
    (registered : env.constants form.assignFact = some ⟨0,assignSignatureWith form.header⟩)
    (constructor : env.constants ``HybridWord.Cmd.assign = some ⟨0,assignConstructor⟩)
    (setter : env.constants ``HybridWord.State.set = some ⟨0,setterSignature⟩)
    (coverage : Conversion.Covers conv 0 casts) (exposure : Exposure env)
    (scalarCall : PieceParser env scalarExpected) (readCall : PieceParser env readExpected)
    (stepCall : StepParser env) (bodyCall : PieceParser env bodyExpected)
    (parsed : scalarCall ctx p source = some piece) :
    ∃ result, bodyStep env conv exposure scalarCall readCall stepCall bodyCall ctx p
      (form.source (app ``HybridWord.State.set [p.s,r,source])) = some result ∧
      Nonempty (BodyCasts inputs result casts) := by
  exact assign_step_split_complete signatures inputs form register child registered constructor setter
    (fun _ _ _ h => h) coverage exposure scalarCall readCall stepCall bodyCall parsed

end IRComparison.WordFrontend.Certificate.Return
