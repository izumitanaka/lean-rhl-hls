import IRComparison.Frontend.WordTraversalCompleteness
import IRComparison.Frontend.WordScalarTypes

/-! Typing and successful construction of the actual frontend certificates.
The premises below describe the installed library signatures and the types of
in-scope source values. They do not assume a successful certificate checker.
This module is proof infrastructure, not a new source language or evaluator. -/
namespace IRComparison.WordFrontend.Certificate
open Lean4Lean LeanTyped LeanTypeInference

/-- Success with the exact cached children used by production. The returned
invariant supports induction on syntax, instead of assuming that the next
certificate check succeeds. -/
theorem finish_known_complete
    (expectedRep : Represents expected expectedCore)
    (proofRep : Represents proof proofCore)
    (typed : DirectTyping env 0 ctx proofCore expectedCore)
    (coherent : KnownTypes.Direct known)
    (conv : Conversion env) (exposure : Exposure env) (code : Lean.Expr) :
    ∃ result, finish env conv exposure ctx expected code proof known = some result ∧
      DirectTyping env 0 ctx result.proofCore.val result.core.val ∧
      result.code = code ∧ result.proof = proof := by
  obtain ⟨⟨ec,he⟩,translatedExpected,sameExpected⟩ := expectedRep.translate_complete
  obtain ⟨⟨pc,hp⟩,translatedProof,sameProof⟩ := proofRep.translate_complete
  dsimp only at sameExpected sameProof
  subst ec; subst pc
  obtain ⟨⟨_,inferred⟩,accepted,same⟩ := typed.infer_known_complete coherent conv exposure
  dsimp only at same
  subst expectedCore
  simp only [finish,translatedExpected,translatedProof,bind,Option.bind,accepted,dif_pos rfl]
  exact ⟨_,rfl,typed,rfl,rfl⟩


theorem finish_cast_complete
    (expectedRep : Represents expected expectedCore)
    (proofRep : Represents proof proofCore)
    (typed : CastTyping env 0 casts ctx proofCore expectedCore)
    (coherent : KnownTypes.Casts known casts)
    (coverage : Conversion.Covers conv 0 casts) (exposure : Exposure env) (code : Lean.Expr) :
    ∃ result, finish env conv exposure ctx expected code proof known = some result ∧
      CastTyping env 0 casts ctx result.proofCore.val result.core.val ∧
      result.code = code ∧ result.proof = proof := by
  obtain ⟨⟨ec,he⟩,translatedExpected,sameExpected⟩ := expectedRep.translate_complete
  obtain ⟨⟨pc,hp⟩,translatedProof,sameProof⟩ := proofRep.translate_complete
  dsimp only at sameExpected sameProof
  subst ec; subst pc
  obtain ⟨⟨_,inferred⟩,accepted,same⟩ := typed.infer_complete coherent coverage exposure
  dsimp only at same
  subst expectedCore
  simp only [finish,translatedExpected,translatedProof,bind,Option.bind,accepted,dif_pos rfl]
  exact ⟨_,rfl,typed,rfl,rfl⟩


/-- A converted certificate also leaves an exact-type term for enclosing
syntax rules. The conversion is part of the typing specification, and its
coverage is proved separately; success is not an input premise. -/
theorem finish_checked_complete
    (expectedRep : Represents expected expectedCore)
    (proofRep : Represents proof proofCore)
    (typed : CheckedTyping env 0 casts ctx proofCore expectedCore)
    (expectedTyped : CastTyping env 0 casts ctx expectedCore (.sort u))
    (coherent : KnownTypes.Casts known casts)
    (coverage : Conversion.Covers conv 0 casts) (exposure : Exposure env) (code : Lean.Expr) :
    ∃ result, finish env conv exposure ctx expected code proof known = some result ∧
      CastTyping env 0 casts ctx result.proofCore.val result.core.val ∧ result.code = code := by
  cases typed with
  | exact typed =>
    obtain ⟨result,done,typed,codeEq,_⟩ := finish_cast_complete expectedRep proofRep typed coherent coverage exposure code
    exact ⟨result,done,typed,codeEq⟩
  | @converted actual expectedCore typed cast =>
    obtain ⟨⟨ec,he⟩,translatedExpected,sameExpected⟩ := expectedRep.translate_complete
    obtain ⟨⟨pc,hp⟩,translatedProof,sameProof⟩ := proofRep.translate_complete
    dsimp only at sameExpected sameProof
    subst ec; subst pc
    obtain ⟨⟨actualType,inferred⟩,accepted,same⟩ := typed.infer_complete coherent coverage exposure
    dsimp only at same
    subst actualType
    by_cases identical : actual = expectedCore
    · subst actual
      simp only [finish,translatedExpected,translatedProof,bind,Option.bind,accepted,dif_pos rfl]
      exact ⟨_,rfl,typed,rfl⟩
    · obtain ⟨equation,converted⟩ := coverage ctx actual expectedCore cast
      have identity : CastTyping env 0 casts ctx (.lam expectedCore (.bvar 0))
          (.forallE expectedCore expectedCore.lift) := .lambda expectedTyped (.bvar .zero)
      have transported := CastTyping.convertedApplication identity typed cast
      simp only [VExpr.inst_lift] at transported
      simp only [finish,translatedExpected,translatedProof,bind,Option.bind,accepted,dif_neg identical,converted]
      exact ⟨_,rfl,transported,rfl⟩


structure InputsTyped (env : VEnv) (ctx : List VExpr) (p : Inputs) where
  i : {core // Represents p.i core}
  x : {core // Represents p.x core}
  y : {core // Represents p.y core}
  s : {core // Represents p.s core}
  ls : {core // Represents p.list core}
  hi : DirectTyping env 0 ctx i.val wordType
  hx : DirectTyping env 0 ctx x.val wordType
  hy : DirectTyping env 0 ctx y.val wordType
  hs : DirectTyping env 0 ctx s.val stateType
  hl : CastTyping env 0 Arithmetic.Casts ctx ls.val wordsType

/-- Compatibility condition used only by the older conversion-free lemmas.
The general scope invariant above permits the ordinary Word/BitVec alias. -/
class InputsTyped.DirectLocals (inputs : InputsTyped env ctx p) : Prop where
  typed : DirectTyping env 0 ctx inputs.ls.val wordsType

theorem InputsTyped.directLocals (inputs : InputsTyped env ctx p) [h : inputs.DirectLocals] :
    DirectTyping env 0 ctx inputs.ls.val wordsType := h.typed

/-- The particular conversion relation used by a certificate can type the
current locals list. This is a type derivation, not a checker outcome. -/
class InputsTyped.CastLocals (inputs : InputsTyped env ctx p) (casts : TypeCasts) : Prop where
  typed : CastTyping env 0 casts ctx inputs.ls.val wordsType

instance (inputs : InputsTyped env ctx p) [Arithmetic.Includes casts] : inputs.CastLocals casts :=
  ⟨inputs.hl.mono Arithmetic.Includes.embed⟩

instance (priority := low) (inputs : InputsTyped env ctx p) [inputs.DirectLocals] : inputs.CastLocals casts :=
  ⟨inputs.directLocals.withCasts casts⟩

theorem InputsTyped.castLocals (inputs : InputsTyped env ctx p) [h : inputs.CastLocals casts] :
    CastTyping env 0 casts ctx inputs.ls.val wordsType := h.typed

def InputsTyped.args (inputs : InputsTyped env ctx p) : List VExpr :=
  [inputs.i.val,inputs.x.val,inputs.y.val,inputs.s.val,inputs.ls.val]

theorem InputsTyped.arguments (inputs : InputsTyped env ctx p) :
    List.Forall₂ Represents p.args inputs.args :=
  .cons inputs.i.property (.cons inputs.x.property (.cons inputs.y.property
    (.cons inputs.s.property (.cons inputs.ls.property .nil))))

theorem locals_lift (locals : List Lean.Expr) :
    (locals.map (LeanBindings.rename Nat.succ)).foldr consWord nilWords =
      LeanBindings.rename Nat.succ (locals.foldr consWord nilWords) := by
  induction locals with
  | nil => rfl
  | cons value rest ih =>
    simp only [List.map_cons,List.foldr_cons,ih,consWord,Lean.mkApp3,
      Lean.mkApp2,Lean.mkAppB,LeanBindings.rename]
    rfl

def InputsTyped.lift (inputs : InputsTyped env ctx p)
    (closed : ClosedConstantTypes env) (binder : VExpr) :
    InputsTyped env (binder::ctx) p.lift where
  i := ⟨inputs.i.val.lift,inputs.i.property.lift⟩
  x := ⟨inputs.x.val.lift,inputs.x.property.lift⟩
  y := ⟨inputs.y.val.lift,inputs.y.property.lift⟩
  s := ⟨inputs.s.val.lift,inputs.s.property.lift⟩
  ls := ⟨inputs.ls.val.lift,by
    change Represents ((p.locals.map (LeanBindings.rename Nat.succ)).foldr consWord nilWords) _
    rw [locals_lift]
    exact inputs.ls.property.lift⟩
  hi := inputs.hi.lift closed binder
  hx := inputs.hx.lift closed binder
  hy := inputs.hy.lift closed binder
  hs := inputs.hs.lift closed binder
  hl := inputs.hl.lift closed Arithmetic.casts_closed binder

/-- Updating the current State in a continuation reuses the same scope
invariant. This is a binder operation, not a physical copy or new memory. -/
def InputsTyped.nextState (inputs : InputsTyped env ctx p)
    (closed : ClosedConstantTypes env) :
    InputsTyped env (stateType::ctx) {p.lift with s := .bvar 0} where
  i := (inputs.lift closed stateType).i
  x := (inputs.lift closed stateType).x
  y := (inputs.lift closed stateType).y
  s := ⟨.bvar 0,.bvar⟩
  ls := (inputs.lift closed stateType).ls
  hi := (inputs.lift closed stateType).hi
  hx := (inputs.lift closed stateType).hx
  hy := (inputs.lift closed stateType).hy
  hs := .bvar .zero
  hl := (inputs.lift closed stateType).hl

def nilSignature : VConstant := ⟨1,.forallE (.sort (.succ (.param 0)))
  (.app (.const ``List [.param 0]) (.bvar 0))⟩

def consSignature : VConstant := ⟨1,.forallE (.sort (.succ (.param 0)))
  (.forallE (.bvar 0) (.forallE (.app (.const ``List [.param 0]) (.bvar 1))
    (.app (.const ``List [.param 0]) (.bvar 2))))⟩

/-- Retain an ordinary scalar whose inferred type may be an abbreviation of
Word. The list constructor checks the value at Word, just as Lean does. -/
def InputsTyped.withLocal (inputs : InputsTyped env ctx p)
    (represented : Represents value core)
    (typed : CheckedTyping env 0 Arithmetic.Casts ctx core wordType)
    (wordDeclared : env.constants ``HybridWord.Word = some ⟨0,.sort (.succ .zero)⟩)
    (consDeclared : env.constants ``List.cons = some consSignature) :
    InputsTyped env ctx {p with locals := value :: p.locals} where
  i := inputs.i
  x := inputs.x
  y := inputs.y
  s := inputs.s
  ls := ⟨applications (.const ``List.cons [.zero]) [wordType,core,inputs.ls.val],
    .app (.app (.app (.constant rfl) (.constant rfl)) represented) inputs.ls.property⟩
  hi := inputs.hi
  hx := inputs.hx
  hy := inputs.hy
  hs := inputs.hs
  hl := by
    have wt : CastTyping env 0 Arithmetic.Casts ctx wordType (.sort (.succ .zero)) :=
      .constant wordDeclared (by simp) rfl
    have ct : CastTyping env 0 Arithmetic.Casts ctx (.const ``List.cons [.zero])
        (.forallE (.sort (.succ .zero)) (.forallE (.bvar 0)
          (.forallE (.app (.const ``List [.zero]) (.bvar 1))
            (.app (.const ``List [.zero]) (.bvar 2))))) :=
      .constant consDeclared (by simp [VLevel.WF]) rfl
    have first := CastTyping.application ct wt
    simp only [VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,wordType,VExpr.lift,VExpr.liftN] at first
    have second := first.checkedApplication typed
    simp only [VExpr.inst,wordType,VExpr.lift,VExpr.liftN] at second
    exact .application second inputs.hl

/-- Introducing a scalar preserves the existing values and extends the
locals list. The argument is uniform in the number of earlier bindings. -/
def InputsTyped.nextWord (inputs : InputsTyped env ctx p)
    (closed : ClosedConstantTypes env)
    (wordDeclared : env.constants ``HybridWord.Word = some ⟨0,.sort (.succ .zero)⟩)
    (consDeclared : env.constants ``List.cons = some consSignature) :
    InputsTyped env (wordType::ctx) {p.lift with locals := .bvar 0 :: p.lift.locals} :=
  (inputs.lift closed wordType).withLocal .bvar (.exact (.bvar .zero)) wordDeclared consDeclared

/-- The top-level scope invariant follows from the fixed declarations. HLS
users do not supply a separate typing proof for its administrative parameters. -/
def initialInputs (wordDeclared : env.constants ``HybridWord.Word = some ⟨0,.sort (.succ .zero)⟩)
    (nilDeclared : env.constants ``List.nil = some nilSignature) :
    InputsTyped env context parameters where
  i := ⟨.bvar 3,.bvar⟩
  x := ⟨.bvar 2,.bvar⟩
  y := ⟨.bvar 1,.bvar⟩
  s := ⟨.bvar 0,.bvar⟩
  ls := ⟨.app (.const ``List.nil [.zero]) wordType,.app (.constant rfl) (.constant rfl)⟩
  hi := .bvar (.succ (.succ (.succ .zero)))
  hx := .bvar (.succ (.succ .zero))
  hy := .bvar (.succ .zero)
  hs := .bvar .zero
  hl := by
    have wordTyped : DirectTyping env 0 context wordType (.sort (.succ .zero)) :=
      .constant wordDeclared (by simp) rfl
    have nilTyped : DirectTyping env 0 context (.const ``List.nil [.zero])
        (.forallE (.sort (.succ .zero)) (.app (.const ``List [.zero]) (.bvar 0))) :=
      .constant nilDeclared (by simp [VLevel.WF]) rfl
    exact (DirectTyping.application nilTyped wordTyped).withCasts Arithmetic.Casts

instance initialInputs_direct {env : VEnv}
    (wordDeclared : env.constants ``HybridWord.Word = some ⟨0,.sort (.succ .zero)⟩)
    (nilDeclared : env.constants ``List.nil = some nilSignature) :
    (initialInputs wordDeclared nilDeclared).DirectLocals := by
  refine ⟨?_⟩
  have wordTyped : DirectTyping env 0 context wordType (.sort (.succ .zero)) :=
    .constant wordDeclared (by simp) rfl
  have nilTyped : DirectTyping env 0 context (.const ``List.nil [.zero])
      (.forallE (.sort (.succ .zero)) (.app (.const ``List [.zero]) (.bvar 0))) :=
    .constant nilDeclared (by simp [VLevel.WF]) rfl
  exact .application nilTyped wordTyped

def inputsType (result : VExpr) : VExpr :=
  .forallE wordType (.forallE wordType (.forallE wordType
    (.forallE stateType (.forallE wordsType result))))

def InputsTyped.instantiate (inputs : InputsTyped env ctx p) (result : VExpr) : VExpr :=
  ((((result.inst inputs.i.val 4).inst inputs.x.val 3).inst inputs.y.val 2).inst
    inputs.s.val 1).inst inputs.ls.val

/-- Apply the five shared arguments once, for every frontend fact. -/
theorem InputsTyped.apply (inputs : InputsTyped env ctx p) [inputs.DirectLocals]
    (typed : DirectTyping env 0 ctx function (inputsType result)) :
    DirectTyping env 0 ctx (applications function inputs.args) (inputs.instantiate result) := by
  unfold inputsType at typed
  have a1 := DirectTyping.application typed inputs.hi
  simp only [wordType,stateType,wordsType,VExpr.inst] at a1
  have a2 := DirectTyping.application a1 inputs.hx
  simp only [VExpr.inst] at a2
  have a3 := DirectTyping.application a2 inputs.hy
  simp only [VExpr.inst] at a3
  have a4 := DirectTyping.application a3 inputs.hs
  simp only [VExpr.inst] at a4
  exact DirectTyping.application a4 inputs.directLocals

theorem InputsTyped.apply_casts (inputs : InputsTyped env ctx p) [inputs.CastLocals casts]
    (typed : CastTyping env 0 casts ctx function (inputsType result)) :
    CastTyping env 0 casts ctx (applications function inputs.args) (inputs.instantiate result) := by
  unfold inputsType at typed
  have a1 := CastTyping.application typed (inputs.hi.withCasts casts)
  simp only [wordType,stateType,wordsType,VExpr.inst] at a1
  have a2 := CastTyping.application a1 (inputs.hx.withCasts casts)
  simp only [VExpr.inst] at a2
  have a3 := CastTyping.application a2 (inputs.hy.withCasts casts)
  simp only [VExpr.inst] at a3
  have a4 := CastTyping.application a3 (inputs.hs.withCasts casts)
  simp only [VExpr.inst] at a4
  exact .application a4 inputs.castLocals

def indexResult : VExpr :=
  equalValues (optionType wordType)
    (scalarValue (.bvar 4) (.bvar 3) (.bvar 2) (.bvar 1) (.bvar 0)
      (.const ``HybridWord.Expr.index [])) (someValue wordType (.bvar 4))
def indexSignature : VExpr := inputsType indexResult

theorem index_cast_typed (inputs : InputsTyped env ctx p) [inputs.CastLocals casts]
    (registered : env.constants ``WordFrontendFacts.index = some ⟨0,indexSignature⟩) :
    CastTyping env 0 casts ctx
      (applications (.const ``WordFrontendFacts.index []) inputs.args)
      (equalValues (optionType wordType)
        (scalarValue inputs.i.val inputs.x.val inputs.y.val inputs.s.val inputs.ls.val
          (.const ``HybridWord.Expr.index []))
        (someValue wordType inputs.i.val)) := by
  have h : CastTyping env 0 casts ctx (.const ``WordFrontendFacts.index []) indexSignature :=
    .constant registered (by simp) rfl
  simpa only [InputsTyped.instantiate,indexResult,applications,wordType,optionType,
    equalValues,scalarValue,someValue,Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst_lift,
    VExpr.inst,VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] using inputs.apply_casts h

theorem index_typed (inputs : InputsTyped env ctx p) [inputs.DirectLocals]
    (registered : env.constants ``WordFrontendFacts.index = some ⟨0,indexSignature⟩) :
    DirectTyping env 0 ctx
      (applications (.const ``WordFrontendFacts.index []) inputs.args)
      (equalValues (optionType wordType)
        (scalarValue inputs.i.val inputs.x.val inputs.y.val inputs.s.val inputs.ls.val
          (.const ``HybridWord.Expr.index []))
        (someValue wordType inputs.i.val))  := by
  exact (index_cast_typed (casts := fun _ _ _ => False) inputs registered).withoutCasts

theorem scalarExpected_represents (inputs : InputsTyped env ctx p)
    (codeRep : Represents code codeCore) (valueRep : Represents value valueCore) :
    Represents (scalarExpected p code value)
      (equalValues (optionType wordType)
        (scalarValue inputs.i.val inputs.x.val inputs.y.val inputs.s.val inputs.ls.val codeCore)
        (someValue wordType valueCore)) := by
  refine .app (.app (.app (.constant rfl) (.app (.constant rfl) (.constant rfl))) ?_)
    (.app (.app (.constant rfl) (.constant rfl)) valueRep)
  exact app_represents (.constant rfl) (.cons inputs.i.property (.cons inputs.x.property
    (.cons inputs.y.property (.cons inputs.s.property (.cons inputs.ls.property (.cons codeRep .nil))))))

/-- The index leaf constructs a formally checked source equality at every
well-typed scope, without a successful checker as a premise. -/
theorem index_finish (inputs : InputsTyped env ctx p) [inputs.DirectLocals]
    (registered : env.constants ``WordFrontendFacts.index = some ⟨0,indexSignature⟩)
    (conv : Conversion env) (exposure : Exposure env) :
    ∃ result, finish env conv exposure ctx
      (scalarExpected p (.const ``HybridWord.Expr.index []) p.i)
      (.const ``HybridWord.Expr.index []) (app ``WordFrontendFacts.index p.args) = some result := by
  exact finish_complete (scalarExpected_represents inputs (.constant rfl) inputs.i.property)
    (app_represents (.constant rfl) inputs.arguments) (index_typed inputs registered) conv exposure _

def bodyValue (i x y code s ls : VExpr) : VExpr :=
  applications (.const ``HybridWord.Cmd.eval []) [i,x,y,code,s,ls]

def cmdType : VExpr := .const ``HybridWord.Cmd []
def evalSignature : VExpr := .forallE wordType (.forallE wordType (.forallE wordType
  (.forallE cmdType (.forallE stateType (.forallE wordsType (optionType stateType))))))
def optionSignature : VConstant := ⟨1,.forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩
def eqSignature : VConstant := ⟨1,.forallE (.sort (.param 0))
  (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)))⟩

theorem eval_cast_typed (inputs : InputsTyped env ctx p) [inputs.CastLocals casts]
    (registered : env.constants ``HybridWord.Cmd.eval = some ⟨0,evalSignature⟩)
    (codeTyped : CastTyping env 0 casts ctx code cmdType) :
    CastTyping env 0 casts ctx
      (bodyValue inputs.i.val inputs.x.val inputs.y.val code inputs.s.val inputs.ls.val)
      (optionType stateType) := by
  have h : CastTyping env 0 casts ctx (.const ``HybridWord.Cmd.eval []) evalSignature :=
    .constant registered (by simp) rfl
  have a1 := CastTyping.application h (inputs.hi.withCasts casts)
  simp only [evalSignature,wordType,cmdType,stateType,wordsType,optionType,VExpr.inst] at a1
  have a2 := CastTyping.application a1 (inputs.hx.withCasts casts)
  simp only [VExpr.inst] at a2
  have a3 := CastTyping.application a2 (inputs.hy.withCasts casts)
  simp only [VExpr.inst] at a3
  have a4 := CastTyping.application a3 codeTyped
  simp only [VExpr.inst] at a4
  have a5 := CastTyping.application a4 (inputs.hs.withCasts casts)
  simp only [VExpr.inst] at a5
  exact .application a5 inputs.castLocals

theorem eval_typed (inputs : InputsTyped env ctx p) [inputs.DirectLocals]
    (registered : env.constants ``HybridWord.Cmd.eval = some ⟨0,evalSignature⟩)
    (codeTyped : DirectTyping env 0 ctx code cmdType) :
    DirectTyping env 0 ctx
      (bodyValue inputs.i.val inputs.x.val inputs.y.val code inputs.s.val inputs.ls.val)
      (optionType stateType) := by
  have h : DirectTyping env 0 ctx (.const ``HybridWord.Cmd.eval []) evalSignature :=
    .constant registered (by simp) rfl
  have a1 := DirectTyping.application h inputs.hi
  simp only [evalSignature,wordType,cmdType,stateType,wordsType,optionType,VExpr.inst] at a1
  have a2 := DirectTyping.application a1 inputs.hx
  simp only [VExpr.inst] at a2
  have a3 := DirectTyping.application a2 inputs.hy
  simp only [VExpr.inst] at a3
  have a4 := DirectTyping.application a3 codeTyped
  simp only [VExpr.inst] at a4
  have a5 := DirectTyping.application a4 inputs.hs
  simp only [VExpr.inst] at a5
  exact .application a5 inputs.directLocals

/-- The final target-evaluation check follows from target typing. It is not
an additional whole-program validation premise. -/
theorem target_check_cast_complete
    (wordDeclared : env.constants ``HybridWord.Word = some ⟨0,.sort (.succ .zero)⟩)
    (nilDeclared : env.constants ``List.nil = some nilSignature)
    (evalDeclared : env.constants ``HybridWord.Cmd.eval = some ⟨0,evalSignature⟩)
    (represented : {core // Represents code core})
    (typed : CastTyping env 0 casts context represented.val cmdType)
    (coverage : Conversion.Covers conv 0 casts) (exposure : Exposure env) :
    ∃ result, checkWith env conv 0 context (targetEvaluation code represented).val
      optionState exposure = some result :=
  (eval_cast_typed (initialInputs wordDeclared nilDeclared) evalDeclared typed).check_complete
    (known := noKnownTypes env 0) (by intro _ _ _ h; cases h) coverage exposure
theorem equality_head_typed
    (stateDeclared : env.constants ``HybridWord.State = some ⟨0,.sort (.succ .zero)⟩)
    (optionDeclared : env.constants ``Option = some optionSignature)
    (eqDeclared : env.constants ``Eq = some eqSignature) :
    DirectTyping env 0 ctx eqHead (.forallE optionState (.forallE optionState (.sort .zero))) := by
  have st : DirectTyping env 0 ctx stateType (.sort (.succ .zero)) :=
    .constant stateDeclared (by simp) rfl
  have op : DirectTyping env 0 ctx (.const ``Option [.zero])
      (.forallE (.sort (.succ .zero)) (.sort (.succ .zero))) :=
    .constant optionDeclared (by simp [VLevel.WF]) rfl
  have eqt : DirectTyping env 0 ctx (.const ``Eq [.succ .zero])
      (.forallE (.sort (.succ .zero)) (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)))) :=
    .constant eqDeclared (by simp [VLevel.WF]) rfl
  exact .application eqt (.application op st)

theorem equality_head_check_complete
    (stateDeclared : env.constants ``HybridWord.State = some ⟨0,.sort (.succ .zero)⟩)
    (optionDeclared : env.constants ``Option = some optionSignature)
    (eqDeclared : env.constants ``Eq = some eqSignature) :
    ∃ result, check env 0 ctx eqHead
      (.forallE optionState (.forallE optionState (.sort .zero))) = some result :=
  (equality_head_typed stateDeclared optionDeclared eqDeclared).check_complete
    (noConversion env) (noExposure env)

def skipResult : VExpr :=
  equalValues (optionType stateType)
    (bodyValue (.bvar 4) (.bvar 3) (.bvar 2) (.const ``HybridWord.Cmd.skip []) (.bvar 1) (.bvar 0))
    (someValue stateType (.bvar 1))
def skipSignature : VExpr := inputsType skipResult

theorem skip_cast_typed (inputs : InputsTyped env ctx p) [inputs.CastLocals casts]
    (registered : env.constants ``WordFrontendFacts.skip = some ⟨0,skipSignature⟩) :
    CastTyping env 0 casts ctx (applications (.const ``WordFrontendFacts.skip []) inputs.args)
      (equalValues (optionType stateType)
        (bodyValue inputs.i.val inputs.x.val inputs.y.val (.const ``HybridWord.Cmd.skip [])
          inputs.s.val inputs.ls.val) (someValue stateType inputs.s.val)) := by
  have h : CastTyping env 0 casts ctx (.const ``WordFrontendFacts.skip []) skipSignature :=
    .constant registered (by simp) rfl
  simpa only [InputsTyped.instantiate,skipResult,applications,stateType,optionType,
    equalValues,bodyValue,someValue,Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst_lift,
    VExpr.inst,VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] using inputs.apply_casts h

theorem skip_typed (inputs : InputsTyped env ctx p) [inputs.DirectLocals]
    (registered : env.constants ``WordFrontendFacts.skip = some ⟨0,skipSignature⟩) :
    DirectTyping env 0 ctx (applications (.const ``WordFrontendFacts.skip []) inputs.args)
      (equalValues (optionType stateType)
        (bodyValue inputs.i.val inputs.x.val inputs.y.val (.const ``HybridWord.Cmd.skip [])
          inputs.s.val inputs.ls.val) (someValue stateType inputs.s.val))  := by
  exact (skip_cast_typed (casts := fun _ _ _ => False) inputs registered).withoutCasts

theorem evalCmd_represents (inputs : InputsTyped env ctx p) (codeRep : Represents code codeCore) :
    Represents (evalCmd p code)
      (bodyValue inputs.i.val inputs.x.val inputs.y.val codeCore inputs.s.val inputs.ls.val) :=
  app_represents (.constant rfl) (.cons inputs.i.property (.cons inputs.x.property
    (.cons inputs.y.property (.cons codeRep (.cons inputs.s.property (.cons inputs.ls.property .nil))))))

theorem bodyExpected_represents (inputs : InputsTyped env ctx p)
    (codeRep : Represents code codeCore) (valueRep : Represents value valueCore) :
    Represents (bodyExpected p code value)
      (equalValues (optionType stateType)
        (bodyValue inputs.i.val inputs.x.val inputs.y.val codeCore inputs.s.val inputs.ls.val) valueCore) := by
  refine .app (.app (.app (.constant rfl) (.app (.constant rfl) (.constant rfl))) ?_) valueRep
  exact evalCmd_represents inputs codeRep

theorem skip_finish (inputs : InputsTyped env ctx p) [inputs.DirectLocals]
    (registered : env.constants ``WordFrontendFacts.skip = some ⟨0,skipSignature⟩)
    (conv : Conversion env) (exposure : Exposure env) :
    ∃ result, finish env conv exposure ctx
      (bodyExpected p (.const ``HybridWord.Cmd.skip []) (someExpr state p.s))
      (.const ``HybridWord.Cmd.skip []) (app ``WordFrontendFacts.skip p.args) = some result := by
  exact finish_complete (bodyExpected_represents inputs (.constant rfl)
      (.app (.app (.constant rfl) (.constant rfl)) inputs.s.property))
    (app_represents (.constant rfl) inputs.arguments) (skip_typed inputs registered) conv exposure _

structure NatArgument (env : VEnv) (ctx : List VExpr) (value : Lean.Expr) where
  represented : {core // Represents value core}
  typed : DirectTyping env 0 ctx represented.val (.const ``Nat [])
  closed : isClosed value = true

def NatArgument.literal (signatures : NatSignatures env) (n : Nat) :
    NatArgument env ctx (.lit (.natVal n)) :=
  ⟨⟨numeral n,.natural⟩,signatures.numeral_typed n,rfl⟩

def copyResult : VExpr :=
  equalValues (optionType stateType)
    (bodyValue (.bvar 4) (.bvar 3) (.bvar 2)
      (applications (.const ``HybridWord.Cmd.copy []) [.bvar 7,.bvar 6,.bvar 5]) (.bvar 1) (.bvar 0))
    (applications (.const ``HybridWord.State.copy []) [.bvar 1,.bvar 7,.bvar 6,.bvar 5])
def copySignature : VExpr := .forallE (.const ``Nat []) (.forallE (.const ``Nat [])
  (.forallE (.const ``Nat []) (inputsType copyResult)))

theorem copy_cast_typed (inputs : InputsTyped env ctx p) [inputs.CastLocals casts]
    (destination : NatArgument env ctx d) (origin : NatArgument env ctx s) (count : NatArgument env ctx n)
    (registered : env.constants ``WordFrontendFacts.copy = some ⟨0,copySignature⟩) :
    CastTyping env 0 casts ctx
      (applications (.const ``WordFrontendFacts.copy [])
        ([destination.represented.val,origin.represented.val,count.represented.val] ++ inputs.args))
      (equalValues (optionType stateType)
        (bodyValue inputs.i.val inputs.x.val inputs.y.val
          (applications (.const ``HybridWord.Cmd.copy [])
            [destination.represented.val,origin.represented.val,count.represented.val]) inputs.s.val inputs.ls.val)
        (applications (.const ``HybridWord.State.copy [])
          [inputs.s.val,destination.represented.val,origin.represented.val,count.represented.val])) := by
  have h : CastTyping env 0 casts ctx (.const ``WordFrontendFacts.copy []) copySignature :=
    .constant registered (by simp) rfl
  unfold copySignature at h
  have a1 := CastTyping.application h (destination.typed.withCasts casts)
  simp only [inputsType,wordType,stateType,wordsType,VExpr.inst] at a1
  have a2 := CastTyping.application a1 (origin.typed.withCasts casts)
  simp only [VExpr.inst] at a2
  have a3 := CastTyping.application a2 (count.typed.withCasts casts)
  simp only [VExpr.inst] at a3
  simpa only [List.cons_append,List.nil_append,applications,InputsTyped.instantiate,copyResult,
    bodyValue,equalValues,optionType,stateType,Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst_lift,
    VExpr.inst,VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] using inputs.apply_casts a3

theorem copy_typed (inputs : InputsTyped env ctx p) [inputs.DirectLocals]
    (destination : NatArgument env ctx d) (origin : NatArgument env ctx s) (count : NatArgument env ctx n)
    (registered : env.constants ``WordFrontendFacts.copy = some ⟨0,copySignature⟩) :
    DirectTyping env 0 ctx
      (applications (.const ``WordFrontendFacts.copy [])
        ([destination.represented.val,origin.represented.val,count.represented.val] ++ inputs.args))
      (equalValues (optionType stateType)
        (bodyValue inputs.i.val inputs.x.val inputs.y.val
          (applications (.const ``HybridWord.Cmd.copy [])
            [destination.represented.val,origin.represented.val,count.represented.val]) inputs.s.val inputs.ls.val)
        (applications (.const ``HybridWord.State.copy [])
          [inputs.s.val,destination.represented.val,origin.represented.val,count.represented.val]))  := by
  exact (copy_cast_typed (casts := fun _ _ _ => False) inputs destination origin count registered).withoutCasts

theorem copy_finish (inputs : InputsTyped env ctx p) [inputs.CastLocals casts]
    (destination : NatArgument env ctx d) (origin : NatArgument env ctx s) (count : NatArgument env ctx n)
    (registered : env.constants ``WordFrontendFacts.copy = some ⟨0,copySignature⟩)
    (conv : Conversion env) (exposure : Exposure env) (coverage : conv.Covers 0 casts) :
    ∃ result, finish env conv exposure ctx
      (bodyExpected p (app ``HybridWord.Cmd.copy [d,s,n]) (app ``HybridWord.State.copy [p.s,d,s,n]))
      (app ``HybridWord.Cmd.copy [d,s,n]) (app ``WordFrontendFacts.copy ([d,s,n] ++ p.args)) = some result ∧
      CastTyping env 0 casts ctx result.proofCore.val result.core.val ∧
      result.code = app ``HybridWord.Cmd.copy [d,s,n] ∧
      result.proof = app ``WordFrontendFacts.copy ([d,s,n] ++ p.args) := by
  have args := List.Forall₂.cons destination.represented.property
    (.cons origin.represented.property (.cons count.represented.property .nil))
  exact finish_cast_complete (bodyExpected_represents inputs
      (app_represents (.constant rfl) args)
      (app_represents (.constant rfl) (.cons inputs.s.property args)))
    (app_represents (.constant rfl) (.cons destination.represented.property
      (.cons origin.represented.property (.cons count.represented.property inputs.arguments))))
    (copy_cast_typed inputs destination origin count registered)
    (known := noKnownTypes env 0) (by intro _ _ _ h; cases h) coverage exposure _

theorem body_copy_complete (inputs : InputsTyped env ctx p) [inputs.CastLocals casts]
    (destination : NatArgument env ctx d) (origin : NatArgument env ctx s) (count : NatArgument env ctx n)
    (registered : env.constants ``WordFrontendFacts.copy = some ⟨0,copySignature⟩)
    (conv : Conversion env) (exposure : Exposure env) (coverage : conv.Covers 0 casts) :
    ∃ result, bodyStep env conv exposure (fun _ _ _ => none) (fun _ _ _ => none)
        (fun _ _ => none) (fun _ _ _ => none) ctx p (app ``HybridWord.State.copy [p.s,d,s,n]) = some result ∧
      CastTyping env 0 casts ctx result.checked.proofCore.val result.checked.core.val ∧
      result.code = app ``HybridWord.Cmd.copy [d,s,n] := by
  obtain ⟨proof,checked,proofTyped,_,_⟩ := copy_finish inputs destination origin count registered conv exposure coverage
  obtain ⟨dc,hd,_⟩ := destination.represented.property.translate_complete
  obtain ⟨sc,hs,_⟩ := origin.represented.property.translate_complete
  obtain ⟨nc,hn,_⟩ := count.represented.property.translate_complete
  have same := sameTerm_complete inputs.s.property inputs.s.property
  have reduced : leadingLet (app ``HybridWord.State.copy [p.s,d,s,n]) = none := rfl
  have head : (app ``HybridWord.State.copy [p.s,d,s,n]).getAppFn.constName? = some ``HybridWord.State.copy := rfl
  have args : (app ``HybridWord.State.copy [p.s,d,s,n]).getAppArgs.toList = [p.s,d,s,n] := rfl
  simp only [bodyStep,reduced,head,args,same]
  dsimp only [app,List.foldl_cons,List.foldl_nil]
  simp only [app,List.foldl_append,List.foldl_cons,List.foldl_nil] at checked
  simp [closedTerm,destination.closed,origin.closed,count.closed,hd,hs,hn,ClosedTerm.app,
    app,checked,proofTyped]

def exprType : VExpr := .const ``HybridWord.Expr []

/-- Inductive invariant of scalar parsing. Neither field asserts that a
checker succeeds; both are typing judgments about the produced terms. -/
structure ScalarTyped (inputs : InputsTyped env ctx p)
    (piece : Piece env ctx p source scalarExpected) where
  sourceCore : {core // Represents source core}
  value : DirectTyping env 0 ctx sourceCore.val wordType
  target : DirectTyping env 0 ctx piece.represented.val exprType
  proof : DirectTyping env 0 ctx piece.checked.proofCore.val piece.checked.core.val

theorem ScalarTyped.equality {inputs : InputsTyped env ctx p}
    {piece : Piece env ctx p source scalarExpected} (typed : ScalarTyped inputs piece) :
    DirectTyping env 0 ctx piece.checked.proofCore.val
      (equalValues (optionType wordType)
        (scalarValue inputs.i.val inputs.x.val inputs.y.val inputs.s.val inputs.ls.val
          piece.represented.val) (someValue wordType typed.sourceCore.val)) := by
  have same := piece.checked.core.property.unique
    (scalarExpected_represents inputs piece.represented.property typed.sourceCore.property)
  exact same ▸ typed.proof

theorem known_casts (artifact : Artifact env ctx expected)
    (typed : CastTyping env 0 casts ctx artifact.proofCore.val artifact.core.val) :
    KnownTypes.Casts artifact.known casts := by
  intro scope term result hit
  unfold Artifact.known at hit
  split at hit
  · rename_i sameContext
    subst scope
    split at hit
    · rename_i sameTerm
      subst term
      cases hit
      exact typed
    · contradiction
  · contradiction

/-- A parser induction invariant allowing the casts in ordinary Lean notation.
It describes the terms and types; it does not assume checker success. -/
structure ScalarCasts (inputs : InputsTyped env ctx p)
    (piece : Piece env ctx p source scalarExpected) (casts : TypeCasts)
    (proofCasts : TypeCasts := casts) where
  sourceCore : {core // Represents source core}
  value : CheckedTyping env 0 casts ctx sourceCore.val wordType
  target : CastTyping env 0 casts ctx piece.represented.val exprType
  proof : CastTyping env 0 proofCasts ctx piece.checked.proofCore.val piece.checked.core.val

/-- Certificate transports may need more conversions than source value
computation; keeping the two separate avoids assuming arbitrary normalization
for a scalar's ordinary arithmetic type. -/
def ScalarCasts.inProofCasts {inputs : InputsTyped env ctx p}
    {piece : Piece env ctx p source scalarExpected} (typed : ScalarCasts inputs piece casts proofCasts)
    (embeds : ∀ scope a b, casts scope a b → proofCasts scope a b) :
    ScalarCasts inputs piece proofCasts :=
  ⟨typed.sourceCore,typed.value.mono embeds,typed.target.mono embeds,typed.proof⟩

def ScalarCasts.mapProofs {inputs : InputsTyped env ctx p}
    {piece : Piece env ctx p source scalarExpected} (typed : ScalarCasts inputs piece casts proofCasts)
    (embeds : ∀ scope a b, proofCasts scope a b → nextProofCasts scope a b) :
    ScalarCasts inputs piece casts nextProofCasts :=
  ⟨typed.sourceCore,typed.value,typed.target,typed.proof.mono embeds⟩

def ScalarCasts.mapSource {inputs : InputsTyped env ctx p}
    {piece : Piece env ctx p source scalarExpected} (typed : ScalarCasts inputs piece casts proofCasts)
    (embeds : ∀ scope a b, casts scope a b → nextCasts scope a b) :
    ScalarCasts inputs piece nextCasts proofCasts :=
  ⟨typed.sourceCore,typed.value.mono embeds,typed.target.mono embeds,typed.proof⟩

def ScalarCasts.mono {inputs : InputsTyped env ctx p}
    {piece : Piece env ctx p source scalarExpected} (typed : ScalarCasts inputs piece casts)
    (embeds : ∀ scope a b, casts scope a b → nextCasts scope a b) :
    ScalarCasts inputs piece nextCasts where
  sourceCore := typed.sourceCore
  value := typed.value.mono embeds
  target := typed.target.mono embeds
  proof := typed.proof.mono embeds

def ScalarTyped.withCasts {inputs : InputsTyped env ctx p}
    {piece : Piece env ctx p source scalarExpected} (typed : ScalarTyped inputs piece)
    (casts : TypeCasts) : ScalarCasts inputs piece casts :=
  ⟨typed.sourceCore,typed.value.withCasts casts,typed.target.withCasts casts,typed.proof.withCasts casts⟩

theorem ScalarCasts.equality {inputs : InputsTyped env ctx p}
    {piece : Piece env ctx p source scalarExpected} (typed : ScalarCasts inputs piece casts) :
    CastTyping env 0 casts ctx piece.checked.proofCore.val
      (equalValues (optionType wordType)
        (scalarValue inputs.i.val inputs.x.val inputs.y.val inputs.s.val inputs.ls.val
          piece.represented.val) (someValue wordType typed.sourceCore.val)) := by
  have same := piece.checked.core.property.unique
    (scalarExpected_represents inputs piece.represented.property typed.sourceCore.property)
  exact same ▸ typed.proof

theorem forIn_constant_yield (xs : List α) (state : β) :
    forIn (m := Option) xs state (fun _ _ => some (ForInStep.yield state)) = some state := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa only [List.forIn_cons,bind,Option.bind] using ih

def registerResult : VExpr := equalValues (optionType wordType)
  (scalarValue (.bvar 4) (.bvar 3) (.bvar 2) (.bvar 1) (.bvar 0)
    (.app (.const ``HybridWord.Expr.reg []) (.bvar 5)))
  (someValue wordType (applications (.const ``HybridWord.State.regs []) [.bvar 1,.bvar 5]))
def registerSignature : VExpr := .forallE (.const ``Nat []) (inputsType registerResult)

theorem register_cast_typed (inputs : InputsTyped env ctx p) [inputs.CastLocals casts] (register : NatArgument env ctx r)
    (registered : env.constants ``WordFrontendFacts.register = some ⟨0,registerSignature⟩) :
    CastTyping env 0 casts ctx
      (applications (.const ``WordFrontendFacts.register []) (register.represented.val :: inputs.args))
      (equalValues (optionType wordType)
        (scalarValue inputs.i.val inputs.x.val inputs.y.val inputs.s.val inputs.ls.val
          (.app (.const ``HybridWord.Expr.reg []) register.represented.val))
        (someValue wordType (applications (.const ``HybridWord.State.regs [])
          [inputs.s.val,register.represented.val]))) := by
  have fact : CastTyping env 0 casts ctx (.const ``WordFrontendFacts.register []) registerSignature :=
    .constant registered (by simp) rfl
  have first := CastTyping.application fact (register.typed.withCasts casts)
  simp only [registerSignature,inputsType,wordType,stateType,wordsType,VExpr.inst] at first
  simpa only [InputsTyped.instantiate,registerResult,scalarValue,equalValues,optionType,wordType,someValue,
    applications,Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst_lift,VExpr.inst,VExpr.instVar_lower,
    VExpr.instVar_zero,VExpr.instVar_succ] using inputs.apply_casts first

theorem register_typed (inputs : InputsTyped env ctx p) [inputs.DirectLocals] (register : NatArgument env ctx r)
    (registered : env.constants ``WordFrontendFacts.register = some ⟨0,registerSignature⟩) :
    DirectTyping env 0 ctx
      (applications (.const ``WordFrontendFacts.register []) (register.represented.val :: inputs.args))
      (equalValues (optionType wordType)
        (scalarValue inputs.i.val inputs.x.val inputs.y.val inputs.s.val inputs.ls.val
          (.app (.const ``HybridWord.Expr.reg []) register.represented.val))
        (someValue wordType (applications (.const ``HybridWord.State.regs [])
          [inputs.s.val,register.represented.val])))  := by
  exact (register_cast_typed (casts := fun _ _ _ => False) inputs register registered).withoutCasts

def assignPremise : VExpr :=
  equalValues (optionType wordType)
    (scalarValue (.bvar 5) (.bvar 4) (.bvar 3) (.bvar 2) (.bvar 1) (.bvar 6))
    (someValue wordType (.bvar 0))
def assignResult : VExpr :=
  equalValues (optionType stateType)
    (bodyValue (.bvar 6) (.bvar 5) (.bvar 4)
      (applications (.const ``HybridWord.Cmd.assign []) [.bvar 8,.bvar 7]) (.bvar 3) (.bvar 2))
    (someValue stateType (applications (.const ``HybridWord.State.set []) [.bvar 3,.bvar 8,.bvar 1]))
def assignSignature : VExpr := .forallE (.const ``Nat []) (.forallE exprType
  (inputsType (.forallE wordType (.forallE assignPremise assignResult))))

/-- Assignment facts differ only in the existing `some`/`pure` return header. -/
def assignResultWith (header : VExpr) : VExpr :=
  equalValues (optionType stateType)
    (bodyValue (.bvar 6) (.bvar 5) (.bvar 4)
      (applications (.const ``HybridWord.Cmd.assign []) [.bvar 8,.bvar 7]) (.bvar 3) (.bvar 2))
    (.app header (applications (.const ``HybridWord.State.set []) [.bvar 3,.bvar 8,.bvar 1]))
def assignSignatureWith (header : VExpr) : VExpr := .forallE (.const ``Nat []) (.forallE exprType
  (inputsType (.forallE wordType (.forallE assignPremise (assignResultWith header)))))

theorem assign_fact_typed (inputs : InputsTyped env ctx p) [inputs.CastLocals casts]
    {piece : Piece env ctx p source scalarExpected}
    (register : NatArgument env ctx r) (child : ScalarCasts inputs piece casts)
    (header : VExpr) (closed : header.ClosedN 0)
    (factTyped : CastTyping env 0 casts ctx (.const fact []) (assignSignatureWith header)) :
    CastTyping env 0 casts ctx
      (applications (.const fact [])
        ([register.represented.val,piece.represented.val] ++ inputs.args ++
          [child.sourceCore.val,piece.checked.proofCore.val]))
      (equalValues (optionType stateType)
        (bodyValue inputs.i.val inputs.x.val inputs.y.val
          (applications (.const ``HybridWord.Cmd.assign []) [register.represented.val,piece.represented.val])
          inputs.s.val inputs.ls.val)
        (.app header (applications (.const ``HybridWord.State.set [])
          [inputs.s.val,register.represented.val,child.sourceCore.val]))) := by
  have headerInst (v : VExpr) (k : Nat) : header.inst v k = header := closed.instN_eq (Nat.zero_le k)
  have h := factTyped
  unfold assignSignatureWith at h
  have a1 := CastTyping.application h (register.typed.withCasts casts)
  simp only [inputsType,exprType,wordType,stateType,wordsType,VExpr.inst] at a1
  have a2 := CastTyping.application a1 child.target
  simp only [VExpr.inst] at a2
  have a3 := inputs.apply_casts a2
  simp only [InputsTyped.instantiate,assignPremise,assignResultWith,scalarValue,bodyValue,
    equalValues,optionType,wordType,stateType,someValue,applications,Nat.reduceAdd,
    ← VExpr.lift_instN_lo,VExpr.inst_lift,headerInst,VExpr.inst,VExpr.instVar_lower,
    VExpr.instVar_zero,VExpr.instVar_succ] at a3
  have a4 := CastTyping.checkedApplication a3 child.value
  simp only [Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst_lift,VExpr.inst,
    VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] at a4
  have a5 := CastTyping.application a4 child.equality
  simpa only [InputsTyped.args,List.cons_append,List.nil_append,applications,
    bodyValue,equalValues,optionType,stateType,someValue,Nat.reduceAdd,
    ← VExpr.lift_instN_lo,VExpr.inst_lift,headerInst,VExpr.inst,VExpr.instVar_lower,
    VExpr.instVar_zero,VExpr.instVar_succ] using a5

theorem assign_cast_typed (inputs : InputsTyped env ctx p) [inputs.CastLocals casts]
    {piece : Piece env ctx p source scalarExpected}
    (register : NatArgument env ctx r) (child : ScalarCasts inputs piece casts)
    (registered : env.constants ``WordFrontendFacts.assign = some ⟨0,assignSignature⟩) :
    CastTyping env 0 casts ctx
      (applications (.const ``WordFrontendFacts.assign [])
        ([register.represented.val,piece.represented.val] ++ inputs.args ++
          [child.sourceCore.val,piece.checked.proofCore.val]))
      (equalValues (optionType stateType)
        (bodyValue inputs.i.val inputs.x.val inputs.y.val
          (applications (.const ``HybridWord.Cmd.assign []) [register.represented.val,piece.represented.val])
          inputs.s.val inputs.ls.val)
        (someValue stateType (applications (.const ``HybridWord.State.set [])
          [inputs.s.val,register.represented.val,child.sourceCore.val]))) := by
  exact assign_fact_typed inputs register child (.app (.const ``Option.some [.zero]) stateType)
    (by trivial) (.constant registered (by simp) rfl)

theorem assign_cast_finish (inputs : InputsTyped env ctx p) [inputs.CastLocals casts]
    {piece : Piece env ctx p source scalarExpected}
    (register : NatArgument env ctx r) (child : ScalarCasts inputs piece casts)
    (registered : env.constants ``WordFrontendFacts.assign = some ⟨0,assignSignature⟩)
    (coverage : Conversion.Covers conv 0 casts) (exposure : Exposure env) :
    ∃ result, finish env conv exposure ctx
      (bodyExpected p (app ``HybridWord.Cmd.assign [r,piece.code])
        (someExpr state (app ``HybridWord.State.set [p.s,r,source])))
      (app ``HybridWord.Cmd.assign [r,piece.code])
      (app ``WordFrontendFacts.assign ([r,piece.code] ++ p.args ++ [source,piece.checked.proof]))
      piece.checked.known = some result := by
  have targetRep := app_represents (f := Lean.Expr.const ``HybridWord.Cmd.assign []) (.constant rfl)
    (.cons register.represented.property (.cons piece.represented.property .nil))
  have sourceRep := app_represents (f := Lean.Expr.const ``HybridWord.State.set []) (.constant rfl)
    (.cons inputs.s.property (.cons register.represented.property (.cons child.sourceCore.property .nil)))
  have proofRep := app_represents (f := Lean.Expr.const ``WordFrontendFacts.assign []) (.constant rfl)
    (.cons register.represented.property (.cons piece.represented.property
      (.cons inputs.i.property (.cons inputs.x.property (.cons inputs.y.property
        (.cons inputs.s.property (.cons inputs.ls.property
          (.cons child.sourceCore.property (.cons piece.checked.proofCore.property .nil)))))))))
  have outputRep : Represents (someExpr state (app ``HybridWord.State.set [p.s,r,source]))
      (someValue stateType (applications (.const ``HybridWord.State.set [])
        [inputs.s.val,register.represented.val,child.sourceCore.val])) :=
    .app (.app (.constant rfl) (.constant rfl)) sourceRep
  obtain ⟨result,success,_⟩ := finish_cast_complete
    (bodyExpected_represents inputs targetRep outputRep) proofRep
    (assign_cast_typed inputs register child registered) (known_casts piece.checked child.proof) coverage exposure _
  exact ⟨result,success⟩

theorem assign_typed (inputs : InputsTyped env ctx p) [inputs.DirectLocals]
    {piece : Piece env ctx p source scalarExpected}
    (register : NatArgument env ctx r) (child : ScalarTyped inputs piece)
    (registered : env.constants ``WordFrontendFacts.assign = some ⟨0,assignSignature⟩) :
    DirectTyping env 0 ctx
      (applications (.const ``WordFrontendFacts.assign [])
        ([register.represented.val,piece.represented.val] ++ inputs.args ++
          [child.sourceCore.val,piece.checked.proofCore.val]))
      (equalValues (optionType stateType)
        (bodyValue inputs.i.val inputs.x.val inputs.y.val
          (applications (.const ``HybridWord.Cmd.assign []) [register.represented.val,piece.represented.val])
          inputs.s.val inputs.ls.val)
        (someValue stateType (applications (.const ``HybridWord.State.set [])
          [inputs.s.val,register.represented.val,child.sourceCore.val]))) := by
  exact (assign_cast_typed inputs register (child.withCasts (fun _ _ _ => False)) registered).withoutCasts

theorem assign_finish (inputs : InputsTyped env ctx p) [inputs.DirectLocals]
    {piece : Piece env ctx p source scalarExpected}
    (register : NatArgument env ctx r) (child : ScalarTyped inputs piece)
    (registered : env.constants ``WordFrontendFacts.assign = some ⟨0,assignSignature⟩)
    (conv : Conversion env) (exposure : Exposure env) :
    ∃ result, finish env conv exposure ctx
      (bodyExpected p (app ``HybridWord.Cmd.assign [r,piece.code])
        (someExpr state (app ``HybridWord.State.set [p.s,r,source])))
      (app ``HybridWord.Cmd.assign [r,piece.code])
      (app ``WordFrontendFacts.assign ([r,piece.code] ++ p.args ++ [source,piece.checked.proof]))
      piece.checked.known = some result := by
  exact assign_cast_finish inputs register (child.withCasts (fun _ _ _ => False)) registered
    (fun _ _ _ impossible => False.elim impossible) exposure

end IRComparison.WordFrontend.Certificate
