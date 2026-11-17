import IRComparison.Frontend.WordArithmeticCompleteness

/-! Array-read syntax produced by ordinary Lean elaboration and successful
certificate construction in the existing Word frontend. No source AST or new
read semantics is introduced here. -/
namespace IRComparison.WordFrontend.Read
open Lean4Lean LeanTyped LeanTypeInference Certificate
variable {casts proofCasts : TypeCasts} [Arithmetic.Includes casts] [Arithmetic.Includes proofCasts]
set_option maxHeartbeats 800000

def arrayType : VExpr := .app (.const ``Array [.zero]) wordType
def nativeArray : Lean.Expr := .app (.const ``Array [.zero]) word

def validity : VExpr := .lam arrayType (.lam (.const ``Nat [])
  (applications (.const ``LT.lt [.zero]) [.const ``Nat [],.const ``instLTNat [],.bvar 0,
    applications (.const ``Array.size [.zero]) [wordType,.bvar 1]]))
def nativeValidity : Lean.Expr := .lam `xs nativeArray
  (.lam `i (.const ``Nat [])
    ([.const ``Nat [],.const ``instLTNat [],.bvar 0,
      Lean.mkApp2 (.const ``Array.size [.zero]) word (.bvar 1)].foldl Lean.Expr.app
        (.const ``LT.lt [.zero])) .default) .default

def header : VExpr := applications (.const ``GetElem?.getElem? [.zero,.zero,.zero])
  [arrayType,.const ``Nat [],wordType,validity,
    .app (.const ``Array.instGetElem?NatLtSize [.zero]) wordType]
def nativeHeader : Lean.Expr :=
  [nativeArray,.const ``Nat [],word,nativeValidity,
    .app (.const ``Array.instGetElem?NatLtSize [.zero]) word].foldl Lean.Expr.app
      (.const ``GetElem?.getElem? [.zero,.zero,.zero])

theorem header_represents : Represents nativeHeader header := by
  apply app_represents (.constant rfl)
  refine .cons (.app (.constant rfl) (.constant rfl)) (.cons (.constant rfl)
    (.cons (.constant rfl) (.cons ?_ (.cons (.app (.constant rfl) (.constant rfl)) .nil))))
  refine .lam (.app (.constant rfl) (.constant rfl)) (.lam (.constant rfl) ?_)
  exact app_represents (.constant rfl) (.cons (.constant rfl) (.cons (.constant rfl)
    (.cons .bvar (.cons (.app (.app (.constant rfl) (.constant rfl)) .bvar) .nil))))

theorem header_closed : header.ClosedN 0 := header_represents.closed 0 rfl
theorem header_inst (value : VExpr) (k : Nat) : header.inst value k = header :=
  header_closed.instN_eq (Nat.zero_le k)

def source (s a n : Lean.Expr) : Lean.Expr :=
  Lean.mkApp2 nativeHeader (app ``HybridWord.State.arrays [s,a]) n
def sourceCore (s a n : VExpr) : VExpr :=
  applications header [applications (.const ``HybridWord.State.arrays []) [s,a],n]

theorem source_represents (stateRep : Represents s sc) (arrayRep : Represents a ac)
    (indexRep : Represents n nc) : Represents (source s a n) (sourceCore sc ac nc) :=
  .app (.app header_represents (.app (.app (.constant rfl) stateRep) arrayRep)) indexRep

theorem expected_represents (inputs : InputsTyped env ctx p)
    (codeRep : Represents code codeCore) (valueRep : Represents value valueCore) :
    Represents (readExpected p code value)
      (equalValues (optionType wordType)
        (scalarValue inputs.i.val inputs.x.val inputs.y.val inputs.s.val inputs.ls.val codeCore) valueCore) := by
  refine .app (.app (.app (.constant rfl) (.app (.constant rfl) (.constant rfl))) ?_) valueRep
  exact app_represents (.constant rfl) (.cons inputs.i.property (.cons inputs.x.property
    (.cons inputs.y.property (.cons inputs.s.property (.cons inputs.ls.property (.cons codeRep .nil))))))

def natResult : VExpr := equalValues (optionType wordType)
  (scalarValue (.bvar 4) (.bvar 3) (.bvar 2) (.bvar 1) (.bvar 0)
    (applications (.const ``HybridWord.Expr.readNat []) [.bvar 6,.bvar 5]))
  (sourceCore (.bvar 1) (.bvar 6) (.bvar 5))
def natSignature : VExpr := .forallE (.const ``Nat []) (.forallE (.const ``Nat []) (inputsType natResult))

theorem nat_typed (inputs : InputsTyped env ctx p)
    (array : NatArgument env ctx a) (index : NatArgument env ctx n)
    (registered : env.constants ``WordFrontendFacts.readNat = some ⟨0,natSignature⟩) :
    CastTyping env 0 (Arithmetic.SourceCasts env) ctx
      (applications (.const ``WordFrontendFacts.readNat [])
        ([array.represented.val,index.represented.val] ++ inputs.args))
      (equalValues (optionType wordType)
        (scalarValue inputs.i.val inputs.x.val inputs.y.val inputs.s.val inputs.ls.val
          (applications (.const ``HybridWord.Expr.readNat []) [array.represented.val,index.represented.val]))
        (sourceCore inputs.s.val array.represented.val index.represented.val)) := by
  have fact : CastTyping env 0 (Arithmetic.SourceCasts env) ctx (.const ``WordFrontendFacts.readNat []) natSignature :=
    .constant registered (by simp) rfl
  have first := CastTyping.application fact (array.typed.withCasts _)
  simp only [natSignature,inputsType,wordType,stateType,wordsType,VExpr.inst] at first
  have second := CastTyping.application first (index.typed.withCasts _)
  simp only [VExpr.inst] at second
  simpa only [InputsTyped.instantiate,natResult,sourceCore,scalarValue,equalValues,optionType,wordType,
    applications,Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst_lift,VExpr.inst,VExpr.instVar_lower,
    VExpr.instVar_zero,VExpr.instVar_succ,header_inst,List.cons_append,List.nil_append] using inputs.apply_casts second

theorem nat_finish (inputs : InputsTyped env ctx p)
    (array : NatArgument env ctx a) (index : NatArgument env ctx n)
    (registered : env.constants ``WordFrontendFacts.readNat = some ⟨0,natSignature⟩)
    (conv : Conversion env) (exposure : Exposure env)
    (coverage : Conversion.Covers conv 0 (Arithmetic.SourceCasts env)) :
    ∃ result, finish env conv exposure ctx
      (readExpected p (app ``HybridWord.Expr.readNat [a,n]) (source p.s a n))
      (app ``HybridWord.Expr.readNat [a,n]) (app ``WordFrontendFacts.readNat ([a,n] ++ p.args)) = some result ∧
      CastTyping env 0 (Arithmetic.SourceCasts env) ctx result.proofCore.val result.core.val ∧
      result.code = app ``HybridWord.Expr.readNat [a,n] ∧
      result.proof = app ``WordFrontendFacts.readNat ([a,n] ++ p.args) := by
  exact finish_cast_complete (expected_represents inputs
    (app_represents (.constant rfl) (.cons array.represented.property (.cons index.represented.property .nil)))
    (source_represents inputs.s.property array.represented.property index.represented.property))
    (app_represents (.constant rfl) (.cons array.represented.property (.cons index.represented.property inputs.arguments)))
    (nat_typed inputs array index registered) (known := noKnownTypes env 0)
    (by intro _ _ _ h; cases h) coverage exposure _

/-- The two natural-index forms recognized by production: a raw literal or
an elaborated `OfNat` literal. The magnitude is not bounded. -/
def NaturalIndex (n : Lean.Expr) : Prop :=
  (match n with | .lit (.natVal _) => true | _ => false) = true ∨
    n.getAppFn.constName? = some ``OfNat.ofNat

theorem NaturalIndex.not_word (form : NaturalIndex n) :
    n.getAppFn.constName? ≠ some ``BitVec.toNat := by
  rcases form with lit | head
  · cases n <;> simp_all [Lean.Expr.getAppFn,Lean.Expr.constName?]
  · rw [head]; decide

theorem nat_step_complete (inputs : InputsTyped env ctx p)
    (array : NatArgument env ctx a) (index : NatArgument env ctx n) (form : NaturalIndex n)
    (registered : env.constants ``WordFrontendFacts.readNat = some ⟨0,natSignature⟩)
    (conv : Conversion env) (exposure : Exposure env)
    (coverage : Conversion.Covers conv 0 (Arithmetic.SourceCasts env))
    (scalarCall : ∀ value, Option (Piece env ctx p value scalarExpected)) :
    ∃ piece, readStep env conv exposure ctx p scalarCall (source p.s a n) = some piece ∧
      CastTyping env 0 (Arithmetic.SourceCasts env) ctx piece.checked.proofCore.val piece.checked.core.val ∧
      piece.code = app ``HybridWord.Expr.readNat [a,n] := by
  obtain ⟨artifact,checked,typed,_,_⟩ := nat_finish inputs array index registered conv exposure coverage
  obtain ⟨ac,atran,asame⟩ := array.represented.property.translate_complete
  obtain ⟨nc,ntran,nsame⟩ := index.represented.property.translate_complete
  let ca : ClosedTerm := ⟨a,array.closed,ac⟩
  let cn : ClosedTerm := ⟨n,index.closed,nc⟩
  let code := ClosedTerm.app ``HybridWord.Expr.readNat [ca,cn]
  let piece : Piece env ctx p (source p.s a n) readExpected := ⟨code.val,artifact,code.closed,code.represented⟩
  have closedA : closedTerm a = some ca := by
    simp only [closedTerm,array.closed,atran,ca,bind,Option.bind,dite_true,pure]
  have closedN : closedTerm n = some cn := by
    simp only [closedTerm,index.closed,ntran,cn,bind,Option.bind,dite_true,pure]
  have notWord := form.not_word
  have sameState := sameTerm_complete inputs.s.property inputs.s.property
  have head : (source p.s a n).getAppFn.constName? = some ``GetElem?.getElem? := rfl
  have args : (source p.s a n).getAppArgs.toList =
      [nativeArray,.const ``Nat [],word,nativeValidity,
        .app (.const ``Array.instGetElem?NatLtSize [.zero]) word,app ``HybridWord.State.arrays [p.s,a],n] := rfl
  have arrayHead : (app ``HybridWord.State.arrays [p.s,a]).getAppFn.constName? = some ``HybridWord.State.arrays := rfl
  have arrayArgs : (app ``HybridWord.State.arrays [p.s,a]).getAppArgs.toList = [p.s,a] := rfl
  simp only [app,List.foldl_cons,List.foldl_nil] at arrayHead arrayArgs
  refine ⟨piece,?_,typed,rfl⟩
  simp only [readStep,head,args]
  simp [arrayHead,arrayArgs,sameState,notWord,index.closed,closedA,closedN,ClosedTerm.app,
    ca,cn,code,piece,app] at checked ⊢
  simp only [checked,Option.bind_some]
  exact ⟨form,True.intro⟩

def wordIndex (k : Lean.Expr) : Lean.Expr := app ``BitVec.toNat [Arithmetic.nativeWidth,k]
def wordIndexCore (k : VExpr) : VExpr := applications (.const ``BitVec.toNat []) [Arithmetic.width,k]
def wordSource (s a k : Lean.Expr) := source s a (wordIndex k)
def wordSourceCore (s a k : VExpr) := sourceCore s a (wordIndexCore k)

theorem word_source_represents (stateRep : Represents s sc) (arrayRep : Represents a ac)
    (indexRep : Represents n nc) : Represents (wordSource s a n) (wordSourceCore sc ac nc) :=
  source_represents stateRep arrayRep
    (.app (.app (.constant rfl) Arithmetic.width_represents) indexRep)

def wordResult : VExpr := equalValues (optionType wordType)
  (scalarValue (.bvar 6) (.bvar 5) (.bvar 4) (.bvar 3) (.bvar 2)
    (applications (.const ``HybridWord.Expr.read []) [.bvar 8,.bvar 7]))
  (wordSourceCore (.bvar 3) (.bvar 8) (.bvar 1))
def wordSignature : VExpr := .forallE (.const ``Nat []) (.forallE exprType
  (inputsType (.forallE wordType (.forallE assignPremise wordResult))))

theorem word_typed (inputs : InputsTyped env ctx p) (array : NatArgument env ctx a)
    {piece : Piece env ctx p k scalarExpected} (index : ScalarCasts inputs piece casts)
    (registered : env.constants ``WordFrontendFacts.read = some ⟨0,wordSignature⟩) :
    CastTyping env 0 casts ctx
      (applications (.const ``WordFrontendFacts.read [])
        ([array.represented.val,piece.represented.val] ++ inputs.args ++
          [index.sourceCore.val,piece.checked.proofCore.val]))
      (equalValues (optionType wordType)
        (scalarValue inputs.i.val inputs.x.val inputs.y.val inputs.s.val inputs.ls.val
          (applications (.const ``HybridWord.Expr.read []) [array.represented.val,piece.represented.val]))
        (wordSourceCore inputs.s.val array.represented.val index.sourceCore.val)) := by
  have fact : CastTyping env 0 casts ctx (.const ``WordFrontendFacts.read []) wordSignature := by
    have h := CastTyping.constant (casts := casts) (ctx := ctx) (U := 0) (levels := [])
      registered (by simp) rfl
    simpa only [wordSignature,inputsType,assignPremise,wordResult,wordSourceCore,sourceCore,
      wordIndexCore,scalarValue,equalValues,optionType,wordType,stateType,wordsType,exprType,someValue,
      applications,VExpr.instL,List.map_cons,List.map_nil,VLevel.inst,
      header_represents.instL_empty,Arithmetic.width_represents.instL_empty] using h
  have first := CastTyping.application fact (array.typed.withCasts casts)
  simp only [wordSignature,inputsType,exprType,wordType,stateType,wordsType,VExpr.inst] at first
  have second := CastTyping.application first index.target
  simp only [VExpr.inst] at second
  have third := inputs.apply_casts second
  simp only [InputsTyped.instantiate,assignPremise,wordResult,wordSourceCore,sourceCore,wordIndexCore,
    scalarValue,equalValues,optionType,wordType,someValue,applications,Nat.reduceAdd,
    ← VExpr.lift_instN_lo,VExpr.inst_lift,VExpr.inst,VExpr.instVar_lower,VExpr.instVar_zero,
    VExpr.instVar_succ,header_inst,Arithmetic.width_closed.instN_eq (Nat.zero_le _)] at third
  have fourth := CastTyping.checkedApplication third index.value
  simp only [Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst_lift,VExpr.inst,VExpr.instVar_lower,
    VExpr.instVar_zero,VExpr.instVar_succ,header_inst,Arithmetic.width_closed.instN_eq (Nat.zero_le _)] at fourth
  simpa only [InputsTyped.args,applications,List.cons_append,List.nil_append,wordSourceCore,sourceCore,
    wordIndexCore,scalarValue,equalValues,optionType,wordType,someValue,Nat.reduceAdd,
    ← VExpr.lift_instN_lo,VExpr.inst_lift,VExpr.inst,VExpr.instVar_lower,VExpr.instVar_zero,
    VExpr.instVar_succ,header_inst,Arithmetic.width_closed.instN_eq (Nat.zero_le _)] using
    CastTyping.application fourth index.equality

theorem word_finish (inputs : InputsTyped env ctx p) (array : NatArgument env ctx a)
    {piece : Piece env ctx p k scalarExpected} (index : ScalarCasts inputs piece casts)
    (registered : env.constants ``WordFrontendFacts.read = some ⟨0,wordSignature⟩)
    (coverage : Conversion.Covers conv 0 casts) (exposure : Exposure env) :
    ∃ result, finish env conv exposure ctx
      (readExpected p (app ``HybridWord.Expr.read [a,piece.code]) (wordSource p.s a k))
      (app ``HybridWord.Expr.read [a,piece.code])
      (app ``WordFrontendFacts.read ([a,piece.code] ++ p.args ++ [k,piece.checked.proof]))
      piece.checked.known = some result ∧
      CastTyping env 0 casts ctx result.proofCore.val result.core.val ∧
      result.code = app ``HybridWord.Expr.read [a,piece.code] ∧
      result.proof = app ``WordFrontendFacts.read ([a,piece.code] ++ p.args ++ [k,piece.checked.proof]) := by
  exact finish_cast_complete (expected_represents inputs
    (app_represents (.constant rfl) (.cons array.represented.property (.cons piece.represented.property .nil)))
    (word_source_represents inputs.s.property array.represented.property index.sourceCore.property))
    (app_represents (.constant rfl) (.cons array.represented.property (.cons piece.represented.property
      (.cons inputs.i.property (.cons inputs.x.property (.cons inputs.y.property
        (.cons inputs.s.property (.cons inputs.ls.property (.cons index.sourceCore.property
          (.cons piece.checked.proofCore.property .nil))))))))))
    (word_typed inputs array index registered) (known_casts piece.checked index.proof) coverage exposure _

/-- Dynamic indices are the actual scalar expression's BV32-to-Nat conversion.
No affine-address condition, literal index, or successful final checker is assumed. -/
theorem word_step_complete (inputs : InputsTyped env ctx p) (array : NatArgument env ctx a)
    {piece : Piece env ctx p k scalarExpected} (index : ScalarCasts inputs piece casts)
    (registered : env.constants ``WordFrontendFacts.read = some ⟨0,wordSignature⟩)
    (coverage : Conversion.Covers conv 0 casts) (exposure : Exposure env)
    (scalarCall : ∀ value, Option (Piece env ctx p value scalarExpected))
    (parsed : scalarCall k = some piece) :
    ∃ result, readStep env conv exposure ctx p scalarCall (wordSource p.s a k) = some result ∧
      CastTyping env 0 casts ctx result.checked.proofCore.val result.checked.core.val ∧
      result.code = app ``HybridWord.Expr.read [a,piece.code] := by
  obtain ⟨artifact,checked,typed,_,_⟩ := word_finish inputs array index registered coverage exposure
  obtain ⟨ac,atran,asame⟩ := array.represented.property.translate_complete
  let ca : ClosedTerm := ⟨a,array.closed,ac⟩
  let code := ClosedTerm.app ``HybridWord.Expr.read [ca,piece.closedTerm]
  let result : Piece env ctx p (wordSource p.s a k) readExpected := ⟨code.val,artifact,code.closed,code.represented⟩
  have closedA : closedTerm a = some ca := by
    simp only [closedTerm,array.closed,atran,ca,bind,Option.bind,dite_true,pure]
  have sameState := sameTerm_complete inputs.s.property inputs.s.property
  have head : (wordSource p.s a k).getAppFn.constName? = some ``GetElem?.getElem? := rfl
  have args : (wordSource p.s a k).getAppArgs.toList =
      [nativeArray,.const ``Nat [],word,nativeValidity,
        .app (.const ``Array.instGetElem?NatLtSize [.zero]) word,
        app ``HybridWord.State.arrays [p.s,a],wordIndex k] := rfl
  have arrayHead : (app ``HybridWord.State.arrays [p.s,a]).getAppFn.constName? = some ``HybridWord.State.arrays := rfl
  have arrayArgs : (app ``HybridWord.State.arrays [p.s,a]).getAppArgs.toList = [p.s,a] := rfl
  have indexHead : (wordIndex k).getAppFn.constName? = some ``BitVec.toNat := rfl
  have indexArgs : (wordIndex k).getAppArgs.toList = [Arithmetic.nativeWidth,k] := rfl
  simp only [app,List.foldl_cons,List.foldl_nil] at arrayHead arrayArgs
  refine ⟨result,?_,typed,rfl⟩
  simp only [readStep,head,args]
  simp [arrayHead,arrayArgs,indexHead,indexArgs,sameState,closedA,parsed,ClosedTerm.app,Piece.closedTerm,
    ca,code,result,app] at checked ⊢
  simp only [checked,Option.bind_some]

def predicateType : VExpr := .forallE arrayType (.forallE (.const ``Nat []) (.sort .zero))
def predicateKind : VLevel := .imax (.succ .zero) (.imax (.succ .zero) (.succ .zero))
def predicateAnnotation : VLevel := .max (.succ .zero) (.succ .zero)
def arraySignature : VConstant := ⟨1,.forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩
def sizeSignature : VConstant := ⟨1,.forallE (.sort (.succ (.param 0)))
  (.forallE (.app (.const ``Array [.param 0]) (.bvar 0)) (.const ``Nat []))⟩
def lessSignature : VConstant := ⟨1,.forallE (.sort (.succ (.param 0)))
  (.forallE (.app (.const ``LT [.param 0]) (.bvar 0))
    (.forallE (.bvar 1) (.forallE (.bvar 2) (.sort .zero))))⟩
def getSignature : VConstant := ⟨3,
  .forallE (.sort (.succ (.param 0))) (.forallE (.sort (.succ (.param 1)))
    (.forallE (.app (.const ``outParam [.succ (.succ (.param 2))]) (.sort (.succ (.param 2))))
      (.forallE (.app (.const ``outParam [.max (.succ (.param 0)) (.succ (.param 1))])
        (.forallE (.bvar 2) (.forallE (.bvar 2) (.sort .zero))))
        (.forallE (applications (.const ``GetElem? [.param 0,.param 1,.param 2])
          [.bvar 3,.bvar 2,.bvar 1,.bvar 0])
          (.forallE (.bvar 4) (.forallE (.bvar 4)
            (.app (.const ``Option [.param 2]) (.bvar 4))))))))⟩
def getClassSignature : VConstant := ⟨3,
  .forallE (.sort (.succ (.param 0))) (.forallE (.sort (.succ (.param 1)))
    (.forallE (.app (.const ``outParam [.succ (.succ (.param 2))]) (.sort (.succ (.param 2))))
      (.forallE (.app (.const ``outParam [.max (.succ (.param 0)) (.succ (.param 1))])
        (.forallE (.bvar 2) (.forallE (.bvar 2) (.sort .zero))))
        (.sort (.max (.max (.succ (.param 0)) (.succ (.param 1))) (.succ (.param 2)))))))⟩
def arrayInstanceSignature : VConstant := ⟨1,.forallE (.sort (.succ (.param 0)))
  (applications (.const ``GetElem? [.param 0,.zero,.param 0])
    [.app (.const ``Array [.param 0]) (.bvar 0),.const ``Nat [],.bvar 0,
      .lam (.app (.const ``Array [.param 0]) (.bvar 0)) (.lam (.const ``Nat [])
        (applications (.const ``LT.lt [.zero]) [.const ``Nat [],.const ``instLTNat [],.bvar 0,
          applications (.const ``Array.size [.param 0]) [.bvar 2,.bvar 1]]))])⟩
def arraysSignature : VExpr := .forallE stateType (.forallE (.const ``Nat []) arrayType)
def toNatSignature : VExpr := .forallE (.const ``Nat [])
  (.forallE (.app (.const ``BitVec []) (.bvar 0)) (.const ``Nat []))

structure Signatures (env : VEnv) : Prop where
  word : env.constants ``HybridWord.Word = some ⟨0,.sort (.succ .zero)⟩
  natural : env.constants ``Nat = some ⟨0,.sort (.succ .zero)⟩
  array : env.constants ``Array = some arraySignature
  size : env.constants ``Array.size = some sizeSignature
  less : env.constants ``LT.lt = some lessSignature
  instanceLess : env.constants ``instLTNat = some ⟨0,.app (.const ``LT [.zero]) (.const ``Nat [])⟩
  getClass : env.constants ``GetElem? = some getClassSignature
  getter : env.constants ``GetElem?.getElem? = some getSignature
  instanceArray : env.constants ``Array.instGetElem?NatLtSize = some arrayInstanceSignature
  arrays : env.constants ``HybridWord.State.arrays = some ⟨0,arraysSignature⟩
  toNat : env.constants ``BitVec.toNat = some ⟨0,toNatSignature⟩

theorem Signatures.word_typed (signatures : Signatures env) :
    DirectTyping env 0 ctx wordType (.sort (.succ .zero)) :=
  .constant signatures.word (by simp) rfl

theorem Signatures.natural_typed (signatures : Signatures env) :
    DirectTyping env 0 ctx (.const ``Nat []) (.sort (.succ .zero)) :=
  .constant signatures.natural (by simp) rfl

theorem Signatures.array_typed (signatures : Signatures env) :
    DirectTyping env 0 ctx arrayType (.sort (.succ .zero)) := by
  have ar : DirectTyping env 0 ctx (.const ``Array [.zero])
      (.forallE (.sort (.succ .zero)) (.sort (.succ .zero))) :=
    .constant signatures.array (by simp [VLevel.WF]) rfl
  exact .application ar signatures.word_typed

theorem Signatures.predicate_typed (signatures : Signatures env) :
    DirectTyping env 0 ctx predicateType (.sort predicateKind) :=
  .forallType signatures.array_typed (.forallType signatures.natural_typed (.sort trivial))

theorem Signatures.validity_typed (signatures : Signatures env) :
    DirectTyping env 0 ctx validity predicateType := by
  apply DirectTyping.lambda signatures.array_typed
  apply DirectTyping.lambda signatures.natural_typed
  have sz : DirectTyping env 0 (.const ``Nat []::arrayType::ctx) (.const ``Array.size [.zero])
      (.forallE (.sort (.succ .zero)) (.forallE (.app (.const ``Array [.zero]) (.bvar 0)) (.const ``Nat []))) :=
    .constant signatures.size (by simp [VLevel.WF]) rfl
  have size1 := DirectTyping.application sz signatures.word_typed
  simp only [VExpr.inst,VExpr.instVar_zero,wordType] at size1
  have size2 := DirectTyping.application size1 (DirectTyping.bvar (Lookup.succ Lookup.zero))
  have lt : DirectTyping env 0 (.const ``Nat []::arrayType::ctx) (.const ``LT.lt [.zero])
      (lessSignature.type.instL [.zero]) := .constant signatures.less (by simp [VLevel.WF]) rfl
  have lt1 := DirectTyping.application lt signatures.natural_typed
  simp only [lessSignature,VExpr.instL,VLevel.inst,VExpr.inst,VExpr.instVar_lower,
    VExpr.instVar_zero,VExpr.instVar_succ,VExpr.lift,VExpr.liftN] at lt1
  have dictionary : DirectTyping env 0 (.const ``Nat []::arrayType::ctx) (.const ``instLTNat [])
      (.app (.const ``LT [.zero]) (.const ``Nat [])) := .constant signatures.instanceLess (by simp) rfl
  have lt2 := DirectTyping.application lt1 dictionary
  simp only [VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ] at lt2
  have lt3 := DirectTyping.application lt2 (DirectTyping.bvar Lookup.zero)
  simp only [VExpr.inst] at lt3
  exact .application lt3 size2

theorem Signatures.header_typed (signatures : Signatures env) :
    CastTyping env 0 (Arithmetic.SourceCasts env) ctx header
      (.forallE arrayType (.forallE (.const ``Nat []) (optionType wordType))) := by
  have getter : CastTyping env 0 (Arithmetic.SourceCasts env) ctx
      (.const ``GetElem?.getElem? [.zero,.zero,.zero]) (getSignature.type.instL [.zero,.zero,.zero]) :=
    .constant signatures.getter (by simp [VLevel.WF]) rfl
  have a1 := CastTyping.application getter (signatures.array_typed.withCasts _)
  simp only [getSignature,applications,VExpr.instL,VLevel.inst,VExpr.inst,VExpr.instVar_lower,
    VExpr.instVar_zero,VExpr.instVar_succ,arrayType,wordType,VExpr.lift,VExpr.liftN] at a1
  have a2 := CastTyping.application a1 (signatures.natural_typed.withCasts _)
  simp only [VExpr.inst,VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] at a2
  have a3 := CastTyping.convertedApplication a2 (signatures.word_typed.withCasts _) (.arithmetic .resultType)
  simp only [VExpr.inst,VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ,wordType,VExpr.lift,VExpr.liftN] at a3
  have predCast : Arithmetic.SourceCasts env ctx predicateType
      (.app (.const ``outParam [predicateAnnotation]) predicateType) :=
    .parameter predicateType (signatures.predicate_typed (ctx := []))
      (by trivial) (by trivial) rfl
  have a4 := CastTyping.convertedApplication a3 (signatures.validity_typed.withCasts _) predCast
  simp only [VExpr.inst,VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] at a4
  have instanceTyped : DirectTyping env 0 ctx (.const ``Array.instGetElem?NatLtSize [.zero])
      (arrayInstanceSignature.type.instL [.zero]) := .constant signatures.instanceArray (by simp [VLevel.WF]) rfl
  have dictionary := DirectTyping.application instanceTyped signatures.word_typed
  simp only [arrayInstanceSignature,applications,VExpr.instL,VLevel.inst,VExpr.inst,VExpr.instVar_lower,
    VExpr.instVar_zero,VExpr.instVar_succ,wordType,VExpr.lift,VExpr.liftN] at dictionary
  simpa only [header,applications,optionType,arrayType,validity,wordType,VExpr.inst,
    VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.lift,VExpr.liftN] using
    CastTyping.application a4 (dictionary.withCasts _)

theorem Signatures.arrays_typed (signatures : Signatures env) (inputs : InputsTyped env ctx p)
    (array : NatArgument env ctx a) :
    DirectTyping env 0 ctx (applications (.const ``HybridWord.State.arrays [])
      [inputs.s.val,array.represented.val]) arrayType := by
  have fact : DirectTyping env 0 ctx (.const ``HybridWord.State.arrays []) arraysSignature :=
    .constant signatures.arrays (by simp) rfl
  have first := DirectTyping.application fact inputs.hs
  simp only [arraysSignature,arrayType,wordType,stateType,VExpr.inst] at first
  exact .application first array.typed

theorem Signatures.source_typed (signatures : Signatures env) (inputs : InputsTyped env ctx p)
    (array : NatArgument env ctx a)
    (index : CastTyping env 0 (Arithmetic.SourceCasts env) ctx n (.const ``Nat [])) :
    CastTyping env 0 (Arithmetic.SourceCasts env) ctx (sourceCore inputs.s.val array.represented.val n)
      (optionType wordType) := by
  have first := CastTyping.application signatures.header_typed
    ((signatures.arrays_typed inputs array).withCasts _)
  simp only [arrayType,optionType,wordType,VExpr.inst] at first
  exact .application first index

theorem Signatures.word_index_typed (signatures : Signatures env) (arithmetic : Arithmetic.Signatures env)
    (index : CheckedTyping env 0 (Arithmetic.SourceCasts env) ctx k wordType) :
    CastTyping env 0 (Arithmetic.SourceCasts env) ctx (wordIndexCore k) (.const ``Nat []) := by
  have fact : CastTyping env 0 (Arithmetic.SourceCasts env) ctx (.const ``BitVec.toNat []) toNatSignature :=
    .constant signatures.toNat (by simp) rfl
  have first := CastTyping.application fact (arithmetic.width_typed.withCasts _)
  simp only [toNatSignature,VExpr.inst,VExpr.instVar_zero] at first
  cases index with
  | exact typed => exact .convertedApplication first typed .wordValue
  | converted typed cast =>
    cases cast with
    | arithmetic cast =>
      cases cast
      exact .application first typed

structure ReadCasts (inputs : InputsTyped env ctx p)
    (piece : Piece env ctx p value readExpected) (casts : TypeCasts)
    (proofCasts : TypeCasts := casts) where
  sourceCore : {core // Represents value core}
  value : CheckedTyping env 0 casts ctx sourceCore.val (optionType wordType)
  target : CastTyping env 0 casts ctx piece.represented.val exprType
  proof : CastTyping env 0 proofCasts ctx piece.checked.proofCore.val piece.checked.core.val

theorem ReadCasts.equality {value : Lean.Expr} {inputs : InputsTyped env ctx p}
    {piece : Piece env ctx p value readExpected} (typed : ReadCasts inputs piece casts proofCasts) :
    CastTyping env 0 proofCasts ctx piece.checked.proofCore.val
      (equalValues (optionType wordType)
        (scalarValue inputs.i.val inputs.x.val inputs.y.val inputs.s.val inputs.ls.val piece.represented.val)
        typed.sourceCore.val) := by
  have same := piece.checked.core.property.unique
    (expected_represents inputs piece.represented.property typed.sourceCore.property)
  exact same ▸ typed.proof

def ReadCasts.mapProofs {source : Lean.Expr} {inputs : InputsTyped env ctx p}
    {piece : Piece env ctx p source readExpected} (typed : ReadCasts inputs piece casts proofCasts)
    (embeds : ∀ scope a b, proofCasts scope a b → nextCasts scope a b) :
    ReadCasts inputs piece casts nextCasts where
  sourceCore := typed.sourceCore
  value := typed.value
  target := typed.target
  proof := typed.proof.mono embeds

def natConstructor : VExpr := .forallE (.const ``Nat []) (.forallE (.const ``Nat []) exprType)
def wordConstructor : VExpr := .forallE (.const ``Nat []) (.forallE exprType exprType)

theorem nat_step_invariant_complete_code (signatures : Signatures env) (inputs : InputsTyped env ctx p)
    (array : NatArgument env ctx a) (index : NatArgument env ctx n) (form : NaturalIndex n)
    (registered : env.constants ``WordFrontendFacts.readNat = some ⟨0,natSignature⟩)
    (constructor : env.constants ``HybridWord.Expr.readNat = some ⟨0,natConstructor⟩)
    (conv : Conversion env) (exposure : Exposure env)
    (coverage : Conversion.Covers conv 0 (Arithmetic.SourceCasts env))
    (scalarCall : ∀ value, Option (Piece env ctx p value scalarExpected)) :
    ∃ piece, readStep env conv exposure ctx p scalarCall (source p.s a n) = some piece ∧
      Nonempty (ReadCasts inputs piece (Arithmetic.SourceCasts env)) ∧
      piece.code = app ``HybridWord.Expr.readNat [a,n] := by
  obtain ⟨piece,parsed,proof,code⟩ := nat_step_complete inputs array index form registered conv exposure coverage scalarCall
  have targetRep : Represents piece.code (applications (.const ``HybridWord.Expr.readNat [])
      [array.represented.val,index.represented.val]) := by
    rw [code]
    exact app_represents (.constant rfl) (.cons array.represented.property (.cons index.represented.property .nil))
  refine ⟨piece,parsed,⟨⟨⟨_,source_represents inputs.s.property array.represented.property index.represented.property⟩,
    .exact (signatures.source_typed inputs array (index.typed.withCasts _)),?_,proof⟩⟩,code⟩
  rw [piece.represented.property.unique targetRep]
  have fact : CastTyping env 0 (Arithmetic.SourceCasts env) ctx (.const ``HybridWord.Expr.readNat []) natConstructor :=
    .constant constructor (by simp) rfl
  have first := CastTyping.application fact (array.typed.withCasts _)
  simp only [natConstructor,exprType,VExpr.inst] at first
  exact .application first (index.typed.withCasts _)

theorem nat_step_invariant_complete (signatures : Signatures env) (inputs : InputsTyped env ctx p)
    (array : NatArgument env ctx a) (index : NatArgument env ctx n) (form : NaturalIndex n)
    (registered : env.constants ``WordFrontendFacts.readNat = some ⟨0,natSignature⟩)
    (constructor : env.constants ``HybridWord.Expr.readNat = some ⟨0,natConstructor⟩)
    (conv : Conversion env) (exposure : Exposure env)
    (coverage : Conversion.Covers conv 0 (Arithmetic.SourceCasts env))
    (scalarCall : ∀ value, Option (Piece env ctx p value scalarExpected)) :
    ∃ piece, readStep env conv exposure ctx p scalarCall (source p.s a n) = some piece ∧
      Nonempty (ReadCasts inputs piece (Arithmetic.SourceCasts env)) := by
  obtain ⟨piece,success,typed,_⟩ := nat_step_invariant_complete_code signatures inputs array index form registered constructor conv exposure coverage scalarCall
  exact ⟨piece,success,typed⟩

theorem word_step_split_complete_code (signatures : Signatures env) (arithmetic : Arithmetic.Signatures env)
    (inputs : InputsTyped env ctx p) (array : NatArgument env ctx a)
    {indexPiece : Piece env ctx p k scalarExpected}
    (index : ScalarCasts inputs indexPiece (Arithmetic.SourceCasts env) proofCasts)
    (registered : env.constants ``WordFrontendFacts.read = some ⟨0,wordSignature⟩)
    (constructor : env.constants ``HybridWord.Expr.read = some ⟨0,wordConstructor⟩)
    (embeds : ∀ scope a b, Arithmetic.SourceCasts env scope a b → proofCasts scope a b)
    (coverage : Conversion.Covers conv 0 proofCasts) (exposure : Exposure env)
    (scalarCall : ∀ value, Option (Piece env ctx p value scalarExpected))
    (indexParsed : scalarCall k = some indexPiece) :
    ∃ piece, readStep env conv exposure ctx p scalarCall (wordSource p.s a k) = some piece ∧
      Nonempty (ReadCasts inputs piece (Arithmetic.SourceCasts env) proofCasts) ∧
      piece.code = app ``HybridWord.Expr.read [a,indexPiece.code] := by
  obtain ⟨piece,parsed,proof,code⟩ := word_step_complete inputs array (index.inProofCasts embeds) registered coverage exposure scalarCall indexParsed
  have targetRep : Represents piece.code (applications (.const ``HybridWord.Expr.read [])
      [array.represented.val,indexPiece.represented.val]) := by
    rw [code]
    exact app_represents (.constant rfl) (.cons array.represented.property (.cons indexPiece.represented.property .nil))
  refine ⟨piece,parsed,⟨⟨⟨_,word_source_represents inputs.s.property array.represented.property index.sourceCore.property⟩,
    .exact (signatures.source_typed inputs array (signatures.word_index_typed arithmetic index.value)),?_,proof⟩⟩,code⟩
  rw [piece.represented.property.unique targetRep]
  have fact : CastTyping env 0 (Arithmetic.SourceCasts env) ctx (.const ``HybridWord.Expr.read []) wordConstructor :=
    .constant constructor (by simp) rfl
  have first := CastTyping.application fact (array.typed.withCasts _)
  simp only [wordConstructor,exprType,VExpr.inst] at first
  exact .application first index.target

theorem word_step_split_complete (signatures : Signatures env) (arithmetic : Arithmetic.Signatures env)
    (inputs : InputsTyped env ctx p) (array : NatArgument env ctx a)
    {indexPiece : Piece env ctx p k scalarExpected}
    (index : ScalarCasts inputs indexPiece (Arithmetic.SourceCasts env) proofCasts)
    (registered : env.constants ``WordFrontendFacts.read = some ⟨0,wordSignature⟩)
    (constructor : env.constants ``HybridWord.Expr.read = some ⟨0,wordConstructor⟩)
    (embeds : ∀ scope a b, Arithmetic.SourceCasts env scope a b → proofCasts scope a b)
    (coverage : Conversion.Covers conv 0 proofCasts) (exposure : Exposure env)
    (scalarCall : ∀ value, Option (Piece env ctx p value scalarExpected))
    (indexParsed : scalarCall k = some indexPiece) :
    ∃ piece, readStep env conv exposure ctx p scalarCall (wordSource p.s a k) = some piece ∧
      Nonempty (ReadCasts inputs piece (Arithmetic.SourceCasts env) proofCasts) := by
  obtain ⟨piece,success,typed,_⟩ := word_step_split_complete_code signatures arithmetic inputs array index registered constructor embeds coverage exposure scalarCall indexParsed
  exact ⟨piece,success,typed⟩

theorem word_step_invariant_complete (signatures : Signatures env) (arithmetic : Arithmetic.Signatures env)
    (inputs : InputsTyped env ctx p) (array : NatArgument env ctx a)
    {indexPiece : Piece env ctx p k scalarExpected}
    (index : ScalarCasts inputs indexPiece (Arithmetic.SourceCasts env))
    (registered : env.constants ``WordFrontendFacts.read = some ⟨0,wordSignature⟩)
    (constructor : env.constants ``HybridWord.Expr.read = some ⟨0,wordConstructor⟩)
    (coverage : Conversion.Covers conv 0 (Arithmetic.SourceCasts env)) (exposure : Exposure env)
    (scalarCall : ∀ value, Option (Piece env ctx p value scalarExpected))
    (indexParsed : scalarCall k = some indexPiece) :
    ∃ piece, readStep env conv exposure ctx p scalarCall (wordSource p.s a k) = some piece ∧
      Nonempty (ReadCasts inputs piece (Arithmetic.SourceCasts env)) := by
  exact word_step_split_complete signatures arithmetic inputs array index registered constructor
    (fun _ _ _ h => h) coverage exposure scalarCall indexParsed

end IRComparison.WordFrontend.Read
