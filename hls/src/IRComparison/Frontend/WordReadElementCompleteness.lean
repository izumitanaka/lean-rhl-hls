import IRComparison.Frontend.WordForConversion

namespace IRComparison.WordFrontend.Read
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic
set_option maxHeartbeats 1800000

theorem bits_finish_complete (setup : AliasSetup env) (arithmetic : Arithmetic.Signatures env)
    (library : Signatures env) (scalars : ScalarConversion.Signatures env)
    (inputs : InputsTyped env ctx p) (array : NatArgument env ctx a)
    (code : ClosedTerm) (codeTyped : CastTyping env 0 (SourceCasts env) ctx code.represented.val exprType)
    (indexRep : Represents n index)
    (indexTyped : CastTyping env 0 (SourceCasts env) ctx index natType)
    (indexForm : ValueForm setup ctx index natType)
    (getterFresh : ∀ r ∈ setup.rules, ``GetElem?.getElem? ≠ r.name)
    (instanceFresh : ∀ r ∈ setup.rules, ``Array.instGetElem?NatLtSize ≠ r.name)
    (arraysFresh : ∀ r ∈ setup.rules, ``HybridWord.State.arrays ≠ r.name)
    (proofRep : Represents proof proofCore)
    (proofTyped : CastTyping env 0 (For.Casts setup) ctx proofCore
      (equalValues (optionType wordType)
        (scalarValue inputs.i.val inputs.x.val inputs.y.val inputs.s.val inputs.ls.val code.represented.val)
        (sourceCore inputs.s.val array.represented.val index)))
    (coherent : KnownTypes.Casts known (For.Casts setup))
    (coverage : Conversion.Covers setup.conversion 0 (For.Casts setup)) (exposure : Exposure env) :
    ∃ artifact, finish env setup.conversion exposure ctx (readExpected p code.val (bitsSource p.s a n))
        code.val proof known = some artifact ∧
      Nonempty (ReadCasts inputs (⟨code.val,artifact,code.closed,code.represented⟩ : Piece env ctx p _ readExpected)
        (SourceCasts env) (For.Casts setup)) := by
  have embed : ∀ scope a b, SourceCasts env scope a b → For.Casts setup scope a b :=
    fun _ _ _ cast => .base (.base (.source cast))
  have prefixTyped := ScalarConversion.prefix_typed scalars (ScalarConversion.eval_typed scalars inputs codeTyped)
  have sourceTyped := library.bits_source_typed arithmetic inputs array indexTyped
  have sourceChecked : CheckedTyping env 0 (SourceCasts env) ctx
      (bitsSourceCore (applications (.const ``HybridWord.State.arrays []) [inputs.s.val,array.represented.val]) index)
      (optionType wordType) := .converted sourceTyped (.bitvecOption scalars.option)
  have converted : For.Casts setup ctx
      (equalValues (optionType wordType)
        (scalarValue inputs.i.val inputs.x.val inputs.y.val inputs.s.val inputs.ls.val code.represented.val)
        (sourceCore inputs.s.val array.represented.val index))
      (equalValues (optionType wordType)
        (scalarValue inputs.i.val inputs.x.val inputs.y.val inputs.s.val inputs.ls.val code.represented.val)
        (bitsSourceCore (applications (.const ``HybridWord.State.arrays []) [inputs.s.val,array.represented.val]) index)) :=
    .readElementEquality library getterFresh instanceFresh prefixTyped (library.arrays_typed inputs array)
      (.constant rfl arraysFresh (by decide)) indexTyped indexForm
  obtain ⟨artifact,done,typed,_⟩ := finish_checked_complete
    (expected_represents inputs code.represented.property (bitsSource_represents inputs.s.property array.represented.property indexRep))
    proofRep (.converted proofTyped converted)
    ((CastTyping.checkedApplication prefixTyped sourceChecked).mono embed)
    coherent coverage exposure code.val
  exact ⟨artifact,done,⟨⟨⟨_,bitsSource_represents inputs.s.property array.represented.property indexRep⟩,
    sourceChecked,codeTyped,typed⟩⟩⟩

theorem bits_nat_complete_code (setup : AliasSetup env) (arithmetic : Arithmetic.Signatures env)
    (library : Signatures env) (scalars : ScalarConversion.Signatures env)
    (inputs : InputsTyped env ctx p) (array : NatArgument env ctx a) (index : NatArgument env ctx n)
    (form : NaturalIndex n) (indexForm : ValueForm setup ctx index.represented.val natType)
    (getterFresh : ∀ r ∈ setup.rules, ``GetElem?.getElem? ≠ r.name)
    (instanceFresh : ∀ r ∈ setup.rules, ``Array.instGetElem?NatLtSize ≠ r.name)
    (arraysFresh : ∀ r ∈ setup.rules, ``HybridWord.State.arrays ≠ r.name)
    (registered : env.constants ``WordFrontendFacts.readNat = some ⟨0,natSignature⟩)
    (constructor : env.constants ``HybridWord.Expr.readNat = some ⟨0,natConstructor⟩)
    (coverage : Conversion.Covers setup.conversion 0 (For.Casts setup)) (exposure : Exposure env)
    (scalarCall : ∀ value, Option (Piece env ctx p value scalarExpected)) :
    ∃ piece, readStep env setup.conversion exposure ctx p scalarCall (bitsSource p.s a n) = some piece ∧
      Nonempty (ReadCasts inputs piece (SourceCasts env) (For.Casts setup)) ∧
      piece.code = app ``HybridWord.Expr.readNat [a,n] := by
  let ca : ClosedTerm := ⟨a,array.closed,array.represented⟩
  let cn : ClosedTerm := ⟨n,index.closed,index.represented⟩
  let code := ClosedTerm.app ``HybridWord.Expr.readNat [ca,cn]
  have headTyped : CastTyping env 0 (SourceCasts env) ctx (.const ``HybridWord.Expr.readNat []) natConstructor :=
    .constant constructor (by simp) rfl
  have applied := CastTyping.application headTyped (array.typed.withCasts _)
  simp only [natConstructor,exprType,VExpr.inst] at applied
  have codeTyped := CastTyping.application applied (index.typed.withCasts (SourceCasts env))
  obtain ⟨artifact,checked,⟨typed⟩⟩ := bits_finish_complete
    (proof := app ``WordFrontendFacts.readNat ([a,n] ++ p.args)) setup arithmetic library scalars inputs array code codeTyped
    index.represented.property (index.typed.withCasts _) indexForm getterFresh instanceFresh arraysFresh
    (app_represents (.constant rfl) (.cons array.represented.property (.cons index.represented.property inputs.arguments)))
    ((nat_typed inputs array index registered).mono (fun _ _ _ cast => .base (.base (.source cast))))
    (known := noKnownTypes env 0) (by intro _ _ _ h; cases h) coverage exposure
  let piece : Piece env ctx p (bitsSource p.s a n) readExpected := ⟨code.val,artifact,code.closed,code.represented⟩
  obtain ⟨ac,atran,asame⟩ := array.represented.property.translate_complete
  obtain ⟨nc,ntran,nsame⟩ := index.represented.property.translate_complete
  have atrans : translate a = some array.represented := by
    cases ac with | mk val prop => dsimp only at asame; subst val; exact atran
  have ntrans : translate n = some index.represented := by
    cases nc with | mk val prop => dsimp only at nsame; subst val; exact ntran
  have closedA : closedTerm a = some ca := by
    simp only [closedTerm,array.closed,atrans,ca,bind,Option.bind,dite_true,pure]
  have closedN : closedTerm n = some cn := by
    simp only [closedTerm,index.closed,ntrans,cn,bind,Option.bind,dite_true,pure]
  have notWord := form.not_word
  have sameState := sameTerm_complete inputs.s.property inputs.s.property
  have head : (bitsSource p.s a n).getAppFn.constName? = some ``GetElem?.getElem? := rfl
  have args : (bitsSource p.s a n).getAppArgs.toList =
      [nativeArray,.const ``Nat [],WordBinder.Annotation.bitvec.native,nativeValidity,
        .app (.const ``Array.instGetElem?NatLtSize [.zero]) word,app ``HybridWord.State.arrays [p.s,a],n] := rfl
  have arrayHead : (app ``HybridWord.State.arrays [p.s,a]).getAppFn.constName? = some ``HybridWord.State.arrays := rfl
  have arrayArgs : (app ``HybridWord.State.arrays [p.s,a]).getAppArgs.toList = [p.s,a] := rfl
  simp only [app,List.foldl_cons,List.foldl_nil] at arrayHead arrayArgs
  refine ⟨piece,?_,⟨typed⟩,rfl⟩
  simp only [readStep,head,args]
  simp [arrayHead,arrayArgs,sameState,notWord,index.closed,closedA,closedN,ClosedTerm.app,
    ca,cn,code,piece,app] at checked ⊢
  simp only [checked,Option.bind_some]
  exact ⟨form,True.intro⟩

theorem bits_nat_complete (setup : AliasSetup env) (arithmetic : Arithmetic.Signatures env)
    (library : Signatures env) (scalars : ScalarConversion.Signatures env)
    (inputs : InputsTyped env ctx p) (array : NatArgument env ctx a) (index : NatArgument env ctx n)
    (form : NaturalIndex n) (indexForm : ValueForm setup ctx index.represented.val natType)
    (getterFresh : ∀ r ∈ setup.rules, ``GetElem?.getElem? ≠ r.name)
    (instanceFresh : ∀ r ∈ setup.rules, ``Array.instGetElem?NatLtSize ≠ r.name)
    (arraysFresh : ∀ r ∈ setup.rules, ``HybridWord.State.arrays ≠ r.name)
    (registered : env.constants ``WordFrontendFacts.readNat = some ⟨0,natSignature⟩)
    (constructor : env.constants ``HybridWord.Expr.readNat = some ⟨0,natConstructor⟩)
    (coverage : Conversion.Covers setup.conversion 0 (For.Casts setup)) (exposure : Exposure env)
    (scalarCall : ∀ value, Option (Piece env ctx p value scalarExpected)) :
    ∃ piece, readStep env setup.conversion exposure ctx p scalarCall (bitsSource p.s a n) = some piece ∧
      Nonempty (ReadCasts inputs piece (SourceCasts env) (For.Casts setup)) := by
  obtain ⟨piece,success,typed,_⟩ := bits_nat_complete_code setup arithmetic library scalars inputs array index
    form indexForm getterFresh instanceFresh arraysFresh registered constructor coverage exposure scalarCall
  exact ⟨piece,success,typed⟩

/-- The element annotation does not restrict indices to constants. The scalar
child is supplied by the same source-syntax induction as unannotated reads. -/
theorem bits_word_complete_code (setup : AliasSetup env) (arithmetic : Arithmetic.Signatures env)
    (library : Signatures env) (scalars : ScalarConversion.Signatures env)
    (inputs : InputsTyped env ctx p) (array : NatArgument env ctx a)
    {indexPiece : Piece env ctx p k scalarExpected}
    (index : ScalarCasts inputs indexPiece (SourceCasts env) (For.Casts setup))
    (getterFresh : ∀ r ∈ setup.rules, ``GetElem?.getElem? ≠ r.name)
    (instanceFresh : ∀ r ∈ setup.rules, ``Array.instGetElem?NatLtSize ≠ r.name)
    (arraysFresh : ∀ r ∈ setup.rules, ``HybridWord.State.arrays ≠ r.name)
    (indexFresh : ∀ r ∈ setup.rules, ``BitVec.toNat ≠ r.name)
    (registered : env.constants ``WordFrontendFacts.read = some ⟨0,wordSignature⟩)
    (constructor : env.constants ``HybridWord.Expr.read = some ⟨0,wordConstructor⟩)
    (coverage : Conversion.Covers setup.conversion 0 (For.Casts setup)) (exposure : Exposure env)
    (scalarCall : ∀ value, Option (Piece env ctx p value scalarExpected))
    (indexParsed : scalarCall k = some indexPiece) :
    ∃ piece, readStep env setup.conversion exposure ctx p scalarCall (bitsSource p.s a (wordIndex k)) = some piece ∧
      Nonempty (ReadCasts inputs piece (SourceCasts env) (For.Casts setup)) ∧
      piece.code = app ``HybridWord.Expr.read [a,indexPiece.code] := by
  let ca : ClosedTerm := ⟨a,array.closed,array.represented⟩
  let code := ClosedTerm.app ``HybridWord.Expr.read [ca,indexPiece.closedTerm]
  have headTyped : CastTyping env 0 (SourceCasts env) ctx (.const ``HybridWord.Expr.read []) wordConstructor :=
    .constant constructor (by simp) rfl
  have first := CastTyping.application headTyped (array.typed.withCasts _)
  simp only [wordConstructor,exprType,VExpr.inst] at first
  have codeTyped := CastTyping.application first index.target
  obtain ⟨artifact,checked,⟨typed⟩⟩ := bits_finish_complete
    (proof := app ``WordFrontendFacts.read ([a,indexPiece.code] ++ p.args ++ [k,indexPiece.checked.proof]))
    setup arithmetic library scalars inputs array code codeTyped
    (show Represents (wordIndex k) (wordIndexCore index.sourceCore.val) from
      .app (.app (.constant rfl) Arithmetic.width_represents) index.sourceCore.property) (library.word_index_typed arithmetic index.value)
    (.constant rfl indexFresh (by decide)) getterFresh instanceFresh arraysFresh
    (app_represents (.constant rfl) (.cons array.represented.property (.cons indexPiece.represented.property
      (.cons inputs.i.property (.cons inputs.x.property (.cons inputs.y.property
        (.cons inputs.s.property (.cons inputs.ls.property (.cons index.sourceCore.property
          (.cons indexPiece.checked.proofCore.property .nil))))))))))
    (word_typed inputs array (index.inProofCasts (fun _ _ _ h => .base (.base (.source h)))) registered)
    (known_casts indexPiece.checked index.proof) coverage exposure
  let piece : Piece env ctx p (bitsSource p.s a (wordIndex k)) readExpected :=
    ⟨code.val,artifact,code.closed,code.represented⟩
  obtain ⟨ac,atran,asame⟩ := array.represented.property.translate_complete
  have atrans : translate a = some array.represented := by
    cases ac with | mk val prop => dsimp only at asame; subst val; exact atran
  have closedA : closedTerm a = some ca := by
    simp only [closedTerm,array.closed,atrans,ca,bind,Option.bind,dite_true,pure]
  have sameState := sameTerm_complete inputs.s.property inputs.s.property
  have head : (bitsSource p.s a (wordIndex k)).getAppFn.constName? = some ``GetElem?.getElem? := rfl
  have args : (bitsSource p.s a (wordIndex k)).getAppArgs.toList =
      [nativeArray,.const ``Nat [],WordBinder.Annotation.bitvec.native,nativeValidity,
        .app (.const ``Array.instGetElem?NatLtSize [.zero]) word,
        app ``HybridWord.State.arrays [p.s,a],wordIndex k] := rfl
  have arrayHead : (app ``HybridWord.State.arrays [p.s,a]).getAppFn.constName? = some ``HybridWord.State.arrays := rfl
  have arrayArgs : (app ``HybridWord.State.arrays [p.s,a]).getAppArgs.toList = [p.s,a] := rfl
  have indexHead : (wordIndex k).getAppFn.constName? = some ``BitVec.toNat := rfl
  have indexArgs : (wordIndex k).getAppArgs.toList = [Arithmetic.nativeWidth,k] := rfl
  simp only [app,List.foldl_cons,List.foldl_nil] at arrayHead arrayArgs
  refine ⟨piece,?_,⟨typed⟩,rfl⟩
  simp only [readStep,head,args]
  simp [arrayHead,arrayArgs,indexHead,indexArgs,sameState,closedA,indexParsed,ClosedTerm.app,Piece.closedTerm,
    ca,code,piece,app] at checked ⊢
  simp only [checked,Option.bind_some]

theorem bits_word_complete (setup : AliasSetup env) (arithmetic : Arithmetic.Signatures env)
    (library : Signatures env) (scalars : ScalarConversion.Signatures env)
    (inputs : InputsTyped env ctx p) (array : NatArgument env ctx a)
    {indexPiece : Piece env ctx p k scalarExpected}
    (index : ScalarCasts inputs indexPiece (SourceCasts env) (For.Casts setup))
    (getterFresh : ∀ r ∈ setup.rules, ``GetElem?.getElem? ≠ r.name)
    (instanceFresh : ∀ r ∈ setup.rules, ``Array.instGetElem?NatLtSize ≠ r.name)
    (arraysFresh : ∀ r ∈ setup.rules, ``HybridWord.State.arrays ≠ r.name)
    (indexFresh : ∀ r ∈ setup.rules, ``BitVec.toNat ≠ r.name)
    (registered : env.constants ``WordFrontendFacts.read = some ⟨0,wordSignature⟩)
    (constructor : env.constants ``HybridWord.Expr.read = some ⟨0,wordConstructor⟩)
    (coverage : Conversion.Covers setup.conversion 0 (For.Casts setup)) (exposure : Exposure env)
    (scalarCall : ∀ value, Option (Piece env ctx p value scalarExpected))
    (indexParsed : scalarCall k = some indexPiece) :
    ∃ piece, readStep env setup.conversion exposure ctx p scalarCall (bitsSource p.s a (wordIndex k)) = some piece ∧
      Nonempty (ReadCasts inputs piece (SourceCasts env) (For.Casts setup)) := by
  obtain ⟨piece,success,typed,_⟩ := bits_word_complete_code setup arithmetic library scalars inputs array index
    getterFresh instanceFresh arraysFresh indexFresh registered constructor coverage exposure scalarCall indexParsed
  exact ⟨piece,success,typed⟩

end IRComparison.WordFrontend.Read
