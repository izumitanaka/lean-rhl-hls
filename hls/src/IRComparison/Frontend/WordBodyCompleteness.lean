import IRComparison.Frontend.WordReadCompleteness

namespace IRComparison.WordFrontend.Certificate
open Lean4Lean LeanTyped LeanTypeInference
variable {casts proofCasts : TypeCasts} [Arithmetic.Includes casts] [Arithmetic.Includes proofCasts]
set_option maxHeartbeats 800000

/-- The body invariant needed both by enclosing source constructs and by the
final connection to the named Lean function. It does not assert parser success. -/
structure BodyCasts (inputs : InputsTyped env ctx p)
    (piece : Piece env ctx p source bodyExpected) (casts : TypeCasts)
    (proofCasts : TypeCasts := casts) where
  sourceCore : {core // Represents source core}
  value : CastTyping env 0 casts ctx sourceCore.val (optionType stateType)
  target : CastTyping env 0 casts ctx piece.represented.val cmdType
  proof : CastTyping env 0 proofCasts ctx piece.checked.proofCore.val piece.checked.core.val

theorem BodyCasts.equality {inputs : InputsTyped env ctx p}
    {piece : Piece env ctx p source bodyExpected} (typed : BodyCasts inputs piece casts proofCasts) :
    CastTyping env 0 proofCasts ctx piece.checked.proofCore.val
      (equalValues (optionType stateType)
        (bodyValue inputs.i.val inputs.x.val inputs.y.val piece.represented.val inputs.s.val inputs.ls.val)
        typed.sourceCore.val) := by
  have same := piece.checked.core.property.unique
    (bodyExpected_represents inputs piece.represented.property typed.sourceCore.property)
  exact same ▸ typed.proof

def BodyCasts.inProofCasts {inputs : InputsTyped env ctx p}
    {piece : Piece env ctx p source bodyExpected} (typed : BodyCasts inputs piece casts proofCasts)
    (embeds : ∀ scope a b, casts scope a b → proofCasts scope a b) :
    BodyCasts inputs piece proofCasts where
  sourceCore := typed.sourceCore
  value := typed.value.mono embeds
  target := typed.target.mono embeds
  proof := typed.proof

def BodyCasts.mapProofs {inputs : InputsTyped env ctx p}
    {piece : Piece env ctx p source bodyExpected} (typed : BodyCasts inputs piece casts proofCasts)
    (embeds : ∀ scope a b, proofCasts scope a b → nextCasts scope a b) :
    BodyCasts inputs piece casts nextCasts where
  sourceCore := typed.sourceCore
  value := typed.value
  target := typed.target
  proof := typed.proof.mono embeds

/-- Reuse a source/target typing invariant under a wider source-conversion
relation without conflating it with conversions in the certificate. -/
def BodyCasts.mapSource {inputs : InputsTyped env ctx p}
    {piece : Piece env ctx p source bodyExpected} (typed : BodyCasts inputs piece casts proofCasts)
    (embeds : ∀ scope a b, casts scope a b → nextCasts scope a b) :
    BodyCasts inputs piece nextCasts proofCasts where
  sourceCore := typed.sourceCore
  value := typed.value.mono embeds
  target := typed.target.mono embeds
  proof := typed.proof

def copyConstructor : VExpr := .forallE (.const ``Nat [])
  (.forallE (.const ``Nat []) (.forallE (.const ``Nat []) cmdType))
def copySourceSignature : VExpr := .forallE stateType (.forallE (.const ``Nat [])
  (.forallE (.const ``Nat []) (.forallE (.const ``Nat []) (optionType stateType))))

/-- Whole-array copy retains the same source/target/proof invariant as stores
and sequencing. The existing successful parser lemma supplies its actual code. -/
theorem body_copy_invariant_complete_code (inputs : InputsTyped env ctx p)
    (destination : NatArgument env ctx d) (origin : NatArgument env ctx s) (count : NatArgument env ctx n)
    (registered : env.constants ``WordFrontendFacts.copy = some ⟨0,copySignature⟩)
    (constructor : env.constants ``HybridWord.Cmd.copy = some ⟨0,copyConstructor⟩)
    (copier : env.constants ``HybridWord.State.copy = some ⟨0,copySourceSignature⟩)
    (conv : Conversion env) (exposure : Exposure env) (casts : TypeCasts) [Arithmetic.Includes casts] (coverage : conv.Covers 0 casts) :
    ∃ piece, bodyStep env conv exposure (fun _ _ _ => none) (fun _ _ _ => none)
        (fun _ _ => none) (fun _ _ _ => none) ctx p (app ``HybridWord.State.copy [p.s,d,s,n]) = some piece ∧
      Nonempty (BodyCasts inputs piece casts) ∧ piece.code = app ``HybridWord.Cmd.copy [d,s,n] := by
  obtain ⟨piece,parsed,proofTyped,code⟩ := body_copy_complete inputs destination origin count registered conv exposure coverage
  have args := List.Forall₂.cons destination.represented.property
    (.cons origin.represented.property (.cons count.represented.property .nil))
  have targetRep : Represents piece.code (applications (.const ``HybridWord.Cmd.copy [])
      [destination.represented.val,origin.represented.val,count.represented.val]) := by
    rw [code]
    exact app_represents (.constant rfl) args
  refine ⟨piece,parsed,⟨⟨⟨_,app_represents (.constant rfl) (.cons inputs.s.property args)⟩,
    ?_,?_,proofTyped⟩⟩,code⟩
  · have h : DirectTyping env 0 ctx (.const ``HybridWord.State.copy []) copySourceSignature :=
      .constant copier (by simp) rfl
    have a1 := DirectTyping.application h inputs.hs
    simp only [copySourceSignature,stateType,optionType,VExpr.inst] at a1
    have a2 := DirectTyping.application a1 destination.typed
    simp only [VExpr.inst] at a2
    have a3 := DirectTyping.application a2 origin.typed
    simp only [VExpr.inst] at a3
    exact (DirectTyping.application a3 count.typed).withCasts casts
  · rw [piece.represented.property.unique targetRep]
    have h : DirectTyping env 0 ctx (.const ``HybridWord.Cmd.copy []) copyConstructor :=
      .constant constructor (by simp) rfl
    have a1 := DirectTyping.application h destination.typed
    simp only [copyConstructor,cmdType,VExpr.inst] at a1
    have a2 := DirectTyping.application a1 origin.typed
    simp only [VExpr.inst] at a2
    exact (DirectTyping.application a2 count.typed).withCasts casts

/-- Projection for callers that need only success and typing. -/
theorem body_copy_invariant_complete (inputs : InputsTyped env ctx p)
    (destination : NatArgument env ctx d) (origin : NatArgument env ctx s) (count : NatArgument env ctx n)
    (registered : env.constants ``WordFrontendFacts.copy = some ⟨0,copySignature⟩)
    (constructor : env.constants ``HybridWord.Cmd.copy = some ⟨0,copyConstructor⟩)
    (copier : env.constants ``HybridWord.State.copy = some ⟨0,copySourceSignature⟩)
    (conv : Conversion env) (exposure : Exposure env) (casts : TypeCasts) [Arithmetic.Includes casts] (coverage : conv.Covers 0 casts) :
    ∃ piece, bodyStep env conv exposure (fun _ _ _ => none) (fun _ _ _ => none)
        (fun _ _ => none) (fun _ _ _ => none) ctx p (app ``HybridWord.State.copy [p.s,d,s,n]) = some piece ∧
      Nonempty (BodyCasts inputs piece casts) := by
  obtain ⟨piece,parsed,typed,_⟩ := body_copy_invariant_complete_code inputs destination origin count
    registered constructor copier conv exposure casts coverage
  exact ⟨piece,parsed,typed⟩

def storeResult : VExpr := equalValues (optionType stateType)
  (bodyValue (.bvar 8) (.bvar 7) (.bvar 6)
    (applications (.const ``HybridWord.Cmd.store []) [.bvar 11,.bvar 10,.bvar 9]) (.bvar 5) (.bvar 4))
  (applications (.const ``HybridWord.State.write []) [.bvar 5,.bvar 11,.bvar 3,.bvar 2])
def storeSignature : VExpr := .forallE (.const ``Nat []) (.forallE exprType (.forallE exprType
  (inputsType (.forallE wordType (.forallE wordType
    (.forallE Arithmetic.binaryFirstPremise (.forallE Arithmetic.binarySecondPremise storeResult)))))))
def storeConstructor : VExpr := .forallE (.const ``Nat []) (.forallE exprType (.forallE exprType cmdType))
def writeSignature : VExpr := .forallE stateType (.forallE (.const ``Nat [])
  (.forallE wordType (.forallE wordType (optionType stateType))))

theorem store_typed (inputs : InputsTyped env ctx p) (array : NatArgument env ctx a)
    {j : Piece env ctx p k scalarExpected} {e : Piece env ctx p v scalarExpected}
    (index : ScalarCasts inputs j casts) (value : ScalarCasts inputs e casts)
    (registered : env.constants ``WordFrontendFacts.store = some ⟨0,storeSignature⟩) :
    CastTyping env 0 casts ctx
      (applications (.const ``WordFrontendFacts.store [])
        ([array.represented.val,j.represented.val,e.represented.val] ++ inputs.args ++
          [index.sourceCore.val,value.sourceCore.val,j.checked.proofCore.val,e.checked.proofCore.val]))
      (equalValues (optionType stateType)
        (bodyValue inputs.i.val inputs.x.val inputs.y.val
          (applications (.const ``HybridWord.Cmd.store []) [array.represented.val,j.represented.val,e.represented.val])
          inputs.s.val inputs.ls.val)
        (applications (.const ``HybridWord.State.write [])
          [inputs.s.val,array.represented.val,index.sourceCore.val,value.sourceCore.val])) := by
  have fact : CastTyping env 0 casts ctx (.const ``WordFrontendFacts.store []) storeSignature :=
    .constant registered (by simp) rfl
  have first := CastTyping.application fact (array.typed.withCasts casts)
  simp only [storeSignature,inputsType,exprType,wordType,stateType,wordsType,VExpr.inst] at first
  have second := CastTyping.application first index.target
  simp only [VExpr.inst] at second
  have third := CastTyping.application second value.target
  simp only [VExpr.inst] at third
  have fourth := inputs.apply_casts third
  simp only [InputsTyped.instantiate,storeResult,Arithmetic.binaryFirstPremise,Arithmetic.binarySecondPremise,
    scalarValue,bodyValue,equalValues,optionType,wordType,stateType,someValue,applications,Nat.reduceAdd,
    ← VExpr.lift_instN_lo,VExpr.inst_lift,VExpr.inst,VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] at fourth
  have fifth := CastTyping.checkedApplication fourth index.value
  simp only [Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst_lift,VExpr.inst,VExpr.instVar_lower,
    VExpr.instVar_zero,VExpr.instVar_succ] at fifth
  have sixth := CastTyping.checkedApplication fifth value.value
  simp only [Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst_lift,VExpr.inst,VExpr.instVar_lower,
    VExpr.instVar_zero,VExpr.instVar_succ] at sixth
  have seventh := CastTyping.application sixth index.equality
  simp only [Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst_lift,VExpr.inst,VExpr.instVar_lower,
    VExpr.instVar_zero,VExpr.instVar_succ] at seventh
  simpa only [InputsTyped.args,applications,List.cons_append,List.nil_append,scalarValue,bodyValue,
    equalValues,optionType,wordType,stateType,someValue,Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst_lift,
    VExpr.inst,VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] using
    CastTyping.application seventh value.equality

theorem store_finish (inputs : InputsTyped env ctx p) (array : NatArgument env ctx a)
    {j : Piece env ctx p k scalarExpected} {e : Piece env ctx p v scalarExpected}
    (index : ScalarCasts inputs j casts) (value : ScalarCasts inputs e casts)
    (registered : env.constants ``WordFrontendFacts.store = some ⟨0,storeSignature⟩)
    (coverage : Conversion.Covers conv 0 casts) (exposure : Exposure env) :
    ∃ result, finish env conv exposure ctx
      (bodyExpected p (app ``HybridWord.Cmd.store [a,j.code,e.code])
        (app ``HybridWord.State.write [p.s,a,k,v]))
      (app ``HybridWord.Cmd.store [a,j.code,e.code])
      (app ``WordFrontendFacts.store ([a,j.code,e.code] ++ p.args ++ [k,v,j.checked.proof,e.checked.proof]))
      (j.checked.known.orElse e.checked.known) = some result ∧
      CastTyping env 0 casts ctx result.proofCore.val result.core.val ∧
      result.code = app ``HybridWord.Cmd.store [a,j.code,e.code] ∧
      result.proof = app ``WordFrontendFacts.store ([a,j.code,e.code] ++ p.args ++ [k,v,j.checked.proof,e.checked.proof]) := by
  exact finish_cast_complete (bodyExpected_represents inputs
    (app_represents (.constant rfl) (.cons array.represented.property
      (.cons j.represented.property (.cons e.represented.property .nil))))
    (app_represents (.constant rfl) (.cons inputs.s.property (.cons array.represented.property
      (.cons index.sourceCore.property (.cons value.sourceCore.property .nil))))))
    (app_represents (.constant rfl) (.cons array.represented.property (.cons j.represented.property
      (.cons e.represented.property (.cons inputs.i.property (.cons inputs.x.property (.cons inputs.y.property
        (.cons inputs.s.property (.cons inputs.ls.property (.cons index.sourceCore.property
          (.cons value.sourceCore.property (.cons j.checked.proofCore.property
            (.cons e.checked.proofCore.property .nil)))))))))))))
    (store_typed inputs array index value registered)
    ((known_casts j.checked index.proof).orElse (known_casts e.checked value.proof)) coverage exposure _

/-- The actual write branch composes arbitrary parsed index/value expressions.
The full source/target/proof invariant is returned for later sequencing. -/
theorem store_step_invariant_complete_code (inputs : InputsTyped env ctx p) (array : NatArgument env ctx a)
    {j : Piece env ctx p k scalarExpected} {e : Piece env ctx p v scalarExpected}
    (index : ScalarCasts inputs j casts proofCasts) (value : ScalarCasts inputs e casts proofCasts)
    (registered : env.constants ``WordFrontendFacts.store = some ⟨0,storeSignature⟩)
    (constructor : env.constants ``HybridWord.Cmd.store = some ⟨0,storeConstructor⟩)
    (writer : env.constants ``HybridWord.State.write = some ⟨0,writeSignature⟩)
    (embeds : ∀ scope a b, casts scope a b → proofCasts scope a b)
    (coverage : Conversion.Covers conv 0 proofCasts) (exposure : Exposure env)
    (scalarCall : PieceParser env scalarExpected) (readCall : PieceParser env readExpected)
    (stepCall : StepParser env) (bodyCall : PieceParser env bodyExpected)
    (indexParsed : scalarCall ctx p k = some j)
    (valueParsed : scalarCall ctx p v = some e) :
    ∃ piece, bodyStep env conv exposure scalarCall readCall stepCall bodyCall ctx p (app ``HybridWord.State.write [p.s,a,k,v]) = some piece ∧
      Nonempty (BodyCasts inputs piece casts proofCasts) ∧
      piece.code = app ``HybridWord.Cmd.store [a,j.code,e.code] := by
  obtain ⟨artifact,checked,typed,_,_⟩ := store_finish inputs array (index.inProofCasts embeds) (value.inProofCasts embeds) registered coverage exposure
  obtain ⟨ac,atran,asame⟩ := array.represented.property.translate_complete
  let ca : ClosedTerm := ⟨a,array.closed,ac⟩
  let code := ClosedTerm.app ``HybridWord.Cmd.store [ca,j.closedTerm,e.closedTerm]
  let piece : Piece env ctx p (app ``HybridWord.State.write [p.s,a,k,v]) bodyExpected :=
    ⟨code.val,artifact,code.closed,code.represented⟩
  have closedA : closedTerm a = some ca := by
    simp only [closedTerm,array.closed,atran,ca,bind,Option.bind,dite_true,pure]
  refine ⟨piece,?_,⟨⟨⟨_,app_represents (f := Lean.Expr.const ``HybridWord.State.write []) (.constant rfl)
    (.cons inputs.s.property (.cons array.represented.property
      (.cons index.sourceCore.property (.cons value.sourceCore.property .nil))))⟩,?_,?_,typed⟩⟩,rfl⟩
  · have same := sameTerm_complete inputs.s.property inputs.s.property
    have reduced : leadingLet (app ``HybridWord.State.write [p.s,a,k,v]) = none := rfl
    have head : (app ``HybridWord.State.write [p.s,a,k,v]).getAppFn.constName? = some ``HybridWord.State.write := rfl
    have args : (app ``HybridWord.State.write [p.s,a,k,v]).getAppArgs.toList = [p.s,a,k,v] := rfl
    simp only [bodyStep,reduced,head,args]
    simp [same,closedA,indexParsed,valueParsed,ClosedTerm.app,Piece.closedTerm,ca,code,piece,app] at checked ⊢
    simp only [checked,Option.bind_some]
  · have h : CastTyping env 0 casts ctx (.const ``HybridWord.State.write []) writeSignature :=
      .constant writer (by simp) rfl
    have a1 := CastTyping.application h (inputs.hs.withCasts casts)
    simp only [writeSignature,wordType,stateType,optionType,VExpr.inst] at a1
    have a2 := CastTyping.application a1 (array.typed.withCasts casts)
    simp only [VExpr.inst] at a2
    have a3 := CastTyping.checkedApplication a2 index.value
    simp only [VExpr.inst] at a3
    exact .checkedApplication a3 value.value
  · have h : CastTyping env 0 casts ctx (.const ``HybridWord.Cmd.store []) storeConstructor :=
      .constant constructor (by simp) rfl
    change CastTyping env 0 casts ctx
      (applications (.const ``HybridWord.Cmd.store []) [ac.val,j.represented.val,e.represented.val]) cmdType
    rw [asame]
    have a1 := CastTyping.application h (array.typed.withCasts casts)
    simp only [storeConstructor,exprType,cmdType,VExpr.inst] at a1
    have a2 := CastTyping.application a1 index.target
    simp only [VExpr.inst] at a2
    exact .application a2 value.target

theorem store_step_invariant_complete (inputs : InputsTyped env ctx p) (array : NatArgument env ctx a)
    {j : Piece env ctx p k scalarExpected} {e : Piece env ctx p v scalarExpected}
    (index : ScalarCasts inputs j casts proofCasts) (value : ScalarCasts inputs e casts proofCasts)
    (registered : env.constants ``WordFrontendFacts.store = some ⟨0,storeSignature⟩)
    (constructor : env.constants ``HybridWord.Cmd.store = some ⟨0,storeConstructor⟩)
    (writer : env.constants ``HybridWord.State.write = some ⟨0,writeSignature⟩)
    (embeds : ∀ scope a b, casts scope a b → proofCasts scope a b)
    (coverage : Conversion.Covers conv 0 proofCasts) (exposure : Exposure env)
    (scalarCall : PieceParser env scalarExpected) (readCall : PieceParser env readExpected)
    (stepCall : StepParser env) (bodyCall : PieceParser env bodyExpected)
    (indexParsed : scalarCall ctx p k = some j)
    (valueParsed : scalarCall ctx p v = some e) :
    ∃ piece, bodyStep env conv exposure scalarCall readCall stepCall bodyCall ctx p (app ``HybridWord.State.write [p.s,a,k,v]) = some piece ∧
      Nonempty (BodyCasts inputs piece casts proofCasts) := by
  obtain ⟨piece,success,typed,_⟩ := store_step_invariant_complete_code inputs array index value registered
    constructor writer embeds coverage exposure scalarCall readCall stepCall bodyCall indexParsed valueParsed
  exact ⟨piece,success,typed⟩

/-- Compatibility specialization with the same source and proof conversions. -/
theorem store_step_complete (inputs : InputsTyped env ctx p) (array : NatArgument env ctx a)
    {j : Piece env ctx p k scalarExpected} {e : Piece env ctx p v scalarExpected}
    (index : ScalarCasts inputs j casts) (value : ScalarCasts inputs e casts)
    (registered : env.constants ``WordFrontendFacts.store = some ⟨0,storeSignature⟩)
    (constructor : env.constants ``HybridWord.Cmd.store = some ⟨0,storeConstructor⟩)
    (writer : env.constants ``HybridWord.State.write = some ⟨0,writeSignature⟩)
    (coverage : Conversion.Covers conv 0 casts) (exposure : Exposure env)
    (scalarCall : PieceParser env scalarExpected) (readCall : PieceParser env readExpected)
    (stepCall : StepParser env) (bodyCall : PieceParser env bodyExpected)
    (indexParsed : scalarCall ctx p k = some j)
    (valueParsed : scalarCall ctx p v = some e) :
    ∃ piece, bodyStep env conv exposure scalarCall readCall stepCall bodyCall ctx p (app ``HybridWord.State.write [p.s,a,k,v]) = some piece ∧
      Nonempty (BodyCasts inputs piece casts) := by
  exact store_step_invariant_complete inputs array index value registered constructor writer
    (fun _ _ _ h => h) coverage exposure scalarCall readCall stepCall bodyCall indexParsed valueParsed

/-- The exact Option bind header produced by ordinary Lean elaboration. -/
def optionBindHeader (domain result : VExpr) : VExpr := applications (.const ``Bind.bind [.zero,.zero])
  [.const ``Option [.zero], applications (.const ``Monad.toBind [.zero,.zero])
    [.const ``Option [.zero],.const ``instMonadOption [.zero]],domain,result]
def stateBindHeader : VExpr := optionBindHeader stateType stateType

theorem stateBind_represents : Represents (bindHead state state) stateBindHeader := by
  exact .app (.app (.app (.app (.constant rfl) (.constant rfl))
    (.app (.app (.constant rfl) (.constant rfl)) (.constant rfl))) (.constant rfl)) (.constant rfl)

theorem stateBind_inst (v : VExpr) (k : Nat) : stateBindHeader.inst v k = stateBindHeader :=
  (stateBind_represents.closed 0 rfl).instN_eq (Nat.zero_le k)

def bindSignature : VConstant := ⟨2,
  .forallE (.forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 1))))
    (.forallE (.app (.const ``Bind [.param 0,.param 1]) (.bvar 0))
      (.forallE (.sort (.succ (.param 0))) (.forallE (.sort (.succ (.param 0)))
        (.forallE (.app (.bvar 3) (.bvar 1))
          (.forallE (.forallE (.bvar 2) (.app (.bvar 5) (.bvar 2)))
            (.app (.bvar 5) (.bvar 2)))))))⟩
def monadBindSignature : VConstant := ⟨2,
  .forallE (.forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 1))))
    (.forallE (.app (.const ``Monad [.param 0,.param 1]) (.bvar 0))
      (.app (.const ``Bind [.param 0,.param 1]) (.bvar 1)))⟩
def optionMonadSignature : VConstant := ⟨1,
  .app (.const ``Monad [.param 0,.param 0]) (.const ``Option [.param 0])⟩

structure BindSignatures (env : VEnv) : Prop where
  option : env.constants ``Option = some optionSignature
  bind : env.constants ``Bind.bind = some bindSignature
  projector : env.constants ``Monad.toBind = some monadBindSignature
  instanceOption : env.constants ``instMonadOption = some optionMonadSignature

def optionBindPrefix : VExpr := applications (.const ``Bind.bind [.zero,.zero])
  [.const ``Option [.zero], applications (.const ``Monad.toBind [.zero,.zero])
    [.const ``Option [.zero],.const ``instMonadOption [.zero]]]

def optionBindPrefixType : VExpr := .forallE (.sort (.succ .zero)) (.forallE (.sort (.succ .zero))
  (.forallE (optionType (.bvar 1)) (.forallE (.forallE (.bvar 2) (optionType (.bvar 2))) (optionType (.bvar 2)))))

theorem BindSignatures.prefix_typed (signatures : BindSignatures env) :
    DirectTyping env 0 ctx optionBindPrefix optionBindPrefixType := by
  have ot : DirectTyping env 0 ctx (.const ``Option [.zero])
      (.forallE (.sort (.succ .zero)) (.sort (.succ .zero))) :=
    .constant signatures.option (by simp [VLevel.WF]) rfl
  have mt : DirectTyping env 0 ctx (.const ``instMonadOption [.zero])
      (.app (.const ``Monad [.zero,.zero]) (.const ``Option [.zero])) :=
    .constant signatures.instanceOption (by simp [VLevel.WF]) rfl
  have pt : DirectTyping env 0 ctx (.const ``Monad.toBind [.zero,.zero])
      (monadBindSignature.type.instL [.zero,.zero]) :=
    .constant signatures.projector (by simp [VLevel.WF]) rfl
  have p1 := DirectTyping.application pt ot
  simp only [monadBindSignature,VExpr.instL,VLevel.inst,VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ] at p1
  have p2 := DirectTyping.application p1 mt
  simp only [VExpr.inst,VExpr.instVar_zero,VExpr.lift,VExpr.liftN] at p2
  have bt : DirectTyping env 0 ctx (.const ``Bind.bind [.zero,.zero])
      (bindSignature.type.instL [.zero,.zero]) :=
    .constant signatures.bind (by simp [VLevel.WF]) rfl
  have b1 := DirectTyping.application bt ot
  simp only [bindSignature,VExpr.instL,VLevel.inst,VExpr.inst,VExpr.instVar_lower,
    VExpr.instVar_zero,VExpr.instVar_succ] at b1
  have b2 := DirectTyping.application b1 p2
  simp only [VExpr.inst,VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] at b2
  exact b2

theorem BindSignatures.header_typed (signatures : BindSignatures env)
    (domainTyped : DirectTyping env 0 ctx domain (.sort (.succ .zero)))
    (resultTyped : DirectTyping env 0 ctx result (.sort (.succ .zero)))
    (domainClosed : domain.ClosedN 0) (resultClosed : result.ClosedN 0) :
    DirectTyping env 0 ctx (optionBindHeader domain result)
      (.forallE (optionType domain)
        (.forallE (.forallE domain (optionType result)) (optionType result))) := by
  have dl (n k : Nat) : domain.liftN n k = domain := domainClosed.liftN_eq (Nat.zero_le _)
  have di (v : VExpr) (k : Nat) : domain.inst v k = domain := domainClosed.instN_eq (Nat.zero_le _)
  have rl (n k : Nat) : result.liftN n k = result := resultClosed.liftN_eq (Nat.zero_le _)
  have ri (v : VExpr) (k : Nat) : result.inst v k = result := resultClosed.instN_eq (Nat.zero_le _)
  have b2 := signatures.prefix_typed (ctx := ctx)
  have b3 := DirectTyping.application b2 domainTyped
  simp only [optionBindPrefixType,VExpr.inst,VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ,
    VExpr.lift,dl,di,rl,ri,VExpr.liftN,liftVar,Nat.reduceAdd,Nat.reduceLT,ite_true,ite_false] at b3
  simpa only [optionBindHeader,optionBindPrefix,applications,optionType,VExpr.inst,VExpr.instVar_lower,
    VExpr.instVar_zero,VExpr.instVar_succ,VExpr.lift,dl,di,rl,ri,VExpr.liftN,liftVar,Nat.reduceAdd,Nat.reduceLT,ite_true,ite_false] using DirectTyping.application b3 resultTyped

theorem BindSignatures.state_header_typed (signatures : BindSignatures env)
    (stateDeclared : env.constants ``HybridWord.State = some ⟨0,.sort (.succ .zero)⟩) :
    DirectTyping env 0 ctx stateBindHeader
      (.forallE (optionType stateType)
        (.forallE (.forallE stateType (optionType stateType)) (optionType stateType))) := by
  have stateTyped : DirectTyping env 0 ctx stateType (.sort (.succ .zero)) :=
    .constant stateDeclared (by simp) rfl
  exact signatures.header_typed stateTyped stateTyped (by trivial) (by trivial)

def sequenceFirstPremise : VExpr := equalValues (optionType stateType)
  (bodyValue (.bvar 6) (.bvar 5) (.bvar 4) (.bvar 8) (.bvar 3) (.bvar 2)) (.bvar 1)
def sequenceNextPremise : VExpr := .forallE stateType
  (equalValues (optionType stateType)
    (bodyValue (.bvar 8) (.bvar 7) (.bvar 6) (.bvar 9) (.bvar 0) (.bvar 4))
    (.app (.bvar 2) (.bvar 0)))
def sequenceResult : VExpr := equalValues (optionType stateType)
  (bodyValue (.bvar 8) (.bvar 7) (.bvar 6)
    (applications (.const ``HybridWord.Cmd.seq []) [.bvar 10,.bvar 9]) (.bvar 5) (.bvar 4))
  (applications stateBindHeader [.bvar 3,.bvar 2])
def sequenceSignature : VExpr := .forallE cmdType (.forallE cmdType
  (inputsType (.forallE (optionType stateType)
    (.forallE (.forallE stateType (optionType stateType))
      (.forallE sequenceFirstPremise (.forallE sequenceNextPremise sequenceResult))))))

/-- The continuation fact expects a function application, while the recursively
constructed proof mentions its body. This explicitly isolates that beta
conversion from the compiler's semantic transformation. -/
def sequenceContinuationType (inputs : InputsTyped env ctx p) (b next : VExpr) : VExpr :=
  .forallE stateType (equalValues (optionType stateType)
    (bodyValue inputs.i.val.lift inputs.x.val.lift inputs.y.val.lift b.lift
      (.bvar 0) inputs.ls.val.lift)
    (.app next.lift (.bvar 0)))

theorem sequence_typed (inputs : InputsTyped env ctx p)
    {a : Piece env ctx p first bodyExpected} (left : BodyCasts inputs a casts)
    (rightTarget : CastTyping env 0 casts ctx b cmdType)
    (nextTyped : CastTyping env 0 casts ctx next (.forallE stateType (optionType stateType)))
    (nextProof : CastTyping env 0 casts ctx proofNext actual)
    (beta : casts ctx actual (sequenceContinuationType inputs b next))
    (registered : env.constants ``WordFrontendFacts.sequence = some ⟨0,sequenceSignature⟩) :
    CastTyping env 0 casts ctx
      (applications (.const ``WordFrontendFacts.sequence [])
        ([a.represented.val,b] ++ inputs.args ++
          [left.sourceCore.val,next,a.checked.proofCore.val,proofNext]))
      (equalValues (optionType stateType)
        (bodyValue inputs.i.val inputs.x.val inputs.y.val
          (applications (.const ``HybridWord.Cmd.seq []) [a.represented.val,b]) inputs.s.val inputs.ls.val)
        (applications stateBindHeader [left.sourceCore.val,next])) := by
  have fact : CastTyping env 0 casts ctx (.const ``WordFrontendFacts.sequence []) sequenceSignature :=
    .constant (levels := []) registered (by simp) rfl
  have a1 := CastTyping.application fact left.target
  simp only [sequenceSignature,inputsType,cmdType,wordType,stateType,wordsType,optionType,VExpr.inst] at a1
  have a2 := CastTyping.application a1 rightTarget
  simp only [VExpr.inst] at a2
  have a3 := inputs.apply_casts a2
  simp only [InputsTyped.instantiate,sequenceFirstPremise,sequenceNextPremise,sequenceResult,
    bodyValue,equalValues,optionType,stateType,wordType,applications,Nat.reduceAdd,
    ← VExpr.lift_instN_lo,VExpr.inst_lift,stateBind_inst,VExpr.inst,
    VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] at a3
  have a4 := CastTyping.application a3 left.value
  simp only [Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst_lift,stateBind_inst,VExpr.inst,
    VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] at a4
  have a5 := CastTyping.application a4 nextTyped
  simp only [Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst_lift,stateBind_inst,VExpr.inst,
    VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] at a5
  have a6 := CastTyping.application a5 left.equality
  simp only [Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst_lift,stateBind_inst,VExpr.inst,
    VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] at a6
  have cast := beta
  simp only [sequenceContinuationType,bodyValue,equalValues,optionType,stateType] at cast
  simpa only [InputsTyped.args,applications,List.cons_append,List.nil_append,bodyValue,
    equalValues,optionType,stateType,Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst_lift,
    stateBind_inst,VExpr.inst,VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] using
    CastTyping.convertedApplication a6 nextProof cast

def sequenceNextActual (inputs : InputsTyped env ctx p) (b source : VExpr) : VExpr :=
  .forallE stateType (equalValues (optionType stateType)
    (bodyValue inputs.i.val.lift inputs.x.val.lift inputs.y.val.lift b.lift
      (.bvar 0) inputs.ls.val.lift) source)

theorem sequence_next_typed (inputs : InputsTyped env ctx p)
    (closed : ClosedConstantTypes env) (stable : ClosedCasts casts)
    (stateDeclared : env.constants ``HybridWord.State = some ⟨0,.sort (.succ .zero)⟩)
    {b : Piece env (stateType::ctx) {p.lift with s := .bvar 0} nextBody bodyExpected}
    (right : BodyCasts (inputs.nextState closed) b casts proofCasts) :
    CastTyping env 0 casts ctx b.represented.val cmdType ∧
    CastTyping env 0 casts ctx (.lam stateType right.sourceCore.val)
      (.forallE stateType (optionType stateType)) ∧
    CastTyping env 0 proofCasts ctx (.lam stateType b.checked.proofCore.val)
      (sequenceNextActual inputs b.represented.val right.sourceCore.val) := by
  have targetClosed : b.represented.val.ClosedN 0 := b.represented.property.closed 0 b.closed
  have stateTyped : DirectTyping env 0 ctx stateType (.sort (.succ .zero)) :=
    .constant stateDeclared (by simp) rfl
  refine ⟨right.target.closed_context stable targetClosed ctx,
    .lambda (stateTyped.withCasts casts) right.value,?_⟩
  have proof := CastTyping.lambda (stateTyped.withCasts proofCasts) right.equality
  simpa only [sequenceNextActual,InputsTyped.nextState,InputsTyped.lift,
    targetClosed.lift_eq] using proof

def sequenceSource (first next : Lean.Expr) : Lean.Expr := Lean.mkApp2 (bindHead state state) first next

theorem sequence_finish (inputs : InputsTyped env ctx p)
    (closed : ClosedConstantTypes env) (stable : ClosedCasts casts)
    (embeds : ∀ scope a b, casts scope a b → proofCasts scope a b)
    (stateDeclared : env.constants ``HybridWord.State = some ⟨0,.sort (.succ .zero)⟩)
    {a : Piece env ctx p first bodyExpected} (left : BodyCasts inputs a casts proofCasts)
    {b : Piece env (stateType::ctx) {p.lift with s := .bvar 0} nextBody bodyExpected}
    (right : BodyCasts (inputs.nextState closed) b casts proofCasts)
    (beta : proofCasts ctx (sequenceNextActual inputs b.represented.val right.sourceCore.val)
      (sequenceContinuationType inputs b.represented.val (.lam stateType right.sourceCore.val)))
    (registered : env.constants ``WordFrontendFacts.sequence = some ⟨0,sequenceSignature⟩)
    (coverage : Conversion.Covers conv 0 proofCasts) (exposure : Exposure env)
    (binder : Lean.Name) (info : Lean.BinderInfo) :
    ∃ result, finish env conv exposure ctx
      (bodyExpected p (app ``HybridWord.Cmd.seq [a.code,b.code])
        (sequenceSource first (.lam binder state nextBody info)))
      (app ``HybridWord.Cmd.seq [a.code,b.code])
      (app ``WordFrontendFacts.sequence ([a.code,b.code] ++ p.args ++
        [first,.lam binder state nextBody info,a.checked.proof,.lam binder state b.checked.proof info]))
      (a.checked.known.orElse b.checked.known) = some result ∧
      CastTyping env 0 proofCasts ctx result.proofCore.val result.core.val ∧
      result.code = app ``HybridWord.Cmd.seq [a.code,b.code] ∧
      result.proof = app ``WordFrontendFacts.sequence ([a.code,b.code] ++ p.args ++
        [first,.lam binder state nextBody info,a.checked.proof,.lam binder state b.checked.proof info]) := by
  obtain ⟨target,nextTyped,nextProof⟩ := sequence_next_typed inputs closed stable stateDeclared right
  have typed := sequence_typed inputs (left.inProofCasts embeds) (target.mono embeds)
    (nextTyped.mono embeds) nextProof beta registered
  exact finish_cast_complete
    (bodyExpected_represents inputs
      (app_represents (.constant rfl) (.cons a.represented.property (.cons b.represented.property .nil)))
      (.app (.app stateBind_represents left.sourceCore.property) (.lam (.constant rfl) right.sourceCore.property)))
    (app_represents (.constant rfl) (.cons a.represented.property (.cons b.represented.property
      (.cons inputs.i.property (.cons inputs.x.property (.cons inputs.y.property
        (.cons inputs.s.property (.cons inputs.ls.property (.cons left.sourceCore.property
          (.cons (.lam (.constant rfl) right.sourceCore.property)
            (.cons a.checked.proofCore.property (.cons (.lam (.constant rfl) b.checked.proofCore.property) .nil))))))))))))
    typed ((known_casts a.checked left.proof).orElse (known_casts b.checked right.proof))
    coverage exposure _

def sequenceConstructor : VExpr := .forallE cmdType (.forallE cmdType cmdType)

/-- Successful composition by the real body parser. The only additional
certificate conversion is the explicitly displayed continuation beta rule;
no successful typechecker execution is assumed. -/
theorem sequence_step_complete_code (inputs : InputsTyped env ctx p)
    (closed : ClosedConstantTypes env) (stable : ClosedCasts casts)
    (embeds : ∀ scope a b, casts scope a b → proofCasts scope a b)
    (stateDeclared : env.constants ``HybridWord.State = some ⟨0,.sort (.succ .zero)⟩)
    {a : Piece env ctx p first bodyExpected} (left : BodyCasts inputs a casts proofCasts)
    {b : Piece env (stateType::ctx) {p.lift with s := .bvar 0} nextBody bodyExpected}
    (right : BodyCasts (inputs.nextState closed) b casts proofCasts)
    (beta : proofCasts ctx (sequenceNextActual inputs b.represented.val right.sourceCore.val)
      (sequenceContinuationType inputs b.represented.val (.lam stateType right.sourceCore.val)))
    (registered : env.constants ``WordFrontendFacts.sequence = some ⟨0,sequenceSignature⟩)
    (constructor : env.constants ``HybridWord.Cmd.seq = some ⟨0,sequenceConstructor⟩)
    (coverage : Conversion.Covers conv 0 proofCasts) (exposure : Exposure env)
    (bindLibrary : BindSignatures env)
    (binder : Lean.Name) (info : Lean.BinderInfo) (scalarCall : PieceParser env scalarExpected) (readCall : PieceParser env readExpected)
    (stepCall : StepParser env) (bodyCall : PieceParser env bodyExpected)
    (firstParsed : bodyCall ctx p first = some a)
    (nextParsed : bodyCall (stateType::ctx) {p.lift with s := .bvar 0}
      nextBody = some b) :
    ∃ piece, bodyStep env conv exposure scalarCall readCall stepCall bodyCall ctx p
      (sequenceSource first (.lam binder state nextBody info)) = some piece ∧
      Nonempty (BodyCasts inputs piece casts proofCasts) ∧ piece.code = app ``HybridWord.Cmd.seq [a.code,b.code] := by
  obtain ⟨artifact,checked,typed,_,_⟩ := sequence_finish inputs closed stable embeds stateDeclared
    left right beta registered coverage exposure binder info
  let code := ClosedTerm.app ``HybridWord.Cmd.seq [a.closedTerm,b.closedTerm]
  let piece : Piece env ctx p (sequenceSource first (.lam binder state nextBody info)) bodyExpected :=
    ⟨code.val,artifact,code.closed,code.represented⟩
  obtain ⟨_,nextTyped,_⟩ := sequence_next_typed inputs closed stable stateDeclared right
  have applied := CastTyping.application ((bindLibrary.state_header_typed stateDeclared).withCasts casts) left.value
  simp only [optionType,stateType,VExpr.inst] at applied
  have sourceTyped := CastTyping.application applied nextTyped
  refine ⟨piece,?_,⟨⟨⟨_,.app (.app stateBind_represents left.sourceCore.property)
    (.lam (.constant rfl) right.sourceCore.property)⟩,sourceTyped,?_,typed⟩⟩,rfl⟩
  · have stateSame := sameTerm_complete (a := state) (b := state)
      (Represents.constant rfl) (Represents.constant rfl)
    have stateCompatible : compatible env conv ctx state state = true := by
      simp only [compatible,stateSame]; rfl
    have translated : translate state = some ⟨stateType,Represents.constant rfl⟩ := rfl
    have reduced : leadingLet (sequenceSource first (.lam binder state nextBody info)) = none := rfl
    have head : (sequenceSource first (.lam binder state nextBody info)).getAppFn.constName? = some ``Bind.bind := rfl
    have args : (sequenceSource first (.lam binder state nextBody info)).getAppArgs.toList =
      [.const ``Option [.zero], Lean.mkAppN (.const ``Monad.toBind [.zero,.zero])
        #[.const ``Option [.zero],.const ``instMonadOption [.zero]],state,state,first,
        .lam binder state nextBody info] := rfl
    simp only [bodyStep,reduced,head,args]
    simp [stateSame,stateCompatible,translated,firstParsed,nextParsed,
      ClosedTerm.app,Piece.closedTerm,code,piece,app,sequenceSource,Lean.mkApp2,Lean.mkAppB] at checked ⊢
    simp only [checked,Option.bind_some]
  · obtain ⟨target,_,_⟩ := sequence_next_typed inputs closed stable stateDeclared right
    have fact : CastTyping env 0 casts ctx (.const ``HybridWord.Cmd.seq []) sequenceConstructor :=
      .constant constructor (by simp) rfl
    have first := CastTyping.application fact left.target
    simp only [sequenceConstructor,cmdType,VExpr.inst] at first
    exact .application first target


theorem sequence_step_complete (inputs : InputsTyped env ctx p)
    (closed : ClosedConstantTypes env) (stable : ClosedCasts casts)
    (embeds : ∀ scope a b, casts scope a b → proofCasts scope a b)
    (stateDeclared : env.constants ``HybridWord.State = some ⟨0,.sort (.succ .zero)⟩)
    {a : Piece env ctx p first bodyExpected} (left : BodyCasts inputs a casts proofCasts)
    {b : Piece env (stateType::ctx) {p.lift with s := .bvar 0} nextBody bodyExpected}
    (right : BodyCasts (inputs.nextState closed) b casts proofCasts)
    (beta : proofCasts ctx (sequenceNextActual inputs b.represented.val right.sourceCore.val)
      (sequenceContinuationType inputs b.represented.val (.lam stateType right.sourceCore.val)))
    (registered : env.constants ``WordFrontendFacts.sequence = some ⟨0,sequenceSignature⟩)
    (constructor : env.constants ``HybridWord.Cmd.seq = some ⟨0,sequenceConstructor⟩)
    (coverage : Conversion.Covers conv 0 proofCasts) (exposure : Exposure env)
    (bindLibrary : BindSignatures env)
    (binder : Lean.Name) (info : Lean.BinderInfo) (scalarCall : PieceParser env scalarExpected) (readCall : PieceParser env readExpected)
    (stepCall : StepParser env) (bodyCall : PieceParser env bodyExpected)
    (firstParsed : bodyCall ctx p first = some a)
    (nextParsed : bodyCall (stateType::ctx) {p.lift with s := .bvar 0}
      nextBody = some b) :
    ∃ piece, bodyStep env conv exposure scalarCall readCall stepCall bodyCall ctx p
      (sequenceSource first (.lam binder state nextBody info)) = some piece ∧
      Nonempty (BodyCasts inputs piece casts proofCasts) := by
  obtain ⟨piece,parsed,typed,_⟩ := sequence_step_complete_code inputs closed stable embeds stateDeclared
    left right beta registered constructor coverage exposure bindLibrary binder info scalarCall readCall stepCall bodyCall
    firstParsed nextParsed
  exact ⟨piece,parsed,typed⟩


/-- The one beta comparison shared by state and value continuations. The
source body is typed independently of the conversion search. -/
def continuationActual (domain lhs sourceBody : VExpr) : VExpr :=
  .forallE domain (equalValues (optionType stateType) lhs sourceBody)
def continuationExpected (domain lhs sourceBody : VExpr) : VExpr :=
  .forallE domain (equalValues (optionType stateType) lhs
    (.app (.lam domain (sourceBody.liftN 1 1)) (.bvar 0)))

theorem continuation_beta_conversion_with_domain (setup : Arithmetic.AliasSetup env)
    (signatures : Arithmetic.Signatures env) (closed : ClosedConstantTypes env)
    (domainClosed : domain.ClosedN 0)
    (resultClosed : resultType.ClosedN 0) (notSort : ∀ u, resultType ≠ .sort u)
    (domainEq : LeanStructuralConversion.Equation env 0 ctx domain expectedDomain)
    (domainProved : LeanStructuralConversion.prove env setup.basic setup.exposure 0 63 ctx domain expectedDomain = some domainEq)
    (domainKind : domainEq.type = .sort (.succ .zero))
    (prefixTyped : CastTyping env 0 (Arithmetic.SourceCasts env) (domain::ctx)
      (.app (.app (.const ``Eq [.succ .zero]) resultType) lhs)
      (.forallE resultType (.sort .zero)))
    (sourceTyped : CastTyping env 0 (Arithmetic.SourceCasts env) (domain::ctx) sourceBody resultType)
    (sourceForm : Arithmetic.ValueForm setup (domain::ctx) sourceBody resultType)
    (eqFresh : ∀ r ∈ setup.rules, ``Eq ≠ r.name) :
    ∃ result, setup.conversion 0 ctx
      (.forallE domain (equalValues resultType lhs sourceBody))
      (.forallE expectedDomain (equalValues resultType lhs
        (Arithmetic.continuationValue domain sourceBody))) = some result := by
  let eqPrefix : VExpr := .app (.app (.const ``Eq [.succ .zero]) resultType) lhs
  have prefixNone : setup.basic 0 (domain::ctx) eqPrefix eqPrefix = none :=
    setup.basic_no_reduction _ _ rfl rfl eqFresh eqFresh rfl
  have wholeNone : setup.basic 0 (domain::ctx) (.app eqPrefix sourceBody)
      (.app eqPrefix (Arithmetic.continuationValue domain sourceBody)) = none :=
    setup.basic_no_reduction _ _ rfl rfl eqFresh eqFresh rfl
  obtain ⟨prefixEq,prefixProved,prefixKind⟩ := LeanStructuralConversion.prove_reflexive_cast_complete
    prefixTyped prefixNone (setup.covers_source_recursive signatures closed 57)
  obtain ⟨value,valueProved,valueKind⟩ := setup.value_beta_proved signatures closed domainClosed
    resultClosed notSort sourceTyped sourceForm 57
  obtain ⟨bodyEq,bodyProved,bodyKind⟩ := LeanStructuralConversion.prove_application_complete
    (leftName := ``Eq) (rightName := ``Eq) rfl rfl
    (fun same => Arithmetic.continuationValue_ne domain sourceBody (VExpr.app.inj same).2)
    wholeNone prefixEq prefixProved prefixKind value valueProved valueKind
  have unequal : VExpr.forallE domain (equalValues resultType lhs sourceBody) ≠
      .forallE expectedDomain (equalValues resultType lhs
        (Arithmetic.continuationValue domain sourceBody)) := by
    intro same
    apply Arithmetic.continuationValue_ne domain sourceBody
    exact (VExpr.app.inj (VExpr.forallE.inj same).2).2
  have notAlias : setup.basic 0 ctx (.forallE domain (equalValues resultType lhs sourceBody))
      (.forallE expectedDomain (equalValues resultType lhs
        (Arithmetic.continuationValue domain sourceBody))) = none := rfl
  obtain ⟨equation,proved,kind⟩ := LeanStructuralConversion.prove_forall_complete unequal notAlias
    domainEq domainProved domainKind bodyEq
    (by simpa only [continuationActual,continuationExpected,equalValues,
      Arithmetic.continuationValue,eqPrefix] using bodyProved) bodyKind
  exact LeanStructuralConversion.conversion_of_prove equation proved kind

theorem continuation_beta_conversion (setup : Arithmetic.AliasSetup env)
    (signatures : Arithmetic.Signatures env) (closed : ClosedConstantTypes env)
    (domainTyped : DirectTyping env 0 ctx domain (.sort (.succ .zero)))
    (domainClosed : domain.ClosedN 0)
    (domainNone : setup.basic 0 ctx domain domain = none)
    (prefixTyped : CastTyping env 0 (Arithmetic.SourceCasts env) (domain::ctx)
      (.app (.app (.const ``Eq [.succ .zero]) (optionType stateType)) lhs)
      (.forallE (optionType stateType) (.sort .zero)))
    (sourceTyped : CastTyping env 0 (Arithmetic.SourceCasts env) (domain::ctx) sourceBody (optionType stateType))
    (sourceForm : Arithmetic.ValueForm setup (domain::ctx) sourceBody (optionType stateType))
    (eqFresh : ∀ r ∈ setup.rules, ``Eq ≠ r.name) :
    ∃ result, setup.conversion 0 ctx
      (continuationActual domain lhs sourceBody)
      (continuationExpected domain lhs sourceBody) = some result := by
  obtain ⟨domainEq,domainProved,domainKind⟩ := LeanStructuralConversion.prove_reflexive_complete
    domainTyped domainNone 62 setup.exposure
  exact continuation_beta_conversion_with_domain setup signatures closed domainClosed
    (by trivial) (by intro u; simp [optionType]) domainEq domainProved domainKind prefixTyped sourceTyped sourceForm eqFresh

/-- The real converter handles both ordinary operation heads and leading
administrative lets. No limit on the size of the continuation body is used. -/
theorem sequence_beta_conversion (setup : Arithmetic.AliasSetup env)
    (signatures : Arithmetic.Signatures env)
    (inputs : InputsTyped env ctx p) (closed : ClosedConstantTypes env)
    {code sourceBody : VExpr}
    (targetTyped : CastTyping env 0 (Arithmetic.SourceCasts env) ctx code cmdType)
    (sourceTyped : CastTyping env 0 (Arithmetic.SourceCasts env) (stateType::ctx) sourceBody (optionType stateType))
    (stateDeclared : env.constants ``HybridWord.State = some ⟨0,.sort (.succ .zero)⟩)
    (optionDeclared : env.constants ``Option = some optionSignature)
    (eqDeclared : env.constants ``Eq = some eqSignature)
    (evalDeclared : env.constants ``HybridWord.Cmd.eval = some ⟨0,evalSignature⟩)
    (sourceForm : Arithmetic.ValueForm setup (stateType::ctx) sourceBody (optionType stateType))
    (stateFresh : ∀ r ∈ setup.rules, ``HybridWord.State ≠ r.name)
    (eqFresh : ∀ r ∈ setup.rules, ``Eq ≠ r.name) :
    ∃ result, setup.conversion 0 ctx
      (sequenceNextActual inputs code sourceBody)
      (sequenceContinuationType inputs code (.lam stateType sourceBody)) = some result := by
  have liftedTarget : CastTyping env 0 (Arithmetic.SourceCasts env) (stateType::ctx) code.lift cmdType := by
    simpa only [cmdType,VExpr.lift,VExpr.liftN] using
      targetTyped.lift closed Arithmetic.SourceCasts.closed stateType
  have evaluation := eval_cast_typed (inputs.nextState closed) evalDeclared liftedTarget
  have prefixTyped := CastTyping.application
    ((equality_head_typed (ctx := stateType::ctx) stateDeclared optionDeclared eqDeclared).withCasts (Arithmetic.SourceCasts env))
    evaluation
  simp only [WordFrontend.optionState,stateType,VExpr.inst,InputsTyped.nextState,InputsTyped.lift] at prefixTyped
  have stateTyped : DirectTyping env 0 ctx stateType (.sort (.succ .zero)) :=
    .constant stateDeclared (by simp) rfl
  exact continuation_beta_conversion setup signatures closed stateTyped (by trivial)
    (setup.basic_no_reduction _ _ rfl rfl stateFresh stateFresh rfl)
    prefixTyped sourceTyped sourceForm eqFresh

/-- The same continuation comparison when a read binds a Word. -/
def valueContinuationLhs (inputs : InputsTyped env ctx p) (code : VExpr) : VExpr :=
  bodyValue inputs.i.val.lift inputs.x.val.lift inputs.y.val.lift code.lift
    inputs.s.val.lift (applications (.const ``List.cons [.zero]) [wordType,.bvar 0,inputs.ls.val.lift])

theorem value_beta_conversion (setup : Arithmetic.AliasSetup env)
    (signatures : Arithmetic.Signatures env)
    (inputs : InputsTyped env ctx p) (closed : ClosedConstantTypes env)
    {code sourceBody : VExpr}
    (targetTyped : CastTyping env 0 (Arithmetic.SourceCasts env) ctx code cmdType)
    (sourceTyped : CastTyping env 0 (Arithmetic.SourceCasts env) (wordType::ctx) sourceBody (optionType stateType))
    (wordDeclared : env.constants ``HybridWord.Word = some ⟨0,.sort (.succ .zero)⟩)
    (consDeclared : env.constants ``List.cons = some consSignature)
    (stateDeclared : env.constants ``HybridWord.State = some ⟨0,.sort (.succ .zero)⟩)
    (optionDeclared : env.constants ``Option = some optionSignature)
    (eqDeclared : env.constants ``Eq = some eqSignature)
    (evalDeclared : env.constants ``HybridWord.Cmd.eval = some ⟨0,evalSignature⟩)
    (sourceForm : Arithmetic.ValueForm setup (wordType::ctx) sourceBody (optionType stateType))
    (eqFresh : ∀ r ∈ setup.rules, ``Eq ≠ r.name) :
    ∃ result, setup.conversion 0 ctx
      (continuationActual wordType (valueContinuationLhs inputs code) sourceBody)
      (continuationExpected wordType (valueContinuationLhs inputs code) sourceBody) = some result := by
  have liftedTarget : CastTyping env 0 (Arithmetic.SourceCasts env) (wordType::ctx) code.lift cmdType := by
    simpa only [cmdType,VExpr.lift,VExpr.liftN] using
      targetTyped.lift closed Arithmetic.SourceCasts.closed wordType
  have evaluation := eval_cast_typed (inputs.nextWord closed wordDeclared consDeclared) evalDeclared liftedTarget
  have prefixTyped := CastTyping.application
    ((equality_head_typed (ctx := wordType::ctx) stateDeclared optionDeclared eqDeclared).withCasts (Arithmetic.SourceCasts env))
    evaluation
  simp only [WordFrontend.optionState,stateType,VExpr.inst,InputsTyped.nextWord,InputsTyped.lift] at prefixTyped
  have wordTyped : DirectTyping env 0 ctx wordType (.sort (.succ .zero)) :=
    .constant wordDeclared (by simp) rfl
  exact continuation_beta_conversion setup signatures closed wordTyped (by trivial)
    setup.basic_word_refl_none prefixTyped sourceTyped sourceForm eqFresh

/-- Conversions in generated certificates are specified by their syntax and
ordinary source typing. This relation does not contain successful checker
executions as constructors. -/
inductive ProofCasts (setup : Arithmetic.AliasSetup env) : TypeCasts where
  | source : (Arithmetic.SourceCasts env) ctx actual expected → ProofCasts setup ctx actual expected
  | stateContinuation (inputs : InputsTyped env ctx p)
      {code sourceBody : VExpr}
      (target : CastTyping env 0 (Arithmetic.SourceCasts env) ctx code cmdType)
      (source : CastTyping env 0 (Arithmetic.SourceCasts env) (stateType::ctx) sourceBody (optionType stateType))
      (form : Arithmetic.ValueForm setup (stateType::ctx) sourceBody (optionType stateType)) :
      ProofCasts setup ctx (sequenceNextActual inputs code sourceBody)
        (sequenceContinuationType inputs code (.lam stateType sourceBody))

  | valueContinuation (inputs : InputsTyped env ctx p)
      {code sourceBody : VExpr}
      (target : CastTyping env 0 (Arithmetic.SourceCasts env) ctx code cmdType)
      (source : CastTyping env 0 (Arithmetic.SourceCasts env) (wordType::ctx) sourceBody (optionType stateType))
      (form : Arithmetic.ValueForm setup (wordType::ctx) sourceBody (optionType stateType)) :
      ProofCasts setup ctx
        (continuationActual wordType (valueContinuationLhs inputs code) sourceBody)
        (continuationExpected wordType (valueContinuationLhs inputs code) sourceBody)

instance : Arithmetic.Includes (ProofCasts setup) := ⟨fun _ _ _ h => .source (.arithmetic h)⟩

theorem ProofCasts.covered (setup : Arithmetic.AliasSetup env)
    (signatures : Arithmetic.Signatures env) (closed : ClosedConstantTypes env)
    (wordDeclared : env.constants ``HybridWord.Word = some ⟨0,.sort (.succ .zero)⟩)
    (consDeclared : env.constants ``List.cons = some consSignature)
    (stateDeclared : env.constants ``HybridWord.State = some ⟨0,.sort (.succ .zero)⟩)
    (optionDeclared : env.constants ``Option = some optionSignature)
    (eqDeclared : env.constants ``Eq = some eqSignature)
    (evalDeclared : env.constants ``HybridWord.Cmd.eval = some ⟨0,evalSignature⟩)
    (stateFresh : ∀ r ∈ setup.rules, ``HybridWord.State ≠ r.name)
    (eqFresh : ∀ r ∈ setup.rules, ``Eq ≠ r.name) :
    Conversion.Covers setup.conversion 0 (ProofCasts setup) := by
  intro ctx actual expected cast
  cases cast with
  | source cast => exact setup.covers_source signatures closed ctx actual expected cast
  | stateContinuation inputs target source form =>
    exact sequence_beta_conversion setup signatures inputs closed target source
      stateDeclared optionDeclared eqDeclared evalDeclared form stateFresh eqFresh
  | valueContinuation inputs target source form =>
    exact value_beta_conversion setup signatures inputs closed target source
      wordDeclared consDeclared stateDeclared optionDeclared eqDeclared evalDeclared form eqFresh

end IRComparison.WordFrontend.Certificate
