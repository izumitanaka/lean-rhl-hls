import IRComparison.Frontend.WordReadCompleteness
import IRComparison.Frontend.WordBinder

/-! The element type argument of GetElem? can be BitVec 32 while the
collection and its instance retain Word. This is emitted by ordinary Lean
elaboration of an explicitly annotated do-read. -/
namespace IRComparison.WordFrontend.Read
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic
set_option maxHeartbeats 1600000

def dictionaryPrefix : VExpr := applications (.const ``GetElem? [.zero,.zero,.zero])
  [arrayType,natType]

def Signatures.annotationDictionary (signatures : Signatures env) : ReadDictionary env where
  function := dictionaryPrefix
  domain := predicateType
  predicate := validity
  kind := predicateKind
  resultKind := .max (.max (.succ .zero) (.succ .zero)) (.succ .zero)
  annotation := predicateAnnotation
  annotationClosed := by trivial
  sameKind := rfl
  levels := [.zero,.zero,.zero]
  head := rfl
  prefixTyped := by
    have getter : DirectTyping env 0 [] (.const ``GetElem? [.zero,.zero,.zero])
        (getClassSignature.type.instL [.zero,.zero,.zero]) :=
      .constant signatures.getClass (by simp [VLevel.WF]) rfl
    have first := DirectTyping.application getter signatures.array_typed
    simp only [getClassSignature,applications,VExpr.instL,VLevel.inst,VExpr.inst,VExpr.instVar_lower,
      VExpr.instVar_zero,VExpr.instVar_succ,arrayType,wordType,VExpr.lift,VExpr.liftN] at first
    have second := DirectTyping.application first signatures.natural_typed
    simpa only [dictionaryPrefix,resultParameter,predicateAnnotation,predicateType,arrayType,wordType,natType,
      applications,VExpr.inst,VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.lift,VExpr.liftN] using second
  domainTyped := signatures.predicate_typed
  predicateTyped := signatures.validity_typed
  predicateLambda := ⟨_,_,rfl⟩
  domainClosed := by trivial
  kindClosed := by trivial
  resultClosed := by trivial

def bitsHeader : VExpr := applications (.const ``GetElem?.getElem? [.zero,.zero,.zero])
  [arrayType,natType,bitvecType,validity,.app (.const ``Array.instGetElem?NatLtSize [.zero]) wordType]

def nativeBitsHeader : Lean.Expr :=
  [nativeArray,.const ``Nat [],WordBinder.Annotation.bitvec.native,nativeValidity,
    .app (.const ``Array.instGetElem?NatLtSize [.zero]) word].foldl Lean.Expr.app
      (.const ``GetElem?.getElem? [.zero,.zero,.zero])

theorem Signatures.bits_header_typed (signatures : Signatures env) (arithmetic : Arithmetic.Signatures env) :
    CastTyping env 0 (Arithmetic.SourceCasts env) ctx bitsHeader
      (.forallE arrayType (.forallE natType (optionType bitvecType))) := by
  have getter : CastTyping env 0 (Arithmetic.SourceCasts env) ctx
      (.const ``GetElem?.getElem? [.zero,.zero,.zero]) (getSignature.type.instL [.zero,.zero,.zero]) :=
    .constant signatures.getter (by simp [VLevel.WF]) rfl
  have a1 := CastTyping.application getter (signatures.array_typed.withCasts _)
  simp only [getSignature,applications,VExpr.instL,VLevel.inst,VExpr.inst,VExpr.instVar_lower,
    VExpr.instVar_zero,VExpr.instVar_succ,arrayType,wordType,VExpr.lift,VExpr.liftN] at a1
  have a2 := CastTyping.application a1 (signatures.natural_typed.withCasts _)
  simp only [VExpr.inst,VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] at a2
  have a3 := CastTyping.convertedApplication a2 (arithmetic.bitvec_typed.withCasts _) (.arithmetic .resultType)
  have bitsClosed : bitvecType.ClosedN 0 := ⟨by trivial,width_closed⟩
  simp only [VExpr.inst,VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ,
    bitsClosed.liftN_eq (Nat.zero_le _),wordType,VExpr.lift,VExpr.liftN] at a3
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
  have applied := CastTyping.convertedApplication a4 (dictionary.withCasts _) (by
    simpa only [Signatures.annotationDictionary,dictionaryPrefix,predicateType,arrayType,validity,wordType,natType,
      applications,List.map_cons,List.map_nil,VLevel.inst,VExpr.inst,VExpr.instVar_lower,VExpr.instVar_zero,
      VExpr.instVar_succ,liftVar,Nat.reduceAdd,Nat.reduceLT,ite_true,ite_false,VExpr.lift,VExpr.liftN,
      bitsClosed.instN_eq (Nat.zero_le _),bitsClosed.liftN_eq (Nat.zero_le _)] using
      (SourceCasts.readDictionary (ctx := ctx) signatures.annotationDictionary))
  have bvLift (n k : Nat) : bitvecType.liftN n k = bitvecType := bitsClosed.liftN_eq (Nat.zero_le k)
  have bvInst (v : VExpr) (k : Nat) : bitvecType.inst v k = bitvecType := bitsClosed.instN_eq (Nat.zero_le k)
  simpa only [bitsHeader,applications,optionType,arrayType,validity,wordType,natType,VExpr.inst,
    bvLift,bvInst,VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ,
    VExpr.lift,VExpr.liftN,liftVar,Nat.reduceAdd,Nat.reduceLT,ite_true,ite_false,List.map_cons,List.map_nil,VLevel.inst] using applied

theorem bitsHeader_represents : Represents nativeBitsHeader bitsHeader := by
  apply app_represents (.constant rfl)
  refine .cons (.app (.constant rfl) (.constant rfl)) (.cons (.constant rfl)
    (.cons WordBinder.Annotation.bitvec.represented (.cons ?_ (.cons (.app (.constant rfl) (.constant rfl)) .nil))))
  refine .lam (.app (.constant rfl) (.constant rfl)) (.lam (.constant rfl) ?_)
  exact app_represents (.constant rfl) (.cons (.constant rfl) (.cons (.constant rfl)
    (.cons .bvar (.cons (.app (.app (.constant rfl) (.constant rfl)) .bvar) .nil))))

def bitsSource (s a n : Lean.Expr) : Lean.Expr :=
  Lean.mkApp2 nativeBitsHeader (app ``HybridWord.State.arrays [s,a]) n

theorem bitsSource_represents (stateRep : Represents s sc) (arrayRep : Represents a ac)
    (indexRep : Represents n nc) : Represents (bitsSource s a n)
      (.app (.app bitsHeader (applications (.const ``HybridWord.State.arrays []) [sc,ac])) nc) :=
  .app (.app bitsHeader_represents (.app (.app (.constant rfl) stateRep) arrayRep)) indexRep

theorem Signatures.bits_source_typed (signatures : Signatures env) (arithmetic : Arithmetic.Signatures env)
    (inputs : InputsTyped env ctx p) (array : NatArgument env ctx a)
    (indexTyped : CastTyping env 0 (SourceCasts env) ctx index natType) :
    CastTyping env 0 (SourceCasts env) ctx
      (.app (.app bitsHeader (applications (.const ``HybridWord.State.arrays []) [inputs.s.val,array.represented.val])) index)
      (optionType bitvecType) := by
  have first := CastTyping.application (signatures.bits_header_typed arithmetic)
    ((signatures.arrays_typed inputs array).withCasts _)
  have bvInst (v : VExpr) (k : Nat) : bitvecType.inst v k = bitvecType :=
    (WordBinder.Annotation.closed .bitvec).instN_eq (Nat.zero_le k)
  simp only [natType,optionType,VExpr.inst,bvInst] at first
  have applied := CastTyping.application first indexTyped
  simpa only [optionType,VExpr.inst,bvInst] using applied

end IRComparison.WordFrontend.Read
