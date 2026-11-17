import IRComparison.Frontend.WordForCompleteness

/-! Fixed Lean declarations used by the signed-range frontend. These lemmas
discharge library typing premises of the loop composition theorem. -/
namespace IRComparison.WordFrontend.Certificate.For
open Lean4Lean LeanTyped LeanTypeInference
set_option maxHeartbeats 1000000

def intOfNatSignature : VExpr := .forallE (.const ``Nat [])
  (applications (.const ``OfNat [.zero]) [intType,.bvar 0])
def negSignature : VConstant := ⟨1,.forallE (.sort (.succ (.param 0)))
  (.forallE (.app (.const ``Neg [.param 0]) (.bvar 0)) (.forallE (.bvar 1) (.bvar 2)))⟩
def intNegSignature : VExpr := .app (.const ``Neg [.zero]) intType

def integerInstance : Arithmetic.Binary → Lean.Name
  | .add => ``Int.instAdd | .sub => ``Int.instSub | .mul => ``Int.instMul | .div => ``Int.instDiv

def integerBinarySignature (op : Arithmetic.Binary) : VExpr :=
  .app (.const op.className [.zero]) intType

def nativeBinaryHeader (op : Arithmetic.Binary) : Lean.Expr :=
  Lean.mkApp4 (.const op.method [.zero,.zero,.zero]) (.const ``Int []) (.const ``Int []) (.const ``Int [])
    (Lean.mkApp2 (.const op.liftedInstance [.zero]) (.const ``Int []) (.const (integerInstance op) []))
def binaryHeader (op : Arithmetic.Binary) : VExpr :=
  applications (.const op.method [.zero,.zero,.zero]) [intType,intType,intType,
    applications (.const op.liftedInstance [.zero]) [intType,.const (integerInstance op) []]]
def nativeBinary (op : Arithmetic.Binary) (a b : Lean.Expr) : Lean.Expr := Lean.mkApp2 (nativeBinaryHeader op) a b
def binaryValue : Arithmetic.Binary → Int → Int → Int
  | .add => (· + ·) | .sub => (· - ·) | .mul => (· * ·) | .div => (· / ·)

structure BoundSignatures (env : VEnv) : Prop where
  natural : NatSignatures env
  integer : env.constants ``Int = some ⟨0,.sort (.succ .zero)⟩
  ofNat : env.constants ``OfNat.ofNat = some Arithmetic.ofNatSignature
  intOfNat : env.constants ``instOfNat = some ⟨0,intOfNatSignature⟩
  negate : env.constants ``Neg.neg = some negSignature
  intNeg : env.constants ``Int.instNegInt = some ⟨0,intNegSignature⟩
  intBinary : ∀ op, env.constants (integerInstance op) = some ⟨0,integerBinarySignature op⟩

def nativeNatural (n : Nat) : Lean.Expr := Lean.mkApp3 (.const ``OfNat.ofNat [.zero])
  (.const ``Int []) (.lit (.natVal n)) (Lean.mkApp (.const ``instOfNat []) (.lit (.natVal n)))
def naturalTerm (n : Nat) : VExpr := applications (.const ``OfNat.ofNat [.zero])
  [intType,numeral n,.app (.const ``instOfNat []) (numeral n)]
def nativeNegative (e : Lean.Expr) : Lean.Expr := Lean.mkApp3 (.const ``Neg.neg [.zero])
  (.const ``Int []) (.const ``Int.instNegInt []) e
def negativeTerm (e : VExpr) : VExpr := applications (.const ``Neg.neg [.zero]) [intType,.const ``Int.instNegInt [],e]

theorem natural_represents (n : Nat) : Represents (nativeNatural n) (naturalTerm n) :=
  .app (.app (.app (.constant rfl) (.constant rfl)) .natural) (.app (.constant rfl) .natural)

theorem negative_represents (value : Represents e ec) : Represents (nativeNegative e) (negativeTerm ec) :=
  .app (.app (.app (.constant rfl) (.constant rfl)) (.constant rfl)) value

theorem BoundSignatures.natural_typed (signatures : BoundSignatures env) (n : Nat) :
    DirectTyping env 0 ctx (naturalTerm n) intType := by
  have intTyped : DirectTyping env 0 ctx intType (.sort (.succ .zero)) :=
    .constant signatures.integer (by simp) rfl
  have natTyped := signatures.natural.numeral_typed (ctx := ctx) (U := 0) n
  have method : DirectTyping env 0 ctx (.const ``OfNat.ofNat [.zero])
      (Arithmetic.ofNatSignature.type.instL [.zero]) := .constant signatures.ofNat (by simp [VLevel.WF]) rfl
  have a1 := DirectTyping.application method intTyped
  simp only [Arithmetic.ofNatSignature,Arithmetic.natType,intType,applications,VExpr.instL,VLevel.inst,
    VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower,VExpr.lift,VExpr.liftN,Nat.reduceAdd,List.map_nil] at a1
  have a2 := DirectTyping.application a1 natTyped
  simp only [VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower,VExpr.lift,VExpr.liftN,Nat.reduceAdd] at a2
  have instanceTyped : DirectTyping env 0 ctx (.const ``instOfNat []) intOfNatSignature :=
    .constant signatures.intOfNat (by simp) rfl
  have dictionary := DirectTyping.application instanceTyped natTyped
  simp only [intOfNatSignature,intType,applications,VExpr.inst,VExpr.instVar_zero] at dictionary
  exact .application a2 dictionary

theorem BoundSignatures.negative_typed (signatures : BoundSignatures env)
    (value : CastTyping env 0 Arithmetic.Casts ctx e intType) : CastTyping env 0 Arithmetic.Casts ctx (negativeTerm e) intType := by
  have intTyped : DirectTyping env 0 ctx intType (.sort (.succ .zero)) :=
    .constant signatures.integer (by simp) rfl
  have method : DirectTyping env 0 ctx (.const ``Neg.neg [.zero]) (negSignature.type.instL [.zero]) :=
    .constant signatures.negate (by simp [VLevel.WF]) rfl
  have a1 := DirectTyping.application method intTyped
  simp only [negSignature,intType,VExpr.instL,VLevel.inst,VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,
    VExpr.instVar_lower,VExpr.lift,VExpr.liftN,Nat.reduceAdd,List.map_nil] at a1
  have instanceTyped : DirectTyping env 0 ctx (.const ``Int.instNegInt []) intNegSignature :=
    .constant signatures.intNeg (by simp) rfl
  have a2 := DirectTyping.application a1 instanceTyped
  simp only [intType,VExpr.inst] at a2
  exact .application (a2.withCasts Arithmetic.Casts) value

def Bound.natural (signatures : BoundSignatures env) (n : Nat) : Bound env ctx (nativeNatural n) :=
  ⟨⟨naturalTerm n,natural_represents n⟩,(signatures.natural_typed n).withCasts Arithmetic.Casts,rfl⟩

def Bound.negative (signatures : BoundSignatures env) (value : Bound env ctx e) : Bound env ctx (nativeNegative e) :=
  ⟨⟨negativeTerm value.represented.val,negative_represents value.represented.property⟩,
    signatures.negative_typed value.typed,by
      change (true && isClosed e) = true
      simp only [Bool.true_and,value.closed]⟩

theorem binary_represents (op : Arithmetic.Binary) (left : Represents a ac) (right : Represents b bc) :
    Represents (nativeBinary op a b) (.app (.app (binaryHeader op) ac) bc) :=
  .app (.app (.app (.app (.app (.app (.constant rfl) (.constant rfl)) (.constant rfl)) (.constant rfl))
    (.app (.app (.constant rfl) (.constant rfl)) (.constant rfl))) left) right

theorem BoundSignatures.binary_header_typed (library : BoundSignatures env)
    (arithmetic : Arithmetic.Signatures env) (op : Arithmetic.Binary) :
    CastTyping env 0 Arithmetic.Casts ctx (binaryHeader op) (.forallE intType (.forallE intType intType)) := by
  have integer : CastTyping env 0 Arithmetic.Casts ctx intType (.sort (.succ .zero)) :=
    .constant library.integer (by simp) rfl
  have inst : CastTyping env 0 Arithmetic.Casts ctx (.const (integerInstance op) []) (integerBinarySignature op) :=
    .constant (library.intBinary op) (by simp) rfl
  have liftTyped : CastTyping env 0 Arithmetic.Casts ctx (.const op.liftedInstance [.zero])
      (.forallE (.sort (.succ .zero)) (.forallE (.app (.const op.className [.zero]) (.bvar 0))
        (applications (.const op.heterogeneous [.zero,.zero,.zero]) [.bvar 1,.bvar 1,.bvar 1]))) :=
    .constant (arithmetic.lifted op) (by simp [VLevel.WF]) rfl
  have d1 := CastTyping.application liftTyped integer
  simp only [intType,applications,VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower,
    VExpr.lift,VExpr.liftN,Nat.reduceAdd] at d1
  have dictionary := CastTyping.application d1 inst
  simp only [intType,applications,VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower,
    VExpr.lift,VExpr.liftN,Nat.reduceAdd] at dictionary
  have method : CastTyping env 0 Arithmetic.Casts ctx (.const op.method [.zero,.zero,.zero])
      (.forallE (.sort (.succ .zero)) (.forallE (.sort (.succ .zero))
        (.forallE Arithmetic.resultParameter (.forallE
          (applications (.const op.heterogeneous [.zero,.zero,.zero]) [.bvar 2,.bvar 1,.bvar 0])
          (.forallE (.bvar 3) (.forallE (.bvar 3) (.bvar 3))))))) :=
    .constant (arithmetic.methods op) (by simp [VLevel.WF]) rfl
  have a1 := CastTyping.application method integer
  simp only [Arithmetic.resultParameter,intType,applications,VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,
    VExpr.instVar_lower,VExpr.lift,VExpr.liftN,Nat.reduceAdd] at a1
  have a2 := CastTyping.application a1 integer
  simp only [VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower,VExpr.lift,VExpr.liftN,Nat.reduceAdd] at a2
  have a3 := CastTyping.convertedApplication a2 integer Arithmetic.Casts.resultType
  simp only [VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower,VExpr.lift,VExpr.liftN,Nat.reduceAdd] at a3
  exact .application a3 dictionary

def Bound.binary (library : BoundSignatures env) (arithmetic : Arithmetic.Signatures env)
    (op : Arithmetic.Binary) (left : Bound env ctx a) (right : Bound env ctx b) : Bound env ctx (nativeBinary op a b) := by
  refine ⟨⟨_,binary_represents op left.represented.property right.represented.property⟩,?_,?_⟩
  · have first := CastTyping.application (library.binary_header_typed arithmetic op) left.typed
    simp only [intType,VExpr.inst] at first
    exact .application first right.typed
  · change ((true && isClosed a) && isClosed b) = true
    simp only [left.closed,right.closed,Bool.and_self]

namespace Header
open Arithmetic (SourceCasts)

def forInSignature : VConstant := ⟨4, (.forallE (.forallE (.sort (.succ (.param 2)))
 (.sort (.succ (.param 3))))
 (.forallE (.sort (.succ (.param 0)))
 (.forallE (.app (.const ``outParam [(.succ (.succ (.param 1)))]) (.sort (.succ (.param 1))))
 (.forallE (.app (.app (.app (.const ``ForIn [(.param 0),(.param 1),(.param 2),(.param 3)]) (.bvar 2)) (.bvar 1)) (.bvar 0))
 (.forallE (.sort (.succ (.param 2)))
 (.forallE (.bvar 3)
 (.forallE (.bvar 1)
 (.forallE (.forallE (.bvar 4)
 (.forallE (.bvar 3)
 (.app (.bvar 8) (.app (.const ``ForInStep [(.param 2)]) (.bvar 4)))))
 (.app (.bvar 7) (.bvar 3))))))))))⟩
def forInInstanceSignature : VConstant := ⟨4, (.forallE (.forallE (.sort (.succ (.param 0)))
 (.sort (.succ (.param 1))))
 (.forallE (.sort (.succ (.param 2)))
 (.forallE (.sort (.succ (.param 3)))
 (.forallE (.app (.app (.const ``Membership [(.param 3),(.param 2)]) (.bvar 0)) (.bvar 1))
 (.forallE (.app (.app (.app (.app (.const ``ForIn' [(.param 2),(.param 3),(.param 0),(.param 1)]) (.bvar 3)) (.bvar 2)) (.bvar 1)) (.bvar 0))
 (.app (.app (.app (.const ``ForIn [(.param 2),(.param 3),(.param 0),(.param 1)]) (.bvar 4)) (.bvar 3)) (.bvar 2)))))))⟩
def inferInstanceSignature : VConstant := ⟨1, (.forallE (.sort (.param 0))
 (.forallE (.bvar 0)
 (.bvar 1)))⟩
def membershipInstanceSignature : VConstant := ⟨1, (.forallE (.sort (.succ (.param 0)))
 (.app (.app (.const ``Membership [(.param 0),(.param 0)]) (.bvar 0)) (.app (.const ``List [(.param 0)]) (.bvar 0))))⟩
def listInstanceSignature : VConstant := ⟨3, (.forallE (.forallE (.sort (.succ (.param 0)))
 (.sort (.succ (.param 1))))
 (.forallE (.sort (.succ (.param 2)))
 (.forallE (.app (.const ``Monad [(.param 0),(.param 1)]) (.bvar 1))
 (.app (.app (.app (.app (.const ``ForIn' [(.param 2),(.param 2),(.param 0),(.param 1)]) (.bvar 2)) (.app (.const ``List [(.param 2)]) (.bvar 1))) (.bvar 1)) (.app (.app (.const ``inferInstance [(.succ (.param 2))]) (.app (.app (.const ``Membership [(.param 2),(.param 2)]) (.bvar 1)) (.app (.const ``List [(.param 2)]) (.bvar 1)))) (.app (.const ``List.instMembership [(.param 2)]) (.bvar 1)))))))⟩
def listSignature : VConstant := ⟨1, (.forallE (.sort (.succ (.param 0)))
 (.sort (.succ (.param 0))))⟩
def membershipSignature : VConstant := ⟨2, (.forallE (.app (.const ``outParam [(.succ (.succ (.param 0)))]) (.sort (.succ (.param 0))))
 (.forallE (.sort (.succ (.param 1)))
 (.sort (.max (.succ (.param 0)) (.succ (.param 1))))))⟩

structure Signatures (env : VEnv) : Prop where
  word : env.constants ``HybridWord.Word = some ⟨0,.sort (.succ .zero)⟩
  state : env.constants ``HybridWord.State = some ⟨0,.sort (.succ .zero)⟩
  option : env.constants ``Option = some optionSignature
  monad : env.constants ``instMonadOption = some optionMonadSignature
  forIn : env.constants ``ForIn.forIn = some forInSignature
  forInInstance : env.constants ``instForInOfForIn' = some forInInstanceSignature
  inferInstanceDecl : env.constants ``inferInstance = some inferInstanceSignature
  membershipInstance : env.constants ``List.instMembership = some membershipInstanceSignature
  listInstance : env.constants ``List.instForIn'InferInstanceMembershipOfMonad = some listInstanceSignature
  list : env.constants ``List = some listSignature
  membership : env.constants ``Membership = some membershipSignature

def membershipType : VExpr := applications (.const ``Membership [.zero,.zero]) [wordType,wordsType]
def membershipValue : VExpr := applications (.const ``inferInstance [.succ .zero])
  [membershipType,.app (.const ``List.instMembership [.zero]) wordType]
def listValue : VExpr := applications (.const ``List.instForIn'InferInstanceMembershipOfMonad [.zero,.zero,.zero])
  [.const ``Option [.zero],wordType,.const ``instMonadOption [.zero]]
def forInValue : VExpr := applications (.const ``instForInOfForIn' [.zero,.zero,.zero,.zero])
  [.const ``Option [.zero],wordsType,wordType,membershipValue,listValue]

theorem Signatures.word_typed (s : Signatures env) : DirectTyping env 0 ctx wordType (.sort (.succ .zero)) :=
  .constant s.word (by simp) rfl

theorem Signatures.option_typed (s : Signatures env) :
    DirectTyping env 0 ctx (.const ``Option [.zero]) (.forallE (.sort (.succ .zero)) (.sort (.succ .zero))) :=
  .constant s.option (by simp [VLevel.WF]) rfl

namespace At

/-- The same native List iterator dictionary serves signed-range Word
counters and natural counters. The element type is an existing declaration. -/
def listType (name : Lean.Name) : VExpr := .app (.const ``List [.zero]) (.const name [])
def membershipType (name : Lean.Name) : VExpr :=
  applications (.const ``Membership [.zero,.zero]) [.const name [],listType name]
def membershipValue (name : Lean.Name) : VExpr := applications (.const ``inferInstance [.succ .zero])
  [membershipType name,.app (.const ``List.instMembership [.zero]) (.const name [])]
def listValue (name : Lean.Name) : VExpr :=
  applications (.const ``List.instForIn'InferInstanceMembershipOfMonad [.zero,.zero,.zero])
    [.const ``Option [.zero],.const name [],.const ``instMonadOption [.zero]]
def forInValue (name : Lean.Name) : VExpr :=
  applications (.const ``instForInOfForIn' [.zero,.zero,.zero,.zero])
    [.const ``Option [.zero],listType name,.const name [],membershipValue name,listValue name]
def functionType (name : Lean.Name) : VExpr :=
  .forallE (.const name []) (.forallE stateType (optionType Step.stepState))
def headerType (name : Lean.Name) : VExpr :=
  .forallE (listType name) (.forallE stateType (.forallE (functionType name) (optionType stateType)))
def header (name : Lean.Name) : VExpr := applications (.const ``ForIn.forIn [.zero,.zero,.zero,.zero])
  [.const ``Option [.zero],listType name,.const name [],forInValue name,stateType]

def nativeHeader (name : Lean.Name) : Lean.Expr := Lean.mkApp5 (.const ``ForIn.forIn [.zero,.zero,.zero,.zero])
  (.const ``Option [.zero]) (Lean.mkApp (.const ``List [.zero]) (.const name [])) (.const name [])
  (Lean.mkApp5 (.const ``instForInOfForIn' [.zero,.zero,.zero,.zero])
    (.const ``Option [.zero]) (Lean.mkApp (.const ``List [.zero]) (.const name [])) (.const name [])
    (Lean.mkApp2 (.const ``inferInstance [.succ .zero])
      (Lean.mkApp2 (.const ``Membership [.zero,.zero]) (.const name []) (Lean.mkApp (.const ``List [.zero]) (.const name [])))
      (Lean.mkApp (.const ``List.instMembership [.zero]) (.const name [])))
    (Lean.mkApp3 (.const ``List.instForIn'InferInstanceMembershipOfMonad [.zero,.zero,.zero])
      (.const ``Option [.zero]) (.const name []) (.const ``instMonadOption [.zero]))) state

theorem header_represents (name : Lean.Name) : Represents (nativeHeader name) (header name) := by
  repeat first | apply Represents.app | exact Represents.constant rfl

theorem element_typed (declared : env.constants name = some ⟨0,.sort (.succ .zero)⟩) :
    DirectTyping env 0 ctx (.const name []) (.sort (.succ .zero)) :=
  .constant declared (by simp) rfl

theorem words_typed (s : Signatures env) (name : Lean.Name)
    (elementDeclared : env.constants name = some ⟨0,.sort (.succ .zero)⟩) : DirectTyping env 0 ctx (listType name) (.sort (.succ .zero)) :=
  .application (.constant s.list (by simp [VLevel.WF]) rfl) (element_typed elementDeclared)

theorem membership_type (s : Signatures env) (name : Lean.Name)
    (elementDeclared : env.constants name = some ⟨0,.sort (.succ .zero)⟩) :
    CastTyping env 0 (SourceCasts env) ctx (membershipType name) (.sort (.max (.succ .zero) (.succ .zero))) := by
  have fact : CastTyping env 0 (SourceCasts env) ctx (.const ``Membership [.zero,.zero])
      (membershipSignature.type.instL [.zero,.zero]) := .constant s.membership (by simp [VLevel.WF]) rfl
  have a1 := CastTyping.convertedApplication fact ((element_typed elementDeclared).withCasts (SourceCasts env))
    (SourceCasts.arithmetic Arithmetic.Casts.resultType)
  simpa only [membershipSignature,membershipType,VExpr.instL,VLevel.inst,VExpr.inst,
    List.map_nil,Nat.reduceAdd,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower] using
    CastTyping.application a1 ((words_typed s name elementDeclared).withCasts (SourceCasts env))

theorem membership_value (s : Signatures env) (name : Lean.Name)
    (elementDeclared : env.constants name = some ⟨0,.sort (.succ .zero)⟩) :
    CastTyping env 0 (SourceCasts env) ctx (membershipValue name) (membershipType name) := by
  have instanceTyped : DirectTyping env 0 ctx (.const ``List.instMembership [.zero])
      (membershipInstanceSignature.type.instL [.zero]) := .constant s.membershipInstance (by simp [VLevel.WF]) rfl
  have dictionary := DirectTyping.application instanceTyped (element_typed elementDeclared)
  simp only [membershipInstanceSignature,VExpr.instL,VLevel.inst,VExpr.inst,
    VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower,List.map_nil,Nat.reduceAdd] at dictionary
  have inferTyped : CastTyping env 0 (SourceCasts env) ctx (.const ``inferInstance [.succ .zero])
      (inferInstanceSignature.type.instL [.succ .zero]) := .constant s.inferInstanceDecl (by simp [VLevel.WF]) rfl
  have a1 := CastTyping.convertedApplication inferTyped (membership_type s name elementDeclared)
    (SourceCasts.levelEquality (actual := .max (.succ .zero) (.succ .zero)) (expected := .succ .zero)
      (by trivial) (by trivial) rfl)
  simp only [inferInstanceSignature,VExpr.instL,VLevel.inst,VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,
    VExpr.instVar_lower,List.map_nil,Nat.reduceAdd,membershipType,applications,listType,VExpr.lift,VExpr.liftN] at a1
  simpa only [membershipValue,membershipType,applications,listType,VExpr.inst] using
    CastTyping.application a1 (dictionary.withCasts (SourceCasts env))

theorem list_value (s : Signatures env) (name : Lean.Name)
    (elementDeclared : env.constants name = some ⟨0,.sort (.succ .zero)⟩) :
    CastTyping env 0 (SourceCasts env) ctx (listValue name)
      (applications (.const ``ForIn' [.zero,.zero,.zero,.zero])
        [.const ``Option [.zero],(listType name),(.const name []),(membershipValue name)]) := by
  have fact : CastTyping env 0 (SourceCasts env) ctx
      (.const ``List.instForIn'InferInstanceMembershipOfMonad [.zero,.zero,.zero])
      (listInstanceSignature.type.instL [.zero,.zero,.zero]) := .constant s.listInstance (by simp [VLevel.WF]) rfl
  have a1 := CastTyping.application fact (s.option_typed.withCasts (SourceCasts env))
  simp only [listInstanceSignature,VExpr.instL,VLevel.inst,VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,
    VExpr.instVar_lower,List.map_nil,Nat.reduceAdd] at a1
  have a2 := CastTyping.application a1 ((element_typed elementDeclared).withCasts (SourceCasts env))
  simp only [VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower,Nat.reduceAdd] at a2
  have monad : CastTyping env 0 (SourceCasts env) ctx (.const ``instMonadOption [.zero])
      (optionMonadSignature.type.instL [.zero]) := .constant s.monad (by simp [VLevel.WF]) rfl
  simpa only [listValue,membershipValue,membershipType,applications,listType,VExpr.inst,
    VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower,Nat.reduceAdd] using CastTyping.application a2 monad

theorem forIn_value (s : Signatures env) (name : Lean.Name)
    (elementDeclared : env.constants name = some ⟨0,.sort (.succ .zero)⟩) :
    CastTyping env 0 (SourceCasts env) ctx (forInValue name)
      (applications (.const ``ForIn [.zero,.zero,.zero,.zero]) [.const ``Option [.zero],(listType name),(.const name [])]) := by
  have fact : CastTyping env 0 (SourceCasts env) ctx (.const ``instForInOfForIn' [.zero,.zero,.zero,.zero])
      (forInInstanceSignature.type.instL [.zero,.zero,.zero,.zero]) := .constant s.forInInstance (by simp [VLevel.WF]) rfl
  have a1 := CastTyping.application fact (s.option_typed.withCasts (SourceCasts env))
  simp only [forInInstanceSignature,VExpr.instL,VLevel.inst,VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,
    VExpr.instVar_lower,List.map_nil,Nat.reduceAdd] at a1
  have a2 := CastTyping.application a1 ((words_typed s name elementDeclared).withCasts (SourceCasts env))
  simp only [VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower,Nat.reduceAdd,listType] at a2
  have a3 := CastTyping.application a2 ((element_typed elementDeclared).withCasts (SourceCasts env))
  simp only [VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower,Nat.reduceAdd] at a3
  have a4 := CastTyping.application a3 (membership_value s name elementDeclared)
  simp only [VExpr.inst] at a4
  simpa only [forInValue,applications,listType,VExpr.inst] using CastTyping.application a4 (list_value s name elementDeclared)

theorem header_typed (s : Signatures env) (name : Lean.Name)
    (elementDeclared : env.constants name = some ⟨0,.sort (.succ .zero)⟩) :
    CastTyping env 0 (SourceCasts env) ctx (header name) (headerType name) := by
  have fact : CastTyping env 0 (SourceCasts env) ctx (.const ``ForIn.forIn [.zero,.zero,.zero,.zero])
      (forInSignature.type.instL [.zero,.zero,.zero,.zero]) := .constant s.forIn (by simp [VLevel.WF]) rfl
  have a1 := CastTyping.application fact (s.option_typed.withCasts (SourceCasts env))
  simp only [forInSignature,VExpr.instL,VLevel.inst,VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,
    VExpr.instVar_lower,List.map_nil,Nat.reduceAdd] at a1
  have a2 := CastTyping.application a1 ((words_typed s name elementDeclared).withCasts (SourceCasts env))
  simp only [VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower,Nat.reduceAdd,listType] at a2
  have a3 := CastTyping.convertedApplication a2 ((element_typed elementDeclared).withCasts (SourceCasts env))
    (SourceCasts.arithmetic Arithmetic.Casts.resultType)
  simp only [VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower,Nat.reduceAdd] at a3
  have a4 := CastTyping.application a3 (forIn_value s name elementDeclared)
  simp only [VExpr.inst] at a4
  have stateTyped : CastTyping env 0 (SourceCasts env) ctx stateType (.sort (.succ .zero)) :=
    .constant s.state (by simp) rfl
  simpa only [header,headerType,functionType,Step.stepState,optionType,listType,stateType,
    applications,forInValue,listValue,membershipValue,membershipType,VExpr.inst,
    VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower,Nat.reduceAdd] using CastTyping.application a4 stateTyped

end At

theorem Signatures.words_typed (s : Signatures env) : DirectTyping env 0 ctx wordsType (.sort (.succ .zero)) :=
  At.words_typed s ``HybridWord.Word s.word

theorem Signatures.membership_type (s : Signatures env) :
    CastTyping env 0 (SourceCasts env) ctx membershipType (.sort (.max (.succ .zero) (.succ .zero))) :=
  At.membership_type s ``HybridWord.Word s.word

theorem Signatures.membership_value (s : Signatures env) :
    CastTyping env 0 (SourceCasts env) ctx membershipValue membershipType :=
  At.membership_value s ``HybridWord.Word s.word

theorem Signatures.list_value (s : Signatures env) :
    CastTyping env 0 (SourceCasts env) ctx listValue
      (applications (.const ``ForIn' [.zero,.zero,.zero,.zero])
        [.const ``Option [.zero],wordsType,wordType,membershipValue]) :=
  At.list_value s ``HybridWord.Word s.word

theorem Signatures.forIn_value (s : Signatures env) :
    CastTyping env 0 (SourceCasts env) ctx forInValue
      (applications (.const ``ForIn [.zero,.zero,.zero,.zero]) [.const ``Option [.zero],wordsType,wordType]) :=
  At.forIn_value s ``HybridWord.Word s.word

theorem Signatures.header_typed (s : Signatures env) :
    CastTyping env 0 (SourceCasts env) ctx header headerType :=
  At.header_typed s ``HybridWord.Word s.word

end Header

end IRComparison.WordFrontend.Certificate.For
