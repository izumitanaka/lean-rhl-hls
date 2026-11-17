import IRComparison.Frontend.WordTraversalCompleteness
import IRComparison.Frontend.LeanCastTyping

/-! Fixed source types and their permitted alias conversions. These definitions
are shared by lexical environments and certificate construction; no parser or
new source-language semantics is introduced here. -/
namespace IRComparison.WordFrontend.Certificate
open Lean4Lean LeanTyped LeanTypeInference

def wordType : VExpr := .const ``HybridWord.Word []
def stateType : VExpr := .const ``HybridWord.State []
def wordsType : VExpr := .app (.const ``List [.zero]) wordType
def optionType (ty : VExpr) : VExpr := .app (.const ``Option [.zero]) ty
def someValue (ty v : VExpr) : VExpr := .app (.app (.const ``Option.some [.zero]) ty) v
def equalValues (ty lhs rhs : VExpr) : VExpr :=
  .app (.app (.app (.const ``Eq [.succ .zero]) ty) lhs) rhs
def scalarValue (i x y s ls code : VExpr) : VExpr :=
  applications (.const ``HybridWord.Expr.eval []) [i,x,y,s,ls,code]

end IRComparison.WordFrontend.Certificate

namespace IRComparison.WordFrontend.Arithmetic
open Lean4Lean LeanTyped LeanTypeInference Certificate

inductive Binary where
  | add | sub | mul | div
  deriving DecidableEq, Repr

def Binary.method : Binary → Lean.Name
  | .add => ``HAdd.hAdd | .sub => ``HSub.hSub | .mul => ``HMul.hMul | .div => ``HDiv.hDiv
def Binary.className : Binary → Lean.Name
  | .add => ``Add | .sub => ``Sub | .mul => ``Mul | .div => ``Div
def Binary.heterogeneous : Binary → Lean.Name
  | .add => ``HAdd | .sub => ``HSub | .mul => ``HMul | .div => ``HDiv
def Binary.instanceName : Binary → Lean.Name
  | .add => ``BitVec.instAdd | .sub => ``BitVec.instSub
  | .mul => ``BitVec.instMul | .div => ``BitVec.instDiv
def Binary.liftedInstance : Binary → Lean.Name
  | .add => ``instHAdd | .sub => ``instHSub | .mul => ``instHMul | .div => ``instHDiv
def Binary.target : Binary → Lean.Name
  | .add => ``HybridWord.Expr.add | .sub => ``HybridWord.Expr.sub
  | .mul => ``HybridWord.Expr.mul | .div => ``HybridWord.Expr.div
def Binary.fact : Binary → Lean.Name
  | .add => ``WordFrontendFacts.add | .sub => ``WordFrontendFacts.sub
  | .mul => ``WordFrontendFacts.mul | .div => ``WordFrontendFacts.div

def natType : VExpr := .const ``Nat []
def nativeWidth : Lean.Expr :=
  Lean.mkApp3 (.const ``OfNat.ofNat [.zero]) (.const ``Nat []) (.lit (.natVal 32))
    (app ``instOfNatNat [.lit (.natVal 32)])
def width : VExpr := applications (.const ``OfNat.ofNat [.zero])
  [natType,numeral 32,.app (.const ``instOfNatNat []) (numeral 32)]
def bitvecType : VExpr := .app (.const ``BitVec []) width
def resultParameter : VExpr := .app (.const ``outParam [.succ (.succ .zero)]) (.sort (.succ .zero))

theorem width_represents : Represents nativeWidth width :=
  .app (.app (.app (.constant rfl) (.constant rfl)) .natural) (.app (.constant rfl) .natural)
theorem width_closed : width.ClosedN 0 := width_represents.closed 0 rfl

def ofNatSignature : VConstant := ⟨1,.forallE (.sort (.succ (.param 0)))
  (.forallE natType (.forallE
    (applications (.const ``OfNat [.param 0]) [.bvar 1,.bvar 0]) (.bvar 2)))⟩
def natInstanceSignature : VExpr := .forallE natType
  (applications (.const ``OfNat [.zero]) [natType,.bvar 0])
def Binary.classSignature (_op : Binary) : VConstant :=
  ⟨1,.forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩
def Binary.instanceSignature (op : Binary) : VExpr := .forallE natType
  (.app (.const op.className [.zero]) (.app (.const ``BitVec []) (.bvar 0)))
def Binary.liftedSignature (op : Binary) : VConstant :=
  ⟨1,.forallE (.sort (.succ (.param 0)))
    (.forallE (.app (.const op.className [.param 0]) (.bvar 0))
      (applications (.const op.heterogeneous [.param 0,.param 0,.param 0]) [.bvar 1,.bvar 1,.bvar 1]))⟩
def Binary.methodSignature (op : Binary) : VConstant :=
  ⟨3,.forallE (.sort (.succ (.param 0))) (.forallE (.sort (.succ (.param 1)))
    (.forallE (.app (.const ``outParam [.succ (.succ (.param 2))]) (.sort (.succ (.param 2))))
      (.forallE (applications (.const op.heterogeneous [.param 0,.param 1,.param 2])
        [.bvar 2,.bvar 1,.bvar 0]) (.forallE (.bvar 3) (.forallE (.bvar 3) (.bvar 3))))))⟩

/-- The fixed heterogeneous class declaration used by all four arithmetic
operators. The three value type annotations may independently spell BV32. -/
def Binary.heterogeneousSignature (_op : Binary) : VConstant :=
  ⟨3,.forallE (.sort (.succ (.param 0))) (.forallE (.sort (.succ (.param 1)))
    (.forallE (.app (.const ``outParam [.succ (.succ (.param 2))]) (.sort (.succ (.param 2))))
      (.sort (.max (.max (.succ (.param 0)) (.succ (.param 1))) (.succ (.param 2))))))⟩

def Binary.classApplication (op : Binary) (a b c : VExpr) : VExpr :=
  applications (.const op.heterogeneous [.zero,.zero,.zero]) [a,b,c]

inductive WordSpelling : VExpr → Prop where
  | word : WordSpelling wordType
  | bitvec : WordSpelling bitvecType

theorem WordSpelling.closed (spelling : WordSpelling value) : value.ClosedN 0 := by
  cases spelling
  · trivial
  · exact ⟨by trivial,width_closed⟩

def ofNatClassSignature : VConstant := ⟨1,.forallE (.sort (.succ (.param 0)))
  (.forallE natType (.sort (.succ (.param 0))))⟩
def bitvecOfNatSignature : VExpr := .forallE natType (.forallE natType
  (applications (.const ``OfNat [.zero]) [.app (.const ``BitVec []) (.bvar 1),.bvar 0]))

def negClassSignature : VConstant := ⟨1,.forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩
def negInstanceSignature : VExpr := .forallE natType
  (.app (.const ``Neg [.zero]) (.app (.const ``BitVec []) (.bvar 0)))
def negMethodSignature : VConstant := ⟨1,.forallE (.sort (.succ (.param 0)))
  (.forallE (.app (.const ``Neg [.param 0]) (.bvar 0)) (.forallE (.bvar 1) (.bvar 2)))⟩

/-- The conversions needed by the fixed operators and numeral notation.
This relation says what the types are, not whether a checker accepts them. -/
inductive Casts : TypeCasts where
  | bitvecValue : Casts ctx bitvecType wordType
  | resultType : Casts ctx (.sort (.succ .zero)) resultParameter
  | wordInstance (op : Binary) : Casts ctx
      (.app (.const op.className [.zero]) bitvecType) (.app (.const op.className [.zero]) wordType)

  | negInstance : Casts ctx (.app (.const ``Neg [.zero]) bitvecType) (.app (.const ``Neg [.zero]) wordType)

  | literalInstance (n : Nat) : Casts ctx
      (applications (.const ``OfNat [.zero]) [bitvecType,numeral n])
      (applications (.const ``OfNat [.zero]) [wordType,numeral n])

/-- Arithmetic's fixed type casts do not depend on any source binder. -/
theorem casts_closed : ClosedCasts Casts := by
  intro ctx actual expected cast
  cases cast with
  | bitvecValue => exact ⟨⟨by trivial,width_closed⟩,by trivial,fun _ => .bitvecValue⟩
  | resultType => exact ⟨by trivial,by trivial,fun _ => .resultType⟩
  | wordInstance op =>
    exact ⟨⟨by trivial,⟨by trivial,width_closed⟩⟩,by trivial,fun _ => .wordInstance op⟩
  | negInstance =>
    exact ⟨⟨by trivial,⟨by trivial,width_closed⟩⟩,by trivial,fun _ => .negInstance⟩
  | literalInstance n =>
    have closed : (numeral n).ClosedN 0 :=
      (Represents.natural (n := n)).closed 0 rfl
    exact ⟨⟨⟨by trivial,⟨by trivial,width_closed⟩⟩,closed⟩,
      ⟨⟨by trivial,by trivial⟩,closed⟩,fun _ => .literalInstance n⟩


/-- The fixed arithmetic aliases available in a source/proof conversion
relation. This is an embedding of typing rules, never a successful query. -/
class Includes (casts : TypeCasts) : Prop where
  embed : ∀ ctx a b, Casts ctx a b → casts ctx a b

instance : Includes Casts := ⟨fun _ _ _ h => h⟩

end IRComparison.WordFrontend.Arithmetic
