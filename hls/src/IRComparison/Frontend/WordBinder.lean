import IRComparison.Frontend.WordScalarSyntax

/-! Equivalent native annotations for a retained BV32 scalar. Scope extension
uses the actual annotation while the local-value interface remains Word. -/
namespace IRComparison.WordFrontend.WordBinder
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic

inductive Annotation where
  | word | bitvec
  deriving DecidableEq

def Annotation.core : Annotation → VExpr
  | .word => wordType | .bitvec => bitvecType

def Annotation.native : Annotation → Lean.Expr
  | .word => WordFrontend.word
  | .bitvec => .app (.const ``BitVec []) nativeWidth

structure Annotation.View (source : Lean.Expr) where
  annotation : Annotation
  shape : source = annotation.native

/-- Recognize the two annotations emitted by ordinary Lean elaboration. -/
def Annotation.view (source : Lean.Expr) : Option (View source) :=
  match source with
  | .const ``HybridWord.Word [] => some ⟨.word,rfl⟩
  | .app (.const ``BitVec [])
      (.app (.app (.app (.const ``OfNat.ofNat [.zero]) (.const ``Nat [])) (.lit (.natVal 32)))
        (.app (.const ``instOfNatNat []) (.lit (.natVal 32)))) => some ⟨.bitvec,rfl⟩
  | _ => none

theorem Annotation.view_complete (annotation : Annotation) :
    ∃ result, view annotation.native = some result := by
  cases annotation <;> exact ⟨_,rfl⟩

theorem Annotation.represented (annotation : Annotation) : Represents annotation.native annotation.core := by
  cases annotation with
  | word => exact .constant rfl
  | bitvec => exact .app (.constant rfl) width_represents

/-- Closed annotations are unchanged by lexical substitution. -/
theorem Annotation.substitute_native (annotation : Annotation) (σ : Nat → Lean.Expr) :
    LeanBindings.substitute σ annotation.native = annotation.native := by
  cases annotation <;> rfl

theorem Annotation.closed (annotation : Annotation) : annotation.core.ClosedN 0 := by
  cases annotation with | word => trivial | bitvec => exact ⟨by trivial,width_closed⟩

theorem Annotation.type_typed (annotation : Annotation) (library : Signatures env) :
    DirectTyping env 0 ctx annotation.core (.sort (.succ .zero)) := by
  cases annotation with
  | word => exact .constant library.word (by simp) rfl
  | bitvec => exact library.bitvec_typed

theorem Annotation.variable (annotation : Annotation) :
    CheckedTyping env 0 Arithmetic.Casts (annotation.core::ctx) (.bvar 0) wordType := by
  cases annotation with
  | word => exact .exact (.bvar .zero)
  | bitvec =>
    have termTyped : CastTyping env 0 Arithmetic.Casts (bitvec.core::ctx) (.bvar 0)
        bitvec.core.lift := .bvar .zero
    have unchanged : bitvec.core.lift = bitvec.core :=
      (Annotation.closed bitvec).liftN_eq (Nat.zero_le _)
    rw [unchanged] at termTyped
    exact .converted termTyped .bitvecValue

/-- The inferred type of a scalar body may retain the BV32 spelling. -/
theorem Annotation.result (annotation : Annotation)
    (value : CastTyping env 0 (SourceCasts env) ctx source annotation.core) :
    CheckedTyping env 0 (SourceCasts env) ctx source wordType := by
  cases annotation with
  | word => exact .exact value
  | bitvec => exact .converted value .bitvecValue

def Annotation.nextInputs (annotation : Annotation) (inputs : InputsTyped env ctx p)
    (closed : ClosedConstantTypes env) (library : Signatures env)
    (consDeclared : env.constants ``List.cons = some consSignature) :
    InputsTyped env (annotation.core::ctx) {p.lift with locals := .bvar 0 :: p.lift.locals} :=
  (inputs.lift closed annotation.core).withLocal .bvar annotation.variable library.word consDeclared

def Annotation.nextLocals (annotation : Annotation) (scope : ScalarSyntax.Locals env ctx p)
    (closed : ClosedConstantTypes env) :
    ScalarSyntax.Locals env (annotation.core::ctx) {p.lift with locals := .bvar 0 :: p.lift.locals} :=
  (scope.lift closed annotation.core).withLocal .bvar annotation.variable

theorem Annotation.argument (annotation : Annotation)
    (value : CheckedTyping env 0 (SourceCasts env) ctx source wordType) :
    CheckedTyping env 0 (SourceCasts env) ctx source annotation.core := by
  cases annotation with
  | word => exact value
  | bitvec =>
    cases value with
    | exact typed => exact .converted typed .wordValue
    | converted typed cast =>
      cases cast with
      | arithmetic cast => cases cast; exact .exact typed

end IRComparison.WordFrontend.WordBinder
