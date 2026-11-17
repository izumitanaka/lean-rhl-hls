import IRComparison.Frontend.WordArithmeticTyping

/-! Both raw Nat literals and the `OfNat.ofNat Nat` applications produced by
ordinary elaboration. This concerns static identifiers/capacities, not a new
source notation or normalization of arbitrary Lean expressions. -/
namespace IRComparison.WordFrontend
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic

inductive NatNotation where
  | raw | elaborated
  deriving DecidableEq

def NatNotation.native (form : NatNotation) (n : Nat) : Lean.Expr :=
  match form with
  | .raw => .lit (.natVal n)
  | .elaborated => Lean.mkApp3 (.const ``OfNat.ofNat [.zero]) (.const ``Nat []) (.lit (.natVal n))
      (.app (.const ``instOfNatNat []) (.lit (.natVal n)))

def NatNotation.core (form : NatNotation) (n : Nat) : VExpr :=
  match form with
  | .raw => numeral n
  | .elaborated => applications (.const ``OfNat.ofNat [.zero])
      [natType,numeral n,.app (.const ``instOfNatNat []) (numeral n)]

theorem NatNotation.represents (form : NatNotation) (n : Nat) : Represents (form.native n) (form.core n) := by
  cases form with
  | raw => exact .natural
  | elaborated => exact .app (.app (.app (.constant rfl) (.constant rfl)) .natural) (.app (.constant rfl) .natural)

def NatNotation.argument (form : NatNotation) (library : Arithmetic.Signatures env) (n : Nat) :
    NatArgument env ctx (form.native n) := {
  represented := ⟨form.core n,form.represents n⟩
  typed := by cases form; exact library.literals.numeral_typed n; exact library.natural_notation_typed n
  closed := by cases form <;> rfl }

structure NatNotation.View (source : Lean.Expr) where
  value : Nat
  form : NatNotation
  shape : source = form.native value

def NatNotation.view (source : Lean.Expr) : Option (View source) :=
  match h : source with
  | .lit (.natVal n) => some ⟨n,.raw,rfl⟩
  | .app (.app (.app (.const ``OfNat.ofNat [.zero]) (.const ``Nat [])) (.lit (.natVal n)))
      (.app (.const ``instOfNatNat []) (.lit (.natVal m))) =>
    if same : m = n then some ⟨n,.elaborated,by subst m; rfl⟩ else none
  | _ => none

theorem NatNotation.view_complete (form : NatNotation) (n : Nat) :
    ∃ result, view (form.native n) = some result := by
  cases form with
  | raw => exact ⟨_,rfl⟩
  | elaborated =>
    refine ⟨⟨n,.elaborated,rfl⟩,?_⟩
    simp [view,native,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB]

end IRComparison.WordFrontend
