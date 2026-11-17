import IRComparison.Frontend.LeanIREvaluation

namespace IRComparison.LeanBodyQuotation
open Lean4Lean LeanTyped

def imperativeQuote : Imperative.Cmd → Lean.Expr
  | .skip  => .const ``Imperative.Cmd.skip []
  | .letValue e b => .app (.app (.const ``Imperative.Cmd.letValue []) (LeanIRQuotation.quote e)) (imperativeQuote b)
  | .assign reg value => .app (.app (.const ``Imperative.Cmd.assign []) (Lean.Expr.lit (.natVal reg))) (LeanIRQuotation.quote value)
  | .store array address value => .app (.app (.app (.const ``Imperative.Cmd.store []) (Lean.Expr.lit (.natVal array))) (LeanIRQuotation.quote address)) (LeanIRQuotation.quote value)
  | .seq first second => .app (.app (.const ``Imperative.Cmd.seq []) (imperativeQuote first)) (imperativeQuote second)
  | .branch condition yes no => .app (.app (.app (.const ``Imperative.Cmd.branch []) (LeanIRQuotation.quote condition)) (imperativeQuote yes)) (imperativeQuote no)
  | .repeat count body => .app (.app (.const ``Imperative.Cmd.repeat []) (Lean.Expr.lit (.natVal count))) (imperativeQuote body)
  | .forRange e body => .app (.app (.const ``Imperative.Cmd.forRange []) (LeanIRQuotation.quote e)) (imperativeQuote body)

def imperativeCode : Imperative.Cmd → VExpr
  | .skip  => .const ``Imperative.Cmd.skip []
  | .letValue e b => .app (.app (.const ``Imperative.Cmd.letValue []) (LeanIRQuotation.code e)) (imperativeCode b)
  | .assign reg value => .app (.app (.const ``Imperative.Cmd.assign []) (numeral reg)) (LeanIRQuotation.code value)
  | .store array address value => .app (.app (.app (.const ``Imperative.Cmd.store []) (numeral array)) (LeanIRQuotation.code address)) (LeanIRQuotation.code value)
  | .seq first second => .app (.app (.const ``Imperative.Cmd.seq []) (imperativeCode first)) (imperativeCode second)
  | .branch condition yes no => .app (.app (.app (.const ``Imperative.Cmd.branch []) (LeanIRQuotation.code condition)) (imperativeCode yes)) (imperativeCode no)
  | .repeat count body => .app (.app (.const ``Imperative.Cmd.repeat []) (numeral count)) (imperativeCode body)
  | .forRange e body => .app (.app (.const ``Imperative.Cmd.forRange []) (LeanIRQuotation.code e)) (imperativeCode body)

theorem imperative_represents (body : Imperative.Cmd) : Represents (imperativeQuote body) (imperativeCode body) := by
  induction body with
  | skip  => exact .constant rfl
  | letValue e b hb => exact .app (.app (.constant rfl) (LeanIRQuotation.code_represents e)) hb
  | assign reg value => exact .app (.app (.constant rfl) (.natural)) (LeanIRQuotation.code_represents value)
  | store array address value => exact .app (.app (.app (.constant rfl) (.natural)) (LeanIRQuotation.code_represents address)) (LeanIRQuotation.code_represents value)
  | seq first second hfirst hsecond => exact .app (.app (.constant rfl) (hfirst)) (hsecond)
  | branch condition yes no hyes hno => exact .app (.app (.app (.constant rfl) (LeanIRQuotation.code_represents condition)) (hyes)) (hno)
  | «repeat» count body hbody => exact .app (.app (.constant rfl) (.natural)) (hbody)
  | forRange e body hb => exact .app (.app (.constant rfl) (LeanIRQuotation.code_represents e)) hb

def functionalQuote : Functional.Term → Lean.Expr
  | .letValue v e b => .app (.app (.app (.const ``Functional.Term.letValue []) (Lean.Expr.lit (.natVal v))) (LeanIRQuotation.quote e)) (functionalQuote b)
  | .yield version => .app (.const ``Functional.Term.yield []) (Lean.Expr.lit (.natVal version))
  | .letSet version reg value next => .app (.app (.app (.app (.const ``Functional.Term.letSet []) (Lean.Expr.lit (.natVal version))) (Lean.Expr.lit (.natVal reg))) (LeanIRQuotation.quote value)) (functionalQuote next)
  | .letWrite version array address value next => .app (.app (.app (.app (.app (.const ``Functional.Term.letWrite []) (Lean.Expr.lit (.natVal version))) (Lean.Expr.lit (.natVal array))) (LeanIRQuotation.quote address)) (LeanIRQuotation.quote value)) (functionalQuote next)
  | .bindResult body next => .app (.app (.const ``Functional.Term.bindResult []) (functionalQuote body)) (functionalQuote next)
  | .letResult version body next => .app (.app (.app (.const ``Functional.Term.letResult []) (Lean.Expr.lit (.natVal version))) (functionalQuote body)) (functionalQuote next)
  | .branch version condition yes no => .app (.app (.app (.app (.const ``Functional.Term.branch []) (Lean.Expr.lit (.natVal version))) (LeanIRQuotation.quote condition)) (functionalQuote yes)) (functionalQuote no)
  | .iterate version count body next => .app (.app (.app (.app (.const ``Functional.Term.iterate []) (Lean.Expr.lit (.natVal version))) (Lean.Expr.lit (.natVal count))) (functionalQuote body)) (functionalQuote next)
  | .forRange version e body next => .app (.app (.app (.app (.const ``Functional.Term.forRange []) (Lean.Expr.lit (.natVal version))) (LeanIRQuotation.quote e)) (functionalQuote body)) (functionalQuote next)
  | .forRangeCaptured version e body next => .app (.app (.app (.app (.const ``Functional.Term.forRangeCaptured []) (Lean.Expr.lit (.natVal version))) (LeanIRQuotation.quote e)) (functionalQuote body)) (functionalQuote next)

def functionalCode : Functional.Term → VExpr
  | .letValue v e b => .app (.app (.app (.const ``Functional.Term.letValue []) (numeral v)) (LeanIRQuotation.code e)) (functionalCode b)
  | .yield version => .app (.const ``Functional.Term.yield []) (numeral version)
  | .letSet version reg value next => .app (.app (.app (.app (.const ``Functional.Term.letSet []) (numeral version)) (numeral reg)) (LeanIRQuotation.code value)) (functionalCode next)
  | .letWrite version array address value next => .app (.app (.app (.app (.app (.const ``Functional.Term.letWrite []) (numeral version)) (numeral array)) (LeanIRQuotation.code address)) (LeanIRQuotation.code value)) (functionalCode next)
  | .bindResult body next => .app (.app (.const ``Functional.Term.bindResult []) (functionalCode body)) (functionalCode next)
  | .letResult version body next => .app (.app (.app (.const ``Functional.Term.letResult []) (numeral version)) (functionalCode body)) (functionalCode next)
  | .branch version condition yes no => .app (.app (.app (.app (.const ``Functional.Term.branch []) (numeral version)) (LeanIRQuotation.code condition)) (functionalCode yes)) (functionalCode no)
  | .iterate version count body next => .app (.app (.app (.app (.const ``Functional.Term.iterate []) (numeral version)) (numeral count)) (functionalCode body)) (functionalCode next)
  | .forRange version e body next => .app (.app (.app (.app (.const ``Functional.Term.forRange []) (numeral version)) (LeanIRQuotation.code e)) (functionalCode body)) (functionalCode next)
  | .forRangeCaptured version e body next => .app (.app (.app (.app (.const ``Functional.Term.forRangeCaptured []) (numeral version)) (LeanIRQuotation.code e)) (functionalCode body)) (functionalCode next)

theorem functional_represents (body : Functional.Term) : Represents (functionalQuote body) (functionalCode body) := by
  induction body with
  | letValue v e b hb => exact .app (.app (.app (.constant rfl) .natural) (LeanIRQuotation.code_represents e)) hb
  | yield version => exact .app (.constant rfl) (.natural)
  | letSet version reg value next hnext => exact .app (.app (.app (.app (.constant rfl) (.natural)) (.natural)) (LeanIRQuotation.code_represents value)) (hnext)
  | letWrite version array address value next hnext => exact .app (.app (.app (.app (.app (.constant rfl) (.natural)) (.natural)) (LeanIRQuotation.code_represents address)) (LeanIRQuotation.code_represents value)) (hnext)
  | bindResult body next hb hn => exact .app (.app (.constant rfl) hb) hn
  | letResult version body next hbody hnext => exact .app (.app (.app (.constant rfl) (.natural)) (hbody)) (hnext)
  | branch version condition yes no hyes hno => exact .app (.app (.app (.app (.constant rfl) (.natural)) (LeanIRQuotation.code_represents condition)) (hyes)) (hno)
  | iterate version count body next hbody hnext => exact .app (.app (.app (.app (.constant rfl) (.natural)) (.natural)) (hbody)) (hnext)
  | forRange v e body next hb hn => exact .app (.app (.app (.app (.constant rfl) .natural) (LeanIRQuotation.code_represents e)) hb) hn
  | forRangeCaptured v e body next hb hn => exact .app (.app (.app (.app (.constant rfl) .natural) (LeanIRQuotation.code_represents e)) hb) hn

def optionState : VExpr := .app (.const ``Option [.zero]) LeanIREvaluation.stateType

def eqState (left right : VExpr) : VExpr :=
  applications (.const ``Eq [.succ .zero]) [optionState,left,right]

def imperativeEval (body i x y state : VExpr) (locals : VExpr := LeanIRQuotation.nilInts) : VExpr :=
  applications (.const ``Imperative.Cmd.eval []) [i,x,y,body,state,locals]

def functionalEval (body i x y state : VExpr) (locals : VExpr := LeanIRQuotation.nilInts) : VExpr :=
  let states := applications (.const ``List.cons [.zero]) [LeanIREvaluation.stateType,state,
    .app (.const ``List.nil [.zero]) LeanIREvaluation.stateType]
  applications (.const ``Functional.Term.eval []) [i,x,y,body,states,locals]

def eqHead : VExpr := .app (.const ``Eq [.succ .zero]) optionState

theorem result_congr {env : VEnv} {U : Nat} {ctx : List VExpr}
    (eqTyped : env.HasType U ctx eqHead (.forallE optionState (.forallE optionState (.sort .zero))))
    (left : env.HasType U ctx result optionState)
    (right : env.IsDefEq U ctx source body optionState) :
    env.IsDefEq U ctx (eqState result source) (eqState result body) (.sort .zero) := by
  have head := VEnv.IsDefEq.appDF eqTyped left
  simp only [optionState, LeanIREvaluation.stateType, VExpr.inst] at head
  exact .appDF head right

end IRComparison.LeanBodyQuotation
