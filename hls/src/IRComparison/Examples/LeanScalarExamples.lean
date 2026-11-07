import IRComparison.Frontend.LeanArithmeticNormalization
import IRComparison.Examples.Examples

namespace IRComparison.LeanScalarExamples

/-- These are ordinary Lean definitions, not an imperative-source AST. -/
def mean (_i x y : Int) : Int := (x + y) / 2

def shadow (i x y : Int) : Int :=
  let x := x + y
  let y := x - i
  x * y

def choose (i x y : Int) : Int :=
  if x != 0 then
    let z := y + i
    z * z
  else x - y

def signed (i x y : Int) : Int := -x + (y - i) / 2

/-- An unsupported source construct must be reported, not assigned a default meaning. -/
def helperCall (i x y : Int) : Int := shadow i x y

unsafe def unsafeMean (_i x y : Int) : Int := (x + y) / 2
opaque opaqueMean (_i x y : Int) : Int := (x + y) / 2

private def zeroState : State := ⟨fun _ => 0, fun _ => #[]⟩

/-- Exercise the general binary certificate parser at every supported arithmetic
    node, including under let and conditional expressions. Only a regression
    test; correctness is supplied by compileBinary_correct. -/
private def checkArithmeticNodes (env : Lean.Environment) (layout : LeanScalar.Layout) :
    Lean.Expr → Except String Nat
  | source@(.app (.app head left) right) => do
      if (LeanScalar.checkBinaryHead head).isSome then
        let some result := LeanArithmetic.compileBinary env layout source
          | throw "formal operator bridge rejected a scalar compiler operator"
        for (i,x,y) in ([(0,2,4), (3,-4,0)] : List (Int × Int × Int)) do
          let some original := LeanScalar.compile layout source | throw "scalar parser rejected binary node"
          unless result.code.code.expr.eval i x y zeroState == original.code.expr.eval i x y zeroState do
            throw "formal operator bridge changed generated code behavior"
        return 1 + (← checkArithmeticNodes env layout left) + (← checkArithmeticNodes env layout right)
      else
        return (← checkArithmeticNodes env layout (.app head left)) +
          (← checkArithmeticNodes env layout right)
  | .app f x => return (← checkArithmeticNodes env layout f) + (← checkArithmeticNodes env layout x)
  | .letE _ (.const ``Int []) value body _ => do
      let some a := LeanScalar.compile layout value | throw "scalar let value rejected"
      return (← checkArithmeticNodes env layout value) +
        (← checkArithmeticNodes env (some a.toBinding :: layout) body)
  | .mdata _ body => checkArithmeticNodes env layout body
  | _ => return 0

/- These commands TEST actual definition extraction and actual Lean evaluation.
   They are not part of the correctness argument and must not be counted as
   the general native-function/Lean.Expr quotation theorem. -/
open Lean Meta Elab Command in
run_cmd liftTermElabM do
  let inputs : List (Int × Int × Int) := [(0,2,4), (3,0,5), (-2,-3,7), (2,5,-4)]
  for name in [``mean, ``shadow, ``choose, ``signed] do
    let some definition := LeanDefinition.compile (← getEnv) name
      | throwError "native definition parser rejected {name}"
    let some _ := LeanTyped.viewDefinition definition
      | throwError "proof-side declaration translation rejected {name}"
    let parsed := definition.function
    let a := parsed.scalar
    let some normalized := LeanArithmeticNormalization.plan (← getEnv) parsed.body
      | throwError "arithmetic normalization planning failed for {name}"
    let some normalizedCode := LeanScalar.compile LeanScalar.initialLayout normalized.expression
      | throwError "normalized expression was not accepted for {name}"
    match checkArithmeticNodes (← getEnv) LeanScalar.initialLayout parsed.body with
    | .error message => throwError "{name}: {message}"
    | .ok count =>
      unless count > 0 do throwError "arithmetic normalization was not exercised for {name}"
      logInfo m!"native input {name}: {count} arithmetic source/IR certificates constructed"
    for (i,x,y) in inputs do
      let actual ← evalExpr Int (mkConst ``Int)
        (mkAppN (mkConst name) #[toExpr i, toExpr x, toExpr y])
      unless a.native i x y zeroState == actual do
        throwError "native mismatch for {name} at {(i,x,y)}"
      unless normalizedCode.native i x y zeroState == actual do
        throwError "normalized native mismatch for {name} at {(i,x,y)}"
      unless a.code.expr.eval i x y zeroState == some actual do
        throwError "scalar IR mismatch for {name}"
    -- Both IRs use the exact same parsed native source, via independent bodies.
    let body := LeanScalar.storeBody a 0
    let xs : Array Int := #[2,4,6,8]
    let input := arrayInput xs
    for (start,stride,count) in ([(0,1,3), (3,-1,3), (0,2,1)] : List (Int × Int × Nat)) do
      let mut expected : Array Int := #[0,0,0,0]
      for k in List.range count do
        let i := start + (k : Int) * stride
        let some x := input i | throwError "test input index"
        let some y := input (i+stride) | throwError "test input successor"
        let value ← evalExpr Int (mkConst ``Int)
          (mkAppN (mkConst name) #[toExpr i, toExpr x, toExpr y])
        expected := expected.set! i.toNat value
      let s := Examples.initial 4
      let original := NativeLoop.run (NativeLoop.readBody input
        (fun i x y s => s.write 0 i (a.native i x y s)) 0 stride) start stride count s
      let imp := (NativeBody.compileImperative body start stride count 0 stride).eval input s
      let fn := (NativeBody.compileFunctional body start stride count 0 stride).eval input s
      for (label,result) in [("parsed native",original),("imperative",imp),("functional",fn)] do
        unless Examples.observe result == some (0,expected) do
          throwError "{label} output mismatch for {name}, stride {stride}"
    logInfo m!"native input {name}: scalar/let/branch and both optimized IRs checked"
  for name in [``unsafeMean, ``opaqueMean, `IRComparison.missingDefinition] do
    if (LeanDefinition.compile (← getEnv) name).isSome then
      throwError "unsupported or unavailable declaration was accepted: {name}"
  let unsupported ← getConstInfoDefn ``helperCall
  if (LeanScalar.compileFunction unsupported.value).isSome then
    throwError "unsupported constant application was silently accepted"

/- Check the fixed primitive bridge statements against the exact heads used
   by the parser. This is a library consistency check, not per-program proof. -/
open Lean Elab Command in
run_cmd do
  for (name, expected) in [
      (``LeanTyped.Standard.intRefl, LeanTyped.reflType),
      (``LeanTyped.Standard.intTrans, LeanTyped.transType),
      (``LeanTyped.Standard.intCongr, LeanTyped.congrType)] do
    let some fact := LeanTyped.loadFixedFact (← getEnv) name expected
      | throwError "fixed equality theorem has a different signature: {name}"
    let some _ := fact.install Lean4Lean.VEnv.empty
      | throwError "fixed equality theorem registration failed: {name}"
    if (LeanTyped.loadFixedFact (← getEnv) name LeanTyped.intType).isSome then
      throwError "fixed theorem importer accepted a wrong signature: {name}"
  let facts := [
    (``LeanTyped.Standard.add, NativeRHL.ExprAnalysis.addHead, ``Int.add),
    (``LeanTyped.Standard.sub, NativeRHL.ExprAnalysis.subHead, ``Int.sub),
    (``LeanTyped.Standard.mul, NativeRHL.ExprAnalysis.mulHead, ``Int.mul),
    (``LeanTyped.Standard.div, NativeRHL.ExprAnalysis.divHead, ``Int.ediv)]
  for (fact, head, primitive) in facts do
    let some view := LeanTyped.viewBinaryFact (← getEnv) fact
      | throwError "could not import fixed standard fact {fact}"
    let some model := view.install Lean4Lean.VEnv.empty
      | throwError "could not register fixed standard fact {fact}"
    unless (view.install model).isNone do
      throwError "standard fact import overwrote an existing declaration: {fact}"
    let info ← getConstInfo fact
    let .forallE _ (.const ``Int []) (.forallE _ (.const ``Int []) statement _) _ := info.type
      | throwError "primitive bridge {fact} has an unexpected argument type"
    let .app (.app (.app (.const ``Eq [.succ .zero]) (.const ``Int [])) left) right := statement
      | throwError "primitive bridge {fact} is not the expected integer equality"
    let expectedLeft := Expr.app (.app head (.bvar 1)) (.bvar 0)
    let expectedRight := Expr.app (.app (.const primitive []) (.bvar 1)) (.bvar 0)
    unless left == expectedLeft && right == expectedRight do
      throwError "primitive bridge {fact} does not match the parser's exact standard instance"

def intLiteral (n : Nat) : Lean.Expr := .app (.const ``Int.ofNat []) (.lit (.natVal n))

theorem unbound_variable_rejected : (LeanScalar.compile [] (.bvar 0)).isNone = true := rfl

theorem non_scalar_slot_rejected : (LeanScalar.compile [none] (.bvar 0)).isNone = true := rfl

theorem wrong_universe_rejected :
    (LeanScalar.compile [] (.app (.app (.const ``Int.add [.zero]) (intLiteral 1))
      (intLiteral 2))).isNone = true := by decide

theorem unsupported_let_type_rejected :
    (LeanScalar.compile [] (.letE `n (.const ``Nat []) (.lit (.natVal 2))
      (.bvar 0) false)).isNone = true := rfl

/-- A dangling variable can hide in the decision argument ignored by the
    scalar interpretation. The public definition entry must still reject it. -/
private def danglingDecisionBody : Lean.Expr :=
  NativeRHL.ExprAnalysis.conditional (intLiteral 1) (.bvar 99)
    (intLiteral 2) (intLiteral 3)

private def danglingDecisionFunction : Lean.Expr :=
  .lam `i (.const ``Int []) (.lam `x (.const ``Int [])
    (.lam `y (.const ``Int []) danglingDecisionBody .default) .default) .default

theorem dangling_decision_has_scalar_interpretation :
    (LeanScalar.compile LeanScalar.initialLayout danglingDecisionBody).isSome = true := by decide

theorem dangling_decision_function_rejected :
    (LeanScalar.compileFunction danglingDecisionFunction).isNone = true := by decide

end IRComparison.LeanScalarExamples
