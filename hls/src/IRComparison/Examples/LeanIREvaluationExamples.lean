import IRComparison.Frontend.LeanIREvaluationCompiler
import IRComparison.Examples.LeanScalarExamples

namespace IRComparison.LeanIREvaluationExamples
open Lean Elab Command Lean4Lean LeanTyped LeanIRQuotation LeanIREvaluation

private def constants : Lean.Expr → List Lean.Name
  | .const name _ => [name]
  | .app f x => constants f ++ constants x
  | .lam _ ty b _ | .forallE _ ty b _ => constants ty ++ constants b
  | .letE _ ty value body _ => constants ty ++ constants value ++ constants body
  | .mdata _ b | .proj _ _ b => constants b
  | _ => []

run_cmd do
  let native ← getEnv
  for (name, type) in [(``Facts.literal,literalType),
      (``Facts.index, Slot.type .index), (``Facts.left, Slot.type .left), (``Facts.right, Slot.type .right),
      (``Facts.add,binaryType ``IRComparison.Expr.add ``Int.add),
      (``Facts.sub,binaryType ``IRComparison.Expr.sub ``Int.sub),
      (``Facts.mul,binaryType ``IRComparison.Expr.mul ``Int.mul),
      (``Facts.div,binaryType ``IRComparison.Expr.div ``Int.ediv),
      (``Facts.select, LeanIRSelect.signature)] do
    unless (loadFixedFact native name type).isSome do
      throwError "actual IR evaluator theorem signature mismatch: {name}"
  for name in [``LeanScalarExamples.mean, ``LeanScalarExamples.shadow,
      ``LeanScalarExamples.signed, ``LeanScalarExamples.choose] do
    let some original := LeanDefinition.compile native name | throwError "source rejected"
    let emitted := original.function.scalar.code.expr
    let names := (constants (quote emitted) ++ [``List, ``List.nil, ``List.cons, ``ScopedFacts.literal, ``ScopedFacts.index, ``ScopedFacts.left, ``ScopedFacts.right,
      ``ScopedFacts.add, ``ScopedFacts.sub, ``ScopedFacts.mul, ``ScopedFacts.div, ``ScopedFacts.select, ``Nat.zero, ``Nat.succ, ``Int, ``Int.ofNat, ``Int.neg,
      ``Int.add, ``Int.sub, ``Int.mul, ``Int.ediv, ``IRComparison.Expr, ``State, ``Option, ``Option.some,
      ``IRComparison.Expr.eval, ``Facts.literal, ``Facts.index, ``Facts.left, ``Facts.right,
      ``Facts.add, ``Facts.sub, ``Facts.mul, ``Facts.div, ``Facts.select, ``selectValue]).eraseDups
    let some model := LeanLibrary.installTypes native VEnv.empty names | throwError "type import failed"
    let context := stateType :: List.replicate 3 intType
    let some hi := LeanTypeInference.check model 0 context (.bvar 3) intType | throwError "index typing"
    let some hx := LeanTypeInference.check model 0 context (.bvar 2) intType | throwError "left typing"
    let some hy := LeanTypeInference.check model 0 context (.bvar 1) intType | throwError "right typing"
    let some hs := LeanTypeInference.check model 0 context (.bvar 0) stateType | throwError "state typing"
    let inputs : LeanIREvaluationCompiler.Inputs model 0 context :=
      ⟨.bvar 3,.bvar 2,.bvar 1,.bvar 0,hi.down,hx.down,hy.down,hs.down,nilInts⟩
    let some _ := LeanIREvaluationCompiler.compile native inputs emitted
      | throwError "IR evaluation proof construction failed for {name}"
    logInfo m!"{name}: constructed a typed equality about the actual emitted Expr.eval"

end IRComparison.LeanIREvaluationExamples
