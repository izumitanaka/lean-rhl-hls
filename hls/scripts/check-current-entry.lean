import IRComparison.Tests

/-! Guard the production/archive boundary. Retired public parser entries must
not become available again through normal imports. The old reference traversals and direct-substitution rules must be absent.
The structural traversal and its Source/Syntax induction retain arguments unconditionally. -/
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let retired : List Name := [
    `IRComparison.WordFrontend.StructuralBody.body,
    `IRComparison.WordFrontend.FixedFunctionCompleteness.Source.stateCallInferred,
    `IRComparison.WordFrontend.FixedFunctionCompleteness.Source.stateCallFromSource,
    `IRComparison.WordFrontend.FixedFunctionCompleteness.Source.callFromClosure,
    `IRComparison.WordFrontend.StructuralSyntax.helper_checked_retarget_complete,
    `IRComparison.WordFrontend.FunctionSyntax.step_helper_checked_retarget_complete,
    `IRComparison.WordFrontend.FunctionSyntax.BindingValue.call_complete,
    `IRComparison.WordFrontend.FunctionSyntax.Syntax.checkedCallFromSourceBodies,
    `IRComparison.WordFrontend.FunctionSyntax.Syntax.checkedCallFromLambdaBodies,
    `IRComparison.WordFrontend.FunctionSyntax.Syntax.checkedStepCallFromLambdaBodies,
    `IRComparison.WordFrontend.FixedFunctionCompleteness.checkedCallFromArgumentSyntax,
    `IRComparison.WordFrontend.FunctionSyntax.Syntax.checkedStepCallFromEnvironment,
    `IRComparison.WordFrontend.FunctionSyntax.Syntax.checkedStepCallFromSourceBodies,
    `IRComparison.WordFrontend.FixedFunctionCompleteness.Source.checkedCallFromEnvironment,
    `IRComparison.WordFrontend.FixedFunctionCompleteness.Source.checkedStepCallFromEnvironment,
    `IRComparison.WordFrontend.FixedFunctionCompleteness.Source.checkedCallFromClosure,
    `IRComparison.WordFrontend.FixedFunctionCompleteness.Source.scalarCallFromSource,
    `IRComparison.WordFrontend.FixedFunctionCompleteness.Source.scalarStepCallFromSource,
    `IRComparison.WordFrontend.FixedFunctionCompleteness.Source.checkedStepCallFromClosure,
    `IRComparison.WordFrontend.FixedFunctionCompleteness.Source.stepCallFromClosure,
    `IRComparison.WordFrontend.FixedFunctionCompleteness.Source.stateCallCaptured,
    `IRComparison.WordFrontend.StructuralSyntax.helper_application_step_complete_code,
    `IRComparison.WordFrontend.StructuralSyntax.HeadForm.complete,
    `IRComparison.WordFrontend.StructuralSyntax.helper_complete,
    `IRComparison.WordFrontend.StructuralSyntax.helper_application_step_complete,
    `IRComparison.WordFrontend.FixedFunctionCompleteness.checkedCallFromSourceScope,
    `IRComparison.WordFrontend.FixedFunctionCompleteness.checkedScalarCallFromSyntax,
    `IRComparison.WordFrontend.FunctionSyntax.Syntax.checkedCallFromEnvironment,
    `IRComparison.WordFrontend.FunctionSyntax.Syntax.call,
    `IRComparison.WordFrontend.FunctionSyntax.Syntax.checkedCall,
    `IRComparison.WordFrontend.FunctionSyntax.Syntax.stepCall,
    `IRComparison.WordFrontend.FunctionSyntax.Syntax.checkedStepCall,
    `IRComparison.WordFrontend.FixedFunctionCompleteness.Source.call,
    `IRComparison.WordFrontend.FixedFunctionCompleteness.Source.checkedCall,
    `IRComparison.WordFrontend.FixedFunctionCompleteness.Source.stepCall,
    `IRComparison.WordFrontend.FixedFunctionCompleteness.Source.checkedStepCall,
    `IRComparison.WordFrontend.ScopedSyntax.Syntax.helperCall,
    `IRComparison.WordFrontend.FixedSequenceCompleteness.Source.helperCall,

    `IRComparison.WordFrontend.StructuralBody.read_bits_code,
    `IRComparison.WordFrontend.FixedFunctionCompleteness.generatesFunctionSyntaxInstalledWith,
    `IRComparison.WordFrontend.FixedFunctionCompleteness.generatesRetainedHeadSyntax,
    `IRComparison.WordFrontend.compile,
    `IRComparison.WordFrontend.sourceBudget,
    `IRComparison.WordFrontend.scalar,
    `IRComparison.WordFrontend.read,
    `IRComparison.WordFrontend.stepBody,
    `IRComparison.WordFrontend.body,
    `IRComparison.WordFrontend.ScalarEnvironment.parseCompatible,
    `IRComparison.WordFrontend.ScalarEnvironment.compile,
    `IRComparison.WordFrontend.ScalarEnvironment.compile_of_legacy,
    `IRComparison.WordFrontend.StructuralBody.compile,
    `IRComparison.WordFrontend.StructuralBody.compileCompatible,
    `IRComparison.WordFrontend.StructuralBody.compileCompatible_of_previous]
  for name in retired do
    if env.contains name then throwError "retired entry/declaration reintroduced: {name}"
  for name in [`IRComparison.WordFrontend.StructuralBody.compileRetained,
    `IRComparison.WordFrontend.OrdinarySource.generates,
    `IRComparison.FixedHLS.Entry.compile_total] do
    unless env.contains name do throwError "missing current entry/guarantee: {name}"
  logInfo m!"CURRENT ENTRY: compileRetained and generation theorem present; {retired.length} retired declarations absent"
