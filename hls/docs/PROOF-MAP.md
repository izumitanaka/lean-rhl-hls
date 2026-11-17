# Proof and implementation map

The current ordinary entry is `StructuralBody.compileRetained`. Generation success and semantic preservation are separate theorems with different premises. See [technical scope](TECHNICAL-NOTE.md) and the detailed [source coverage table](LEAN-ENTRY.ja.md#対象構文の対応表).

| Obligation | Source and principal declaration |
|---|---|
| Independent original syntax | [WordOrdinarySource](../src/IRComparison/Frontend/WordOrdinarySource.lean): `OrdinarySource.Body`, scalar/function/read judgments |
| Real environment and dependency conditions | [WordNativeEnvironment](../src/IRComparison/Frontend/WordNativeEnvironment.lean): `NativeEnvironment.Input`, `input`, `input_complete` |
| Shared induction over nesting and binding | [WordOrdinarySourceInterpretation](../src/IRComparison/Frontend/WordOrdinarySourceInterpretation.lean): `Body.Flow.interpret`, `Function.Flow.interpret`, `Body.syntaxEntry` |
| Original syntax through successful RTL generation | [WordOrdinarySourceInterpretation](../src/IRComparison/Frontend/WordOrdinarySourceInterpretation.lean): `OrdinarySource.generates` |
| Internal Syntax to retained entry | [WordFixedFunctionCompleteness](../src/IRComparison/Frontend/WordFixedFunctionCompleteness.lean): `generatesRetainedSyntaxInstalled` |
| Actual frontend and correctness | [WordStructuralBody](../src/IRComparison/Frontend/WordStructuralBody.lean): `compileRetained`, `compileRetained_correct` |
| Fixed-array Entry totality and correctness | [FixedHLS](../src/IRComparison/Frontend/FixedHLS.lean): `Entry.compile_total`, `Entry.compile_correct` |
| Lean-to-RTL composition | [CertifiedHLS](../src/IRComparison/Frontend/CertifiedHLS.lean): `ProgramEntry.compile_correct`, `Compiled.correct` |
| Whole-array routing and SMT candidate checking | [HybridRoutingVC](../src/IRComparison/Hybrid/HybridRoutingVC.lean): `accept`; [HybridSymbolicGlobal](../src/IRComparison/Hybrid/HybridSymbolicGlobal.lean) |
| Shared graph and structured pipeline | [SharedPipelineSound](../src/IRComparison/Circuit/SharedPipelineSound.lean): shared pipeline correctness; [transformation rules](HLS-SYNTAX-RULES.ja.md) for scheduling and integration |
| Output text and preparation protocol | [SystemVerilog](../src/IRComparison/Circuit/SystemVerilog/PreparationSound.lean) and related serialization/interface proofs |
| Axiom dependency audit | [Audit.lean](../Audit.lean) |

`OrdinarySource.generates` concludes the existence of the successfully compiled result, code correspondence and Entry; source execution equivalence is obtained through `Source.computation` and the Entry/backend correctness chain. The theorem is not shorthand for “every program runs without failure.” Native environment conditions, static declarations and runtime readiness/layout conditions are documented separately.

The current build retains common proof-construction, typing and environment infrastructure used by the retained frontend. It does not retain the old `StructuralBody.body` or an automatic direct-substitution fallback.

PaperCore supplies shared index-sequence, buffer-analysis and SMT modules. The full paper-AST compiler is not part of this public distribution. Its generic solver-soundness premise must not be substituted for the current HLS candidate recheck. Current source files and proofs retain their existing namespaces.
