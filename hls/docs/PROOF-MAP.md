# Proof and implementation map

The current ordinary entry is `StructuralBody.compileRetained`. Generation success and semantic preservation are separate theorems with different premises. See [technical scope](TECHNICAL-NOTE.md) and the detailed [source coverage table](LEAN-ENTRY.ja.md#対象構文の対応表).

## The end-to-end claim

For a complete Lean function in the supported fragment, compilation succeeds under the independent source/type/scope/environment and fixed-array conditions. For the generated artifact, execution from a corresponding admissible post-start state terminates and preserves the source's success/failure and public outputs.

The second sentence has execution premises in addition to the first sentence's compilation premises:

| Layer | Assumptions | Conclusion |
|---|---|---|
| Source → generated artifact | Independent original syntax; typing/scope/environment conditions; current-State discipline; fixed declarations and declared outputs | Frontend succeeds, generated code corresponds to the source, an Entry is constructed, RTL generation succeeds (`OrdinarySource.generates`) |
| Artifact → source observation | Source arrays have the specified layout; the selected plan is ready; input values fit allocated widths; the circuit is running after start and its storage agrees with the compiled initial state | There exist finitely many cycles and a resulting text-semantics state with the same source success/failure and public outputs (`Compiled.correct`, specialized by `FixedHLS.Entry.compile_correct`) |
| Setup/readout | Representable IDs/addresses and the separate protocol/initial-state premises | Conditional configuration/start/readout properties; not general configurability of every legal source initial state |

`FixedHLS.Entry.generates_correct` already combines generation and execution preservation once the typed fixed-array Entry exists. `OrdinarySource.generates` supplies the earlier source-to-Entry connection. The generated per-program `.generates` declaration refers to Entry-level totality; it is not the whole source-grammar theorem by itself.

For explicit optimization stages, `CertifiedHLS.Compiled.correct` compares against `runSource`: the native bodies executed in the supplied stage order and ranges. For a whole-function Entry, the specialization compares against the original `program s`. Internal arrays, queues and holding registers need not match the source representation.

## Trust boundary

```text
ordinary Lean definition + environment
    │  trusted Lean implementation / native environment interface
    ▼
source correspondence + general compiler theorems
    │  proof terms checked by the Lean kernel
    ├─ SMT candidates → Lean checks → accepted proof-carrying memory plan
    ▼
emitted text interpreted by the specified SystemVerilog semantics
    │  external simulation / synthesis checks (additional validation)
    ▼
external tool and physical device behavior: not proved by this artifact
```

The text theorem covers the emitted subset and its serialization/interpretation, rather than the whole IEEE standard. Observation includes source failure but not a specific failure reason or intermediate state after failure. The general post-start theorem is separate from reset/configuration. `checkExternalPorts` is an explicit additional check, not automatically called by `.compile`.

## Declaration map

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

[PaperCore](../src/PaperCore/README.md), named for the RHL paper’s core language, supplies semantic lemmas, index-sequence reasoning, buffer analysis and SMT support. Its generic solver interface has an explicit solver-soundness premise. The HLS candidate path instead rechecks candidates in Lean; these two guarantee interfaces are distinct.
