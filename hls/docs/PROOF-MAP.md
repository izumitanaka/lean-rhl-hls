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

## RHL rules in the executable memory transformation

The rule notation is in [sections 3–4 of the IR rules](HLS-SYNTAX-RULES.ja.md#3-バッファ挿入fifo化の基本規則). The links below open the corresponding Lean declarations. These are semantic rule theorems: the implementation does not have to build a syntactic proof tree with one constructor per paper rule. Some transformations invoke a rule directly; others lift it through expression/body syntax or compose it in a plan’s correctness proof.

| Rule / judgment | Lean declaration | Connection to the transformation |
|---|---|---|
| Relational judgment / insertion | [`Relational.Translation`](../src/IRComparison/Core/Relational.lean#L13); [`Insertion`](../src/IRComparison/Core/Relational.lean#L17) | Defines related executions, including matching failure; insertion compares source `skip` with a target action. |
| Tr-ReadMem | [`BufferRules.readMem_rule`](../src/IRComparison/Memory/BufferRules.lean#L50) | Lifted to bound slots by `HybridWindowRead.readMem_rule`, used by `HybridSymbolicRead.compile`, then through the body by `HybridSymbolicBody.compile`. |
| Tr-WriteMem / Tr-InsWBuf | [`StreamState.writeMem_rule`](../src/IRComparison/Memory/StreamState.lean#L115); [`insertWrite_rule`](../src/IRComparison/Memory/StreamState.lean#L128) | Composed by `directSend_rule`; `Related.send` is used in the producer compiler’s store case. The intermediate buffer is a proof decomposition, not an added source operation. |
| Tr-InsRBuf | [`BufferRules.insertRead_rule`](../src/IRComparison/Memory/BufferRules.lean#L31) | Repeated by `take_rule` to discard unwanted values and receive the requested one; `WindowFIFO.Corresponds.at_drop` connects this to executable routing. |
| Tr-InsMove | [`BufferRules.insertMove_rule`](../src/IRComparison/Memory/BufferRules.lean#L41) | Used in `SymbolicWindowSchedule.refill_correct` for a saved slot; the copied value must be defined. |
| Tr-InsMemBuf (retained-memory extension) | [`BufferRules.insertMemory_rule`](../src/IRComparison/Memory/BufferRules.lean#L18) | Used by `WindowCoverage.emit_exists` to establish successful loads; coverage and schedule correctness discharge `HybridSymbolicLoop.Plan.initial_rule` and `refill_rule`. |
| Tr-Seq / Tr-InsertL / Tr-InsertR / Tr-Conseq | [`Relational.seq`](../src/IRComparison/Core/Relational.lean#L34); [`insertLeft`](../src/IRComparison/Core/Relational.lean#L45); [`insertRight`](../src/IRComparison/Core/Relational.lean#L49); [`consequence`](../src/IRComparison/Core/Relational.lean#L22) | Compose the two computations or insert target-only work. `HybridRules` specializes structural rules to hybrid commands; global plans also compose their changing channel relation recursively. |
| Tr-If | [`Relational.branch_rule`](../src/IRComparison/Core/Relational.lean#L66) | Used in `HybridSymbolicBody.compile` and `HybridAlternatives`; guard evaluation, including failure, must agree. Each branch has its own strengthened precondition. |
| Tr-For and refill between iterations | [`Relational.for_rule`](../src/IRComparison/Core/Relational.lean#L94); [`for_with_refill_rule`](../src/IRComparison/Core/Relational.lean#L105) | The invariant is indexed by iteration number. `HybridSymbolicLoop.Plan.loop_rule` uses the refill variant; no refill is inserted after the final iteration. |

For the [producer/filter example](WALKTHROUGH.md#3-exposing-stages-for-buffer-insertion-and-fifo-conversion), follow these three paths. Buffer placement is chosen by analysis; the rule proofs justify the chosen placement rather than specifying the search heuristic.

1. **Buffer the consumer:** `HybridSymbolicLoop.compile` chooses offsets and compiles the body. `Plan.Held` relates the source array to the held values. `Plan.body_rule` justifies substituted reads; `Plan.refill_rule` establishes the next iteration’s relation. `Plan.loop_rule` composes them, and `Plan.correct` prefixes `Plan.initial_rule` using `Relational.insertLeft`. [Loop implementation and proofs](../src/IRComparison/Hybrid/HybridSymbolicLoop.lean).
2. **Replace intermediate memory by a FIFO:** `HybridSymbolicProducer.compile` changes producer stores into sends, and `HybridSymbolicProducerLoop.Plan.correct` handles producer iterations. On the consumer side, `HybridRoutingVC.query` asks for routing parameters; `checkLoads` constructs checked take/copy routes, and `accept` checks initial/refill conditions and invariant closure. `accept_correct` uses `HybridCompactFIFO.Plan.correct` to preserve the buffered consumer’s result. [Producer](../src/IRComparison/Hybrid/HybridSymbolicProducer.lean), [producer loop](../src/IRComparison/Hybrid/HybridSymbolicProducerLoop.lean), [VC construction and acceptance](../src/IRComparison/Hybrid/HybridRoutingVC.lean), [FIFO loop proof](../src/IRComparison/Hybrid/HybridCompactFIFO.lean).
3. **Compose stages and reach RTL:** `HybridSymbolicGlobal.Plan.correct` threads live-channel relations through the stage sequence and preserves public observations. This feeds the common lowering/backend path and finally `CertifiedHLS.Compiled.correct`. The global theorem proves composition of accepted stages; it does not assume that independently valid array choices can always be combined. [Global plan](../src/IRComparison/Hybrid/HybridSymbolicGlobal.lean), [source-to-text theorem](../src/IRComparison/Frontend/CertifiedHLS.lean).

The paper’s rule names identify the inherited reasoning, not identical source languages. This implementation has finite-array bounds, explicit failure and lexical value bindings; BV32 evaluation is preserved by the frontend/IR connection. Tr-InsMemBuf is an additional rule for arrays retained in memory. SMT candidate acceptance is separate from the validity of these general rules.

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
