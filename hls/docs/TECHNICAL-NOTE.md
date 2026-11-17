# Technical scope of the current implementation

Izumi Tanaka — source update, 2026-11-17.

This project extends [*Relational Hoare Logic for High-Level Synthesis of Hardware Accelerators*](https://arxiv.org/abs/2601.09217), by Izumi Tanaka, Ken Sakayori, Shinya Takamaeda-Yamazaki and Naoki Kobayashi (ESOP 2026), toward a Lean-based, formally verified HLS compiler. Its implemented focus is connecting relational memory transformation to ordinary Lean computations and RTL, with explicit proof boundaries. A novelty claim against all other certified HLS work would require a separate comparison.

Start with the [executable walkthrough](WALKTHROUGH.md) for input, intermediate computations, buffer/FIFO transformation and emitted RTL.

## Design intent and relationship to the paper

The paper's central contribution used here is relational reasoning about a change of representation: source arrays and target streams need not have equal internal states. Logical index sequences describe which source elements are represented by queued and held values. Insertion and read-replacement rules preserve that relation through sequencing, branches and loops.

The Lean mechanization, ordinary-Lean input connection, hybrid BV32 language and RTL backend described here are additions to that foundation. They are not obtained simply by importing the paper's core language. The original experimental flow used an external HLS tool; this project implements the lowering and text-generation stages too. The paper's performance results are not measurements of this backend.

| Component | Place in this design |
|---|---|
| `PaperCore` | Lean formalization support named for the paper's core language: semantics, array analysis, index-sequence reasoning and SMT infrastructure |
| `HybridRules.Translation` | Relates source-memory and target-command executions through a relation between states; supports composition and control structure |
| `BufferRules` and `HybridSymbolicLoop` | Instantiate insertion/read-replacement reasoning for held values and loop refills; include memory-backed insertion when an array remains in memory |
| `HybridRoutingVC` and `HybridSymbolicGlobal` | Form/check routing obligations, select whole-array candidates and compose an accepted global plan |
| `CertifiedHLS` and the circuit backend | Connect source computation and transformed execution to scheduled, finite-width circuits and emitted text |

This applies the RHL method to a different language. BV32 rounding, explicit read failures, held scalar values and memory-preserving alternatives require corresponding rule instances and premises. The current SMT encoding is not claimed to be identical to the earlier implementation.

## Entry points and automatic decisions

`hls_fixed_program` accepts a complete function and fixed array declarations. Its loops and sequential order come from the function. `hls_certified` accepts a processing body; the caller then specifies its designated input array, iteration range and stage position. For multiple stages the caller also supplies sizes/layout and public outputs. The generated body entries carry the source correspondence proofs.

Both use the common memory compiler and backend. The whole-function entry packages the function as one stage with one external iteration. It does not automatically split source loops into separate producer/consumer stages, so it does not expose the same cross-stage FIFO opportunities as explicit stage descriptions. No automatic task decomposition is implied by the whole-function generation theorem. The intended direction is to infer the needed stage boundaries and producer/consumer relations from supported complete Lean functions, then apply buffering and eligible FIFO conversion automatically; explicit stage metadata is the current way to supply that information. This does not mean every array must become a FIFO.

| Supplied by the caller | Derived or checked by the tool |
|---|---|
| Supported Lean computation and fixed array layout | Parsed body, retained scalar bindings, source/code correspondence |
| Public output IDs | Output declaration and port-presence checks; preservation of these arrays |
| For optimization entry: stage order, iteration ranges and designated input arrays | Access/reuse analysis, buffer candidates, per-array FIFO candidates and global plan checks |
| Optional loop strategy; default is rolled | Scheduling, admissibility of supported overlap, holding storage, width analysis and RTL |
| Initial data and host setup | Computation after start; separate conditional setup/readout contracts |

The pure `.compile` API does not invoke an external solver. `CertifiedHLS.compileWithSMT` explicitly enables solver-assisted routing. An optimization budget controls search, not how long a circuit may execute. Default choices and checked fallback plans avoid requiring users to write scheduling pragmas.

## Input and guarantees

The ordinary frontend accepts a specified fragment of Lean with BV32 values, an explicit State API, predeclared fixed arrays, reads/writes/copies, local scalar and State bindings, branches, static ranges, supported forIn/foldlM expansions and helper functions. The source judgments allow nesting and composition; proof coverage is not defined as “the parser happens to succeed.” The exact source conditions and coverage table are in [LEAN-ENTRY](LEAN-ENTRY.ja.md).

`OrdinarySource.generates` takes the native environment/input conditions, original-body syntax, latest-State usage, static register conditions, unique declarations and declared public outputs. It derives successful `StructuralBody.compileRetained`, code typing/correspondence, a `FixedHLS.Entry`, and successful `Entry.compile`. It does not take parser success, a generated Entry or internal checker success as assumptions.

This generation theorem is distinct from semantic preservation. The latter uses the source computation correspondence and the existing Entry/backend/text theorems, with their input, layout and initial-state conditions. It relates termination, source success/failure and public outputs. It does not prove successful source execution on every possible input or equality of internal hardware state.

Helper scalar arguments use IR `letValue` bindings for call-time values. A helper that updates State before using an argument such as `s.regs 0` still uses the old argument value. The current runtime and common induction proofs use only this retained-argument mode; the direct-substitution body, mode switch and automatic parser fallback have been removed.

## IR, optimization and realization

The hybrid computation IR combines an expression layer with structured stateful execution:

- `Value` computes from available values (arithmetic, locals, rounding), without reading state.
- `ReadCode` explicitly orders register/memory reads, binds results and chooses branches, including failure behavior.
- Source memory commands and target commands describe sequencing, array updates, branches and loops; the target also describes buffering and communication.

The name “hybrid” refers to this split between values and effects. The representation uses lexical bindings and structured control rather than a flat SSA graph. This makes it possible to retain a helper argument's call-time value while separately changing an array read into use of a held value or FIFO receive.

Buffer insertion turns repeated accesses into explicit initial loads, held values and refills. FIFO conversion then replaces suitable array storage by ordered sends/receives. The [three-point filter example](WALKTHROUGH.md#3-exposing-stages-for-buffer-insertion-and-fifo-conversion) illustrates why these are different transformations. Buffer insertion precedes whole-array FIFO selection. Arrays that are read and written in the same processing body retain memory in the current optimization path. The whole-array decision avoids introducing simultaneous FIFO and random-access views that would require extra coherence conditions. Public outputs retain addressable memory; routing also checks the supported producer/consumer pattern, order, capacity and noninterference conditions. Memory-backed buffers are possible even where FIFO conversion is unsuitable. Static reads/discards are explicit; there is no lazy peek cache.

The default symbolic route preserves loops. Communication selection starts with a certified memory plan and greedily tries arrays in a deterministic order. Each addition rechecks the whole plan. SMT replies are candidates, rechecked by `HybridRoutingVC.accept` and related Lean predicates; neither solver answers nor locally accepted arrays are blindly composed. A candidate rejection, timeout, or logging failure retains the previously accepted plan. External process deadlines cover process exit and output collection, including inherited pipes.

The structured backend uses shared combinational nodes and references, including validity. Sharing is consumed by range/reference analysis, finite-width evaluation and emission. Unused invalid reads still fail; invalid reads in unselected branches are not observed. Binding environments do not rebuild the old expression tree at runtime. Dedicated `wrap32` supports BV32 rounding; compatibility `wrapped?`, HybridAffine arithmetic expansion and explicitly selected older backend paths remain and are not claimed to be globally sharing-free.

Scheduling adds clock placement to existing operations. Branches and loops can remain structured; checked overlap across loop boundaries is implemented for the supported pattern. For the checked loop-overlap pattern, a final single-clock fragment is moved across the loop boundary and bundled with the next iteration's first clock when dependencies and guard preservation permit. Structured children are processed recursively; a branch or loop remaining inside a body can prevent overlap of that outer loop. This is not arbitrary modulo scheduling or a guarantee of any requested initiation interval. Synchronous memories and multi-cycle arithmetic are not implemented. Physical timing is not part of the correctness statement. [Rules](HLS-SYNTAX-RULES.ja.md), [scheduling rules](HLS-SYNTAX-RULES.ja.md#6-スケジューリング).

## Trust and external interfaces

The Lean implementation and native environment/registration interface are trusted; generated proof terms are checked by the Lean kernel. The artifact does not verify Lean itself. The audit checks selected theorem dependencies and rejects axioms other than `propext`, `Classical.choice`, and `Quot.sound`, including rejecting `sorryAx`.

The output proof concerns a defined two-state SystemVerilog subset and its serialization/interpretation. It does not verify the full IEEE semantics, simulator, synthesis tool, host software or physical device. Finite FIFOs fail on empty receive/full send; failure reasons and post-failure intermediate state are outside the observation relation.

External IDs and addresses use 32-bit ports. `Fits` and related conditional request/readout theorems must be distinguished from internal compilation. `checkExternalPorts` is not automatically called by internal compile, and a general theorem that every legal source initial state can be installed through configuration ports remains unproved. [Exact external boundary](HLS-SYNTAX-RULES.ja.md#外部ポートと初期設定).

## Validation and attribution

The [reproduction guide](REPRODUCING.md) lists commands to build the proofs and run frontend/RTL regressions. Logs and generated artifacts are local outputs rather than part of this repository. Examples supplement general proofs; see [workload scope](BENCHMARKS.md).

This implementation builds on the [RHL work of Tanaka, Sakayori, Takamaeda-Yamazaki and Kobayashi](https://arxiv.org/abs/2601.09217). The name [PaperCore](../src/PaperCore/README.md) refers to the paper’s core language; its formalization supplies semantic, array-analysis and SMT infrastructure used by HLS. The earlier paper's measured FPGA speedups do not transfer to this backend.

Verified HLS itself is not a new claim: see [Vericert](https://github.com/ymherklotz/vericert). This prototype also does not claim superiority over other Lean hardware-verification work such as [Graphiti](https://vca.epfl.ch/papers/asplos26_fvo.pdf). These references identify context, not an exhaustive comparison.
