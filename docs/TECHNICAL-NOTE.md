# Technical scope of the current implementation

Izumi Tanaka — source update, 2026-11-17.

This note describes the current implementation and its guarantee boundaries, not a claim of novelty established by a comprehensive literature survey.

## Input and guarantees

The ordinary frontend accepts a specified fragment of Lean with BV32 values, an explicit State API, predeclared fixed arrays, reads/writes/copies, local scalar and State bindings, branches, static ranges, supported forIn/foldlM expansions and helper functions. The source judgments allow nesting and composition; proof coverage is not defined as “the parser happens to succeed.” The exact source conditions and coverage table are in [LEAN-ENTRY](../hls/docs/LEAN-ENTRY.ja.md).

`OrdinarySource.generates` takes the native environment/input conditions, original-body syntax, latest-State usage, static register conditions, unique declarations and declared public outputs. It derives successful `StructuralBody.compileRetained`, code typing/correspondence, a `FixedHLS.Entry`, and successful `Entry.compile`. It does not take parser success, a generated Entry or internal checker success as assumptions.

This generation theorem is distinct from semantic preservation. The latter uses the source computation correspondence and the existing Entry/backend/text theorems, with their input, layout and initial-state conditions. It relates termination, source success/failure and public outputs. It does not prove successful source execution on every possible input or equality of internal hardware state.

Helper scalar arguments use IR `letValue` bindings for call-time values. A helper that updates State before using an argument such as `s.regs 0` still uses the old argument value. The current runtime and common induction proofs use only this retained-argument mode; the direct-substitution body, mode switch and automatic parser fallback have been removed.

## IR, optimization and realization

The hybrid computation IR separates value computation from ordered state changes, reads/writes and communication. Buffer insertion precedes whole-array FIFO selection. Arrays that are read and written in the same processing body retain memory in the current optimization path. Memory-backed buffers are possible even where FIFO conversion is unsuitable. Static reads/discards are explicit; there is no lazy peek cache.

The default symbolic route preserves loops. Communication selection starts with a certified memory plan and greedily tries arrays in a deterministic order. Each addition rechecks the whole plan. SMT replies are candidates, rechecked by `HybridRoutingVC.accept` and related Lean predicates; neither solver answers nor locally accepted arrays are blindly composed. A candidate rejection, timeout, or logging failure retains the previously accepted plan. External process deadlines cover process exit and output collection, including inherited pipes.

The structured backend uses shared combinational nodes and references, including validity. Sharing is consumed by range/reference analysis, finite-width evaluation and emission. Unused invalid reads still fail; invalid reads in unselected branches are not observed. Binding environments do not rebuild the old expression tree at runtime. Dedicated `wrap32` supports BV32 rounding; compatibility `wrapped?`, HybridAffine arithmetic expansion and explicitly selected older backend paths remain and are not claimed to be globally sharing-free.

Scheduling adds clock placement to existing operations. Branches and loops can remain structured; checked overlap across loop boundaries is implemented for the supported pattern. Arbitrary modulo scheduling, arbitrary initiation intervals, synchronous memories and multi-cycle arithmetic are not implemented. Physical timing is not part of the correctness statement. [Rules](../hls/docs/HLS-SYNTAX-RULES.ja.md), [scheduling rules](../hls/docs/HLS-SYNTAX-RULES.ja.md#6-スケジューリング).

## Trust and external interfaces

The Lean implementation and native environment/registration interface are trusted; generated proof terms are checked by the Lean kernel. The artifact does not verify Lean itself. The audit checks selected theorem dependencies and rejects axioms other than `propext`, `Classical.choice`, and `Quot.sound`, including rejecting `sorryAx`.

The output proof concerns a defined two-state SystemVerilog subset and its serialization/interpretation. It does not verify the full IEEE semantics, simulator, synthesis tool, host software or physical device. Finite FIFOs fail on empty receive/full send; failure reasons and post-failure intermediate state are outside the observation relation.

External IDs and addresses use 32-bit ports. `Fits` and related conditional request/readout theorems must be distinguished from internal compilation. `checkExternalPorts` is not automatically called by internal compile, and a general theorem that every legal source initial state can be installed through configuration ports remains unproved. [Exact external boundary](../hls/docs/HLS-SYNTAX-RULES.ja.md#外部ポートと初期設定).

## Validation and attribution

The [reproduction guide](REPRODUCING.md) lists commands to build the proofs and run frontend/RTL regressions. Logs and generated artifacts are local outputs rather than part of this repository. Examples supplement general proofs; see [workload scope](BENCHMARKS.md).

This implementation builds on the [RHL work of Tanaka, Sakayori, Takamaeda-Yamazaki and Kobayashi](https://arxiv.org/abs/2601.09217). The paper-AST language and related semantic/SMT support retain the `PaperCore` namespace. Only the support modules required by HLS are distributed here. The earlier paper's measured FPGA speedups do not transfer to this backend.

Verified HLS itself is not a new claim: see [Vericert](https://github.com/ymherklotz/vericert). This prototype also does not claim superiority over other Lean hardware-verification work such as [Graphiti](https://vca.epfl.ch/papers/asplos26_fvo.pdf). These references identify context, not an exhaustive comparison.
