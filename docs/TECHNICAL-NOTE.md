# Lean RHL HLS: Verified Memory Transformations and a Sequential RTL Backend

**Izumi Tanaka**

Technical note for prototype baseline **v0.1.0**, prepared 2026-11-07.

This note records the concrete implementation and theorem interfaces available in this baseline. It is not a peer-reviewed publication or a claim of being the first verified HLS compiler.

## 1. Implemented contribution

The prototype connects three parts: supported ordinary Lean kernel definitions, memory-representation transformations motivated by relational Hoare logic, and a sequential RTL backend. The central design uses a hybrid computation IR that separates value computation from ordered reads, writes, state changes, and communication. Buffer insertion and FIFO selection operate before cycle-level realization.

The artifact records the following implemented combination:

1. A Lean input connection that retains the original kernel function and constructs correspondence evidence using general frontend lemmas.
2. General proofs for buffer insertion and consistent whole-array FIFO/memory decisions, with fallback when an optimization cannot be established.
3. Composition with a finite sequential circuit and an actual SystemVerilog string emitter, through a specified text semantics and the startup/readout interface.

These are claims about this implementation. Novelty relative to the full literature requires more detailed comparison than the fact that it uses Lean. The imperative and functional comparison paths are retained, but the current hardware baseline uses the BV32 hybrid path.

## 2. Source and intermediate representations

The frontend accepts a supported subset of ordinary Lean definitions. The main examples use `BitVec 32`, an explicit state API for finite arrays and registers, `Option` for failure, local bindings, reads and writes, branches, and supported iterations. A separate kernel record supplies static iteration and array metadata. The frontend does not automatically accept every Lean definition or infer an arbitrary whole program's kernel decomposition.

The `hls_word` command constructs a BV32 body and its source correspondence. A `HybridWord.Kernel` retains both the original function and the proof relating it to that body. A list of such kernels defines the source computation used by the downstream theorem. Data arithmetic follows the encoded BV32 operations; sizes, trip counts, and logical iteration ordinals are separate metadata.

The hybrid IR separates value expressions from ordered effects. A pure value expression cannot silently consume a FIFO token. Reads, writes, and communication have explicit sequencing and failure behavior. Conversion to control and circuit representations adds execution order, storage, widths, and clock transitions; these lower representations have the semantics needed to state their own correctness.

## 3. Buffer insertion and communication

For a sliding filter, a conceptual transformation is:

```text
before:
  x0 ← read a[i]
  x1 ← read a[i+1]
  x2 ← read a[i+2]
  write b[i] (x0+x1+x2)

after buffer insertion:
  initialize a window once
  repeat:
    write b[i] (window[0]+window[1]+window[2])
    retain reusable values and refill for the next iteration
```

The displayed code is illustrative; the implementation handles supported widths, gaps, and strides through general analyses and transformation functions. Applicability conditions are checked. Unsafe speculative reads are not justified by merely treating all branches as executed.

Buffer selection precedes communication selection. A useful window may remain even if the backing array must remain in memory. FIFO selection checks the use of an array across the program rather than making incompatible local choices at individual reads. It accounts for order and the relation between logical array indices and queue values. Where required, explicitly placed FIFO reads discard unused tokens. There is no implicit `peek` cache.

Not every array can be converted. For example, an order mismatch may require memory, and general multiple-producer/multiple-consumer uses exceed the current FIFO analysis. Successful compilation and successful optimization are distinct: retaining memory is a legitimate outcome.

The general PaperCore SMT interface states a solver-reply soundness premise. The current HLS affine-sequence path additionally rechecks candidate sequence equivalence with a verified arithmetic predicate (`CompactSequence.equivalent_correct` and `accept`). SAT supplies candidates; UNSAT is not used as proof that a counterexample is absent. A failed or unavailable candidate does not authorize a transformation. The combined compiler can use independently verified static alternatives.

## 4. Sequential realization and theorem scope

The backend realizes control as a single sequential controller. Arrays and FIFOs occupy finite register banks. Reads and arithmetic are combinational; state updates occur at clock edges. The compiler checks storage coverage, capacities, and intermediate-width conditions, and the proofs connect these checks to execution. This baseline does not implement synchronous block RAM, multi-cycle operators, or parallel scheduling.

The principal text-level theorem is:

`IRComparison.Circuit.SystemVerilog.emitted_text_reset_config_start_readout`

In simplified form, it states that, for an accepted kernel plan and successful circuit compilation and emission, under the layout, readiness, and output-interface premises, there is a finite number of compute cycles after reset/configuration/start such that:

- the generated text's execution reaches `done` with the controller idle;
- if the source kernel sequence succeeds, the error signal is clear and readout agrees with the specified source-state observation;
- if the source sequence fails, the error signal is set.

The theorem is parameterized by the source kernels and inputs; it is not a theorem only about the benchmark examples. Its exact statement is in [PreparationSound.lean](../hls/src/IRComparison/Circuit/SystemVerilog/PreparationSound.lean). Public observations, initial preparation, and the protocol are specified there and in its dependencies. The theorem does not assert equality of every internal hardware cell with a source variable.

The text semantics is a defined two-state SystemVerilog subset. The printing/parsing connection is proved for the generated language. This does not constitute a proof of the full IEEE four-state/event semantics or of an external simulator, synthesizer, host driver, or FPGA implementation.

## 5. Frontend and trust boundary

The frontend uses pinned Lean4Lean representations and lower-level typing/computation rules, together with provenance facts about the imported Lean declarations. The implementation of Lean itself is trusted. This work does not prove the operational correctness of the Lean executable or automatically establish an ordering theorem for the complete imported environment.

General lemmas justify the frontend's supported proof-construction steps. It can also register generated correspondence theorems for individual definitions. Those generated theorems are useful artifacts; they are not a replacement for the transformation functions' general correctness theorems.

`Audit.lean` checks 844 selected declarations, including proof-construction functions and the main compilation connections. Its allowed logical dependencies are `propext`, `Classical.choice`, and `Quot.sound`; unexpected dependencies, including `sorryAx`, fail the audit. This is a dependency check for the audited roots, not a claim that every theorem in every upstream dependency has been completed.

## 6. Relation to prior work

The earlier [RHL work by Tanaka, Sakayori, Takamaeda-Yamazaki, and Kobayashi](https://arxiv.org/abs/2601.09217) develops a relational translation framework for buffer insertion and stream processing, evaluated with an existing HLS compiler and FPGA. This artifact retains the paper-AST reference separately, mechanizes transformation components, and develops the Lean-input/hybrid-IR and sequential RTL connections. It does not transfer that paper's measured FPGA speedups to this backend.

[Vericert](https://github.com/ymherklotz/vericert) already provides a verified C-to-Verilog HLS flow based on CompCert and Coq; see [Formal Verification of High-Level Synthesis](https://doi.org/10.1145/3485494). Therefore, verified HLS itself is not a new claim here. The design focus of this prototype is the connection of Lean kernel specifications, memory-representation transformations, and explicit computation/communication structure.

[Graphiti](https://vca.epfl.ch/papers/asplos26_fvo.pdf) is a Lean 4 framework for reasoning about and transforming dataflow circuits, including out-of-order execution. This prototype's backend is sequential and its present emphasis is higher-level memory transformations. No superiority over Graphiti's circuit transformations or guarantees is claimed.

These comparisons describe scope and emphasis, not a comprehensive feature matrix or a proof that another system cannot express the same transformations.

## 7. Evidence and remaining work

The baseline was built with Lean 4.29.0. The audit checks 844 declarations. The regression harness checks 45 execution cases, including 11 small workload families with nominal/boundary inputs, and simulates the emitted RTL with Icarus. Yosys synthesis covers 30 distinct RTL designs; identical text is synthesized once per run. The source expectations for the added workloads are independently generated in Python.

The workload suite is small and adapted. It is not a full MachSuite port, a performance comparison with commercial HLS, or a placed-and-routed FPGA evaluation. Measurements are reported with their scope in [BENCHMARKS](BENCHMARKS.md).

Future work includes broader frontend syntax and metadata inference, richer communication choices, synchronous memories, multi-cycle arithmetic, and parallel scheduling. The release does not claim these as implemented. The present source and proof boundaries are summarized in the [proof map](PROOF-MAP.md).
