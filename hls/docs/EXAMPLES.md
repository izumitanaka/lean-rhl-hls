# Examples at a glance

For individual, runnable program files with their generated RTL, start in [`examples/`](../examples/README.md). The catalog below links to broader demonstration and regression suites.

Start with the first two examples to see ordinary Lean input, emitted RTL, and the difference between buffer insertion and FIFO conversion. Each row links to the source and a runnable check.

**Entry labels:** *Whole function* includes loops in the Lean input; *explicit stages* uses Lean processing bodies with separately supplied ranges and stage order; *circuit IR* starts after the frontend and demonstrates a backend transformation.

| Example | Input / entry | What to look for | Source and runnable check |
|---|---|---|---|
| **Increment an array** | Whole function: read five words and add one | `[3,6,9,12,15]` becomes `[4,7,10,13,16]`; complete Lean function → SystemVerilog | [`increment`](../scripts/intro-example.lean); run **A** below |
| **Producer → three-point filter** | Explicit stages: produce B, then read `B[i], B[i+1], B[i+2]` | Three held values reduce nine consumer reads to five; B becomes a FIFO; output `[7,10,13,0,0]` | [`producer` / `filter`](../scripts/intro-example.lean); run **A** |
| **Copy and swap fixed arrays** | Whole function: copy into predeclared buffers, then update or swap them | Copies preserve independent contents; swapping `[10,20,30,40]` and `[5,6,7,8]` uses a declared temporary array | [`independent`, `swap`, `repeated`](../src/IRComparison/Examples/FixedMemoryExamples.lean); run **B** |
| **Nested loops and branching** | Whole function: reverse outer traversal, inner loop, conditional whole-array copy | Both branch outcomes and subsequent element updates are checked against the original Lean computation | [`nested`](../src/IRComparison/Examples/FixedMemoryExamples.lean); run **B** (`nested-mixed` / `nested-true`) |
| **Arithmetic and irregular accesses** | Explicit kernels: AXPY, FIR4, prefix sum, dot product, histogram, gather, matrix multiplication, stencil and in-place recurrence | BV32 arithmetic, loop-carried dependence, multiple arrays and data-dependent indices; these are not all FIFO conversion examples | [Lean definitions](../src/IRComparison/Examples/HLSBenchmarks.lean); [workload sizes and runner](BENCHMARKS.md) |
| **Choose FIFO or retain memory** | Explicit stages: adjacent/nonadjacent producers and consumers, reverse traversal, stride two | FIFO decisions are checked per array; public intermediate arrays, intervening reads and incompatible order can require memory retention | [`rule-vcg.lean`](../scripts/rule-vcg.lean); run **C** |
| **Overlap loop iterations** | Circuit IR: a copy/gather loop; also a separate native filter check | Checked overlap reduces cycles for suitable loops; conflicting in-place accesses retain the loop; output and failure behavior are compared | [`pipelining-rolled.lean`](../scripts/pipelining-rolled.lean); run **D** |
| **Failed and unselected reads** | Explicit stages from ordinary Lean bodies | An unused invalid read still fails; an invalid read in an unselected branch is not observed | [`unused` / `conditionalRead`](../scripts/shared-normal-hls.lean); [run instructions](REPRODUCING.md#emitted-rtl-restart-and-synthesis) |

The pipeline-overlap row contains hand-written circuit schedules: it demonstrates the backend rule, not automatic discovery of those schedules from a whole Lean function. The shared-expression growth cases in the last script also start at BV32 IR; its invalid-read cases use ordinary Lean definitions.

## Run a selected group

Run from `hls/` after `lake build IRComparison IRComparison.Tests`. Use the pinned Lean toolchain. The Python RTL checks require `iverilog` and `vvp`; group A also uses Yosys. Groups A and C require Z3.

**A — introductory input-to-RTL examples**

```sh
lake env lean --run scripts/intro-example.lean
python3 scripts/check-intro-example.py
```

Writes `increment.sv`, `filter.sv`, IR dumps and check results to `artifacts/intro-example/`. The [walkthrough](WALKTHROUGH.md) explains the transformations and actual RTL interface.

**B — fixed-array copies, branches and loops**

```sh
lake env lean --run scripts/fixed-memory.lean
python3 scripts/check-fixed-memory.py
```

Writes RTL and checks under `artifacts/fixed-memory/`. The runner compares all three arrays, including both sides of copies. Its 1,000-iteration case checks generation/storage shape only, rather than simulating all iterations.

**C — routing decisions and buffer reuse**

```sh
lake env lean --run scripts/rule-vcg.lean
python3 scripts/check-rule-vcg.py
```

Writes selected policies, SMT records and RTL under `artifacts/rule-vcg/`. The billion-iteration case checks symbolic plan/control shape only; it does not execute a billion iterations or generate their full memory hardware.

**D — loop overlap without unrolling**

```sh
lake env lean --run scripts/pipelining-rolled.lean
python3 scripts/check-pipelining-rolled.py
```

Writes RTL under `artifacts/rolled-pipeline/` and prints before/after cycle counts. The cycle comparisons are functional simulation results, not a measurement of physical clock frequency.

These examples supplement the [general proofs](PROOF-MAP.md). For the supported input language, see [the input specification](LEAN-ENTRY.ja.md); for benchmark provenance and measurement limits, see [workload scope](BENCHMARKS.md).
