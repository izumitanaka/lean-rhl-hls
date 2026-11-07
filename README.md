# Lean RHL HLS

**A Lean 4 research prototype for verified buffer/FIFO transformations and sequential RTL generation.**

Author: **Izumi Tanaka**. Prototype baseline: **v0.1.0**.

The main path accepts supported Lean kernel bodies with explicit kernel metadata, connects them to a hybrid computation IR, inserts reuse buffers, selects FIFO or memory communication for whole arrays, and generates sequential SystemVerilog. General correctness theorems cover the transformation functions and their composition, including the generated text's interpretation in a specified two-state SystemVerilog subset.

```text
supported Lean definitions + kernel metadata
    → BV32 hybrid computation IR
    → buffer insertion → whole-array FIFO / memory selection
    → sequential control → finite circuit → SystemVerilog text
```

Start with the [technical note](docs/TECHNICAL-NOTE.md) for the implemented research contribution and its scope, the [proof map](docs/PROOF-MAP.md) for the corresponding theorems, and the [reproduction guide](docs/REPRODUCING.md) to check the artifact. The note distinguishes this prototype from the earlier [RHL work](https://arxiv.org/abs/2601.09217) and from verified HLS systems such as Vericert and Graphiti.

## Example input

The existing [frontend examples](hls/src/IRComparison/Examples/WordFrontendExamples.lean) include this ordinary Lean definition:

```lean
import IRComparison.Frontend.LeanWordCommand
open IRComparison HybridWord

def filterPair (i _x _y : Word) (s : HybridWord.State) : Option HybridWord.State := do
  let a ← (s.arrays 0)[i.toNat]?
  let b ← (s.arrays 0)[(i+1).toNat]?
  s.write 1 i ((a+b)/2)

hls_word filterPair as generatedFilter
```

`Word` is `BitVec 32`. `hls_word` translates the supported body and constructs its source correspondence proof. Kernel metadata supplies iteration parameters, array sizes, and communication information. This is not a frontend for arbitrary Lean programs. See [the complete generation harness](hls/scripts/circuit-check.lean) for compilation, interface construction, RTL emission, and execution.

## Check the proofs

Install the Lean version specified in `hls/lean-toolchain` through elan, then:

```sh
cd hls
lake build
lake env lean Audit.lean
lake env lean --run scripts/circuit-validation.lean
```

For RTL generation, Icarus simulation, and Yosys synthesis:

```sh
python3 scripts/check-circuit.py --synth
```

The RTL command requires Python 3, `iverilog`, `vvp`, and `yosys` on `PATH`. Additional SMT regressions require `z3`. See [REPRODUCING](docs/REPRODUCING.md) for a smaller test and expected results.

## What is established

- Verified memory transformations with memory-preserving fallback when a candidate cannot be established.
- BV32 data operations, explicit reads and writes, structured control, and preservation of observable results and defined failure behavior.
- A sequential backend with finite storage and inferred intermediate widths.
- A connection from accepted kernel plans to generated SystemVerilog text, including reset, configuration, start, computation, and readout, under the stated interface and layout premises.
- A baseline audit of **844 declarations**, **45 execution cases**, and **30 distinct synthesized RTL designs**. The tests supplement the general proofs; they do not replace them. Saved results are in [evidence/baseline](evidence/baseline/).

The principal backend theorem is [`emitted_text_reset_config_start_readout`](hls/src/IRComparison/Circuit/SystemVerilog/PreparationSound.lean). Its premises, frontend trust boundary, and observation relation are described in the technical note.

This release does not claim arbitrary-Lean compilation, full IEEE SystemVerilog semantics, a verified host program or EDA toolchain, concurrent scheduling, synchronous RAM, multi-cycle arithmetic, or superiority to commercial HLS. Memories are finite register banks with combinational reads and clocked writes.

## Repository layout

| Directory | Purpose |
| --- | --- |
| `hls/` | Current compiler, general proofs, imperative/functional comparison paths, examples, and regression scripts |
| `papercore/` | Paper-AST RHL reference implementation and shared semantic/SMT infrastructure |
| `docs/` | Technical note, proof map, reproduction, and benchmark scope |
| `evidence/` | Baseline measurements and source checksums |

The Lean declaration namespace `IRComparison` is retained from the earlier comparison experiments. The current main path is the BV32 hybrid IR. Earlier standalone prototypes and unpublished manuscript history are not part of this repository.

## Citation and license status

Citation metadata is provided in [CITATION.cff](CITATION.cff). Cite a specific release or commit when identifying the implemented baseline. No DOI is assigned to this release.

A project license has not yet been designated. Dependency provenance is recorded in [DEPENDENCIES](docs/DEPENDENCIES.md).
