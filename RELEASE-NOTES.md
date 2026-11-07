# v0.1.0 — Prototype baseline

Author: Izumi Tanaka.

This baseline records the implemented connection from supported Lean/BV32 kernel definitions, through hybrid-IR buffer insertion and FIFO/memory selection, to sequential SystemVerilog generation and its defined text semantics.

- General transformation and composition proofs, with exact scope and trust boundaries in the [technical note](docs/TECHNICAL-NOTE.md).
- Finite sequential backend, including reset/configuration/start and readout.
- 844 audited declarations; 45 regression cases; 30 distinct synthesized RTL designs in the saved baseline.
- Source, scripts, pinned dependencies, citation metadata, and reproduction instructions.
- The paper-AST reference library and imperative/functional comparison paths are retained.

This is a research prototype. Parallel scheduling, synchronous RAM, multi-cycle operators, arbitrary Lean input, and full IEEE SystemVerilog semantics are outside this release. No DOI or project license has been assigned. See [publication validation](evidence/publication/validation.json) for checks rerun on the packaged source.
