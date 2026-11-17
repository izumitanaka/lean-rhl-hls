# HLS implementation

This compiler connects ordinary Lean computations to SystemVerilog, including relational buffer/FIFO transformations based on [Relational Hoare Logic for High-Level Synthesis of Hardware Accelerators (ESOP 2026)](https://arxiv.org/abs/2601.09217). The [technical note](docs/TECHNICAL-NOTE.md) distinguishes the paper’s foundation from the Lean frontend, hybrid IR and proved RTL backend added here.

This directory is a self-contained Lean project. It includes the compiler, proofs, tests, support modules, pinned dependencies and user documentation. No sibling directory is required. Lean/Elan and external tools must still be installed; Lake fetches the pinned external Lean libraries.

```sh
lake build IRComparison IRComparison.Tests
lake env lean Audit.lean
lake env lean scripts/structural-frontend.lean
lake env lean scripts/check-current-entry.lean
```

- [Example programs and generated RTL](examples/README.md)
- [Input-to-RTL walkthrough](docs/WALKTHROUGH.md)
- [Build and RTL checks](docs/REPRODUCING.md)
- [Technical scope](docs/TECHNICAL-NOTE.md)
- [Proof map](docs/PROOF-MAP.md)
- [Input syntax and guarantees](docs/LEAN-ENTRY.ja.md) (Japanese)
- [IR syntax and transformation rules](docs/HLS-SYNTAX-RULES.ja.md) (Japanese)
- [Dependency provenance](docs/DEPENDENCIES.md)

[PaperCore](src/PaperCore/README.md) provides semantic, array-analysis and SMT support derived from the RHL paper’s core-language formalization. Generated files stay in local `artifacts/`.
