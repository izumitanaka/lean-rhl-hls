# HLS implementation

This directory is a self-contained Lean project. It includes the compiler, proofs, tests, support modules, pinned dependencies and user documentation. No sibling directory is required. Lean/Elan and external tools must still be installed; Lake fetches the pinned external Lean libraries.

```sh
lake build IRComparison IRComparison.Tests
lake env lean Audit.lean
lake env lean scripts/structural-frontend.lean
lake env lean scripts/check-current-entry.lean
```

- [Build and RTL checks](docs/REPRODUCING.md)
- [Technical scope](docs/TECHNICAL-NOTE.md)
- [Proof map](docs/PROOF-MAP.md)
- [Input syntax and guarantees](docs/LEAN-ENTRY.ja.md) (Japanese)
- [IR syntax and transformation rules](docs/HLS-SYNTAX-RULES.ja.md) (Japanese)
- [Dependency provenance](docs/DEPENDENCIES.md)

`src/PaperCore/` contains only required support, not a second compiler. Generated files stay in local `artifacts/`.
