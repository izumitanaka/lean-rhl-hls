# Dependency provenance

| Component | Source / version | Role |
| --- | --- | --- |
| Lean | `leanprover/lean4:v4.29.0` | Language implementation and proof kernel |
| Lean4Lean | [digama0/lean4lean](https://github.com/digama0/lean4lean), commit `3dc52e0cd8a218e09de9ead031f52a2675734fe7` | Formal representations and lower-level typing/computation rules |
| Batteries | [leanprover-community/batteries](https://github.com/leanprover-community/batteries), commit `756e3321fd3b02a85ffda19fef789916223e578c` | Transitive Lean dependency |
| PaperCore | Included in `hls/src/PaperCore/` | 14 transitive support modules for HLS buffer analysis, index sequences and SMT; not the full paper-AST compiler |
| NativeRHL expression analysis | Included in `hls/src/NativeRHL/ExprAnalysis.lean` | Shared expression-analysis helper retained from the earlier direct-Lean prototype; other common components are in the current IRComparison tree |

Lean4Lean and Batteries are fetched by Lake, not vendored into this publication copy. Their pinned checkouts carry Apache-2.0 license files; see the upstream repositories for their notices. Toolchain and package revisions are recorded in the committed `lean-toolchain` and `lake-manifest.json` files.

Z3, Icarus Verilog, and Yosys are separately installed tools. They are not included in this repository. The project itself has no designated license yet; the dependency notices do not assign a license to the project code.

Prior work is credited in the [technical note](TECHNICAL-NOTE.md), and workload origins/adaptations are documented in [BENCHMARKS](BENCHMARKS.md).
