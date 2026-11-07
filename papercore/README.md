# PaperCore

PaperCore is the paper-AST RHL reference implementation and a source dependency of the [current HLS compiler](../hls/README.md). Its integer source semantics and theorem premises should not be confused with the BV32 Lean-input path.

The complete library is in `src/PaperCore`; shared SMT infrastructure is in `src/PaperCore/SMT`. The public paper-AST compiler entry is `CertifiedPipeline.compileBuffered`; its correctness interfaces are `CertifiedPipeline.forward` and `CertifiedPipeline.backward`. The paper-level generic SMT path has an explicit solver-response soundness premise. The HLS affine candidate checker has a separate, stronger check described in the technical note.

```sh
lake build
lake env lean --run examples/Filter.lean
lake env lean --run scripts/check_paper_notation.lean
lake env lean --run scripts/check_paper_memory_window.lean
```

The filter is an example, not a restriction of the compiler's general theorem. The notation expands into the existing source AST. PaperCore's loop termination test is equality with the endpoint, not a sign-dependent less-than/greater-than test.

This release includes the reference library and selected self-contained regressions. The original OCaml compiler, manuscript sources, FPGA experiments, and external reference-input conversion scripts are not bundled.
