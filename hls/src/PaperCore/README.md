# PaperCore: RHL semantic and analysis support

`PaperCore` is named after the **core language of [Relational Hoare Logic for High-Level Synthesis of Hardware Accelerators](https://arxiv.org/abs/2601.09217)** (Tanaka, Sakayori, Takamaeda-Yamazaki and Kobayashi, ESOP 2026). The namespace originated in the Lean formalization of that language and its relational memory/stream semantics.

In this HLS implementation, these modules provide:

- The core language, operational semantics and state-correspondence lemmas used by the analyses.
- Array-access and sliding-window analysis, through `PaperCore.WindowAnalysis`.
- Index-sequence reasoning and SMT request/response support, through `PaperCore.IndexSequenceSMT`.

The HLS memory passes import these definitions and proofs. They are built as part of the HLS package with `lake build IRComparison IRComparison.Tests`.

The HLS-specific hybrid-IR transformation rules and RTL correctness proofs build on this support layer; they are implemented separately in `IRComparison`. See the [technical note](../../docs/TECHNICAL-NOTE.md#design-intent-and-relationship-to-the-paper) for the inherited ideas and the additions in this compiler.
