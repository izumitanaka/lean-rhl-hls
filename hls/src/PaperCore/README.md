# PaperCore: RHL semantic and analysis support

`PaperCore` is named after the **core language of the RHL paper** on memory-to-stream transformations by [Tanaka, Sakayori, Takamaeda-Yamazaki and Kobayashi](https://arxiv.org/abs/2601.09217). The namespace originated in the Lean formalization of that language and its relational memory/stream semantics.

In this HLS implementation, these modules provide:

- The core language, operational semantics and state-correspondence lemmas used by the analyses.
- Array-access and sliding-window analysis, through `PaperCore.WindowAnalysis`.
- Index-sequence reasoning and SMT request/response support, through `PaperCore.IndexSequenceSMT`.

The HLS memory passes import these definitions and proofs. They are built as part of the HLS package with `lake build IRComparison IRComparison.Tests`.
