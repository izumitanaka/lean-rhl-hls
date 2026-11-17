# PaperCore support library

This directory contains only the 14 PaperCore modules transitively required by the HLS compiler. It is not a second compiler distribution.

The two direct entry points are `PaperCore.WindowAnalysis` (buffer/access analysis) and `PaperCore.IndexSequenceSMT` (index sequences and SMT serialization/response support). Their semantic dependencies remain unchanged. Namespace and file contents are preserved so that HLS proofs continue to import the same declarations.

The standalone paper-AST compiler, its examples, scripts and audit are not included. Build this support library with `lake build`, or build it through the parent [HLS project](../hls/README.md).
