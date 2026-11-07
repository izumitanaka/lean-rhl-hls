import PaperCore.StagedCertified

namespace PaperCore.CertifiedPipeline
/-- Main entry: independently certified memory buffering, then FIFO selection. -/
abbrev compileBuffered := @StagedCertified.compileSource
abbrev compileBufferedWithPolicy := @StagedCertified.compileSourceWithPolicy
/-- Artifacts are indexed by the actual input AST, including inputs written
with `paper { ... }`. No restriction to a particular example or loop shape. -/
abbrev Artifact := @StagedCertified.Artifact

-- Public names for the existing general theorems, without duplicate proofs.
-- Both quantify over an arbitrary source and artifact. SolverSound remains
-- an explicit premise; neither theorem asserts that all inputs optimize.
export StagedCertified.Artifact (forward backward)

end PaperCore.CertifiedPipeline
