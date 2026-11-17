import IRComparison.Examples.PipeliningExamples

namespace IRComparison.PipelineWorkloads
open HybridWord

/-- Data-dependent read/modify/write; repeated keys are intentional. -/
def histogram (i _x _y : Word) (s : HybridWord.State) : Option HybridWord.State := do
  let key ← (s.arrays 0)[i.toNat]?
  let old ← (s.arrays 1)[key.toNat]?
  s.write 1 key (old + 1)

hls_word histogram as histogramCode

/-- Stable conditional extraction into an array plus an output length.
This is the supported native interface, not a source-level FIFO extension. -/
def compactThreshold (i threshold _y : Word) (s : HybridWord.State) : Option HybridWord.State := do
  let value ← (s.arrays 0)[i.toNat]?
  if value > threshold then
    let next ← s.write 1 (s.regs 0) value
    pure (next.set 0 (s.regs 0 + 1))
  else pure s

/-- The current frontend recognizes nonzero predicates. Keep the threshold
specification above; do not silently claim it was compiled. -/
def compactNonzero (i _x _y : Word) (s : HybridWord.State) : Option HybridWord.State := do
  let value ← (s.arrays 0)[i.toNat]?
  if value != 0 then
    let next ← s.write 1 (s.regs 0) value
    pure (next.set 0 (next.regs 0 + 1))
  else pure s

hls_word compactNonzero as compactCode

end IRComparison.PipelineWorkloads
