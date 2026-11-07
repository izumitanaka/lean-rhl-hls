import IRComparison.Frontend.LeanWordCommand

/-! Small BV32 HLS workloads. These are algorithm-pattern adaptations, not
unmodified runs of MachSuite. See HLS-BENCHMARKS.ja.md for provenance and scope.
Every kernel enters through an ordinary Lean definition and hls_word. -/
namespace IRComparison.HLSBenchmarks
open HybridWord
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def axpy (i alpha _y : Word) (s : HybridWord.State) : Option HybridWord.State := do
  let a ← (s.arrays 0)[i.toNat]?
  let b ← (s.arrays 1)[i.toNat]?
  s.write 2 i (alpha*a+b)
hls_word axpy as axpyCode

def fir4 (i _x _y : Word) (s : HybridWord.State) : Option HybridWord.State := do
  let a ← (s.arrays 0)[i.toNat]?
  let b ← (s.arrays 0)[(i+1).toNat]?
  let c ← (s.arrays 0)[(i+2).toNat]?
  let d ← (s.arrays 0)[(i+3).toNat]?
  s.write 1 i (a+2*b+3*c+4*d)
hls_word fir4 as firCode

def prefixSum (i _x _y : Word) (s : HybridWord.State) : Option HybridWord.State := do
  let a ← (s.arrays 0)[i.toNat]?
  if i != 0 then do
    let prior ← (s.arrays 1)[(i-1).toNat]?
    s.write 1 i (prior+a)
  else s.write 1 i a
hls_word prefixSum as prefixCode

def dot (i _x _y : Word) (s : HybridWord.State) : Option HybridWord.State := do
  let a ← (s.arrays 0)[i.toNat]?
  let b ← (s.arrays 1)[i.toNat]?
  let acc ← (s.arrays 2)[0]?
  s.write 2 0 (acc+a*b)
hls_word dot as dotCode

def histogram (i _x _y : Word) (s : HybridWord.State) : Option HybridWord.State := do
  let key ← (s.arrays 0)[i.toNat]?
  let count ← (s.arrays 1)[(key-(key/4)*4).toNat]?
  s.write 1 (key-(key/4)*4) (count+1)
hls_word histogram as histogramCode

def gather (i _x _y : Word) (s : HybridWord.State) : Option HybridWord.State := do
  let key ← (s.arrays 0)[i.toNat]?
  let value ← (s.arrays 1)[key.toNat]?
  s.write 2 i value
hls_word gather as gatherCode

/-- One output of a row-major 2×2 matrix product; the two-term reduction is
explicit. This keeps the source within the existing supported frontend. -/
def gemm2 (i _x _y : Word) (s : HybridWord.State) : Option HybridWord.State := do
  let a0 ← (s.arrays 0)[((i/2)*2).toNat]?
  let a1 ← (s.arrays 0)[((i/2)*2+1).toNat]?
  let b0 ← (s.arrays 1)[((i-(i/2)*2)).toNat]?
  let b1 ← (s.arrays 1)[(2+(i-(i/2)*2)).toNat]?
  s.write 2 i (a0*b0+a1*b1)
hls_word gemm2 as gemmCode

/-- 3×3 weighted stencil on a 4×4 image, four valid outputs packed in row
order. Fixed coefficients [1,2,1;2,4,2;1,2,1], without normalization. -/
def stencil3 (i _x _y : Word) (s : HybridWord.State) : Option HybridWord.State := do
  let base := (i/2)*4+(i-(i/2)*2)
  let a ← (s.arrays 0)[base.toNat]?
  let b ← (s.arrays 0)[(base+1).toNat]?
  let c ← (s.arrays 0)[(base+2).toNat]?
  let d ← (s.arrays 0)[(base+4).toNat]?
  let e ← (s.arrays 0)[(base+5).toNat]?
  let f ← (s.arrays 0)[(base+6).toNat]?
  let g ← (s.arrays 0)[(base+8).toNat]?
  let h ← (s.arrays 0)[(base+9).toNat]?
  let k ← (s.arrays 0)[(base+10).toNat]?
  s.write 1 i (a+2*b+c+2*d+4*e+2*f+g+2*h+k)
hls_word stencil3 as stencilCode

def replaceZero (i replacement _y : Word) (s : HybridWord.State) : Option HybridWord.State := do
  let value ← (s.arrays 1)[i.toNat]?
  if value != 0 then s.write 2 i value else s.write 2 i replacement
hls_word replaceZero as replaceZeroCode

/-- In-place recurrence: subsequent iterations observe the preceding write. -/
def recurrence (i _x _y : Word) (s : HybridWord.State) : Option HybridWord.State := do
  let value ← (s.arrays 0)[i.toNat]?
  if i != 0 then do
    let prior ← (s.arrays 0)[(i-1).toNat]?
    s.write 0 i (prior+2*value)
  else s.write 0 i (2*value)
hls_word recurrence as recurrenceCode

end IRComparison.HLSBenchmarks
