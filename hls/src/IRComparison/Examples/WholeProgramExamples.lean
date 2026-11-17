import IRComparison.Frontend.LeanHLSCommand

namespace IRComparison.WholeProgramExamples
open HybridWord

/-- Two source loops; no separately specified order or outer iteration. -/
def filter (s : HybridWord.State) : Option HybridWord.State := do
  let mut t := s
  for i in HybridWord.range 0 8 1 do
    let v ← (t.arrays 0)[i.toNat]?
    t ← t.write 1 i (v+1)
  for i in HybridWord.range 6 (-1) (-1) do
    let a ← (t.arrays 1)[i.toNat]?
    let b ← (t.arrays 1)[(i+1).toNat]?
    t ← t.write 2 i ((a+b)/2)
  return t
hls_program filter as filterHLS

def nested (s : HybridWord.State) : Option HybridWord.State := do
  let mut t := s
  for i in HybridWord.range 0 3 1 do
    for j in HybridWord.range 1 (-1) (-1) do
      let v ← (t.arrays 0)[i.toNat]?
      if v != 0 then
        t ← t.write 1 (i*2+j) (v+j+1)
      else
        t ← t.write 1 (i*2+j) 0
  return t
hls_program nested as nestedHLS

def ascending (s : HybridWord.State) : Option HybridWord.State := do
  let mut t := s
  for i in HybridWord.range 0 7 2 do
    let v ← (t.arrays 0)[i.toNat]?
    t ← t.write 1 i (v+1)
  return t
hls_program ascending as ascendingHLS

def descending (s : HybridWord.State) : Option HybridWord.State := do
  let mut t := s
  for i in HybridWord.range 6 (-1) (-2) do
    let v ← (t.arrays 0)[i.toNat]?
    t ← t.write 1 i (v+1)
  return t
hls_program descending as descendingHLS

def empty (s : HybridWord.State) : Option HybridWord.State := do
  let mut t := s
  for i in HybridWord.range 4 0 1 do
    let v ← (t.arrays 0)[99]?
    t ← t.write 1 i v
  return t
hls_program empty as emptyHLS

def wrapping (s : HybridWord.State) : Option HybridWord.State := do
  let mut t := s
  for i in HybridWord.range 4294967296 4294967298 1 do
    let v ← (t.arrays 0)[i.toNat]?
    t ← t.write 1 i (v+1)
  return t
hls_program wrapping as wrappingHLS

def failing (s : HybridWord.State) : Option HybridWord.State := do
  let mut t := s
  for i in HybridWord.range 7 10 1 do
    let v ← (t.arrays 0)[i.toNat]?
    t ← t.write 1 i v
  return t
hls_program failing as failingHLS

/-- Generation/shape check only: never execute this source loop in a test. -/
def large (s : HybridWord.State) : Option HybridWord.State := do
  let mut t := s
  for i in HybridWord.range 0 4294967297 1 do
    t := t.set 0 i
  return t
hls_program large as largeHLS

def small (s : HybridWord.State) : Option HybridWord.State := do
  let mut t := s
  for i in HybridWord.range 0 8 1 do
    t := t.set 0 i
  return t
hls_program small as smallHLS

end IRComparison.WholeProgramExamples
