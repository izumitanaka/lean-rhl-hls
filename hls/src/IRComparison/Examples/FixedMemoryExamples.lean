import IRComparison.Frontend.LeanHLSCommand

namespace IRComparison.FixedMemoryExamples
open HybridWord

/-- Regions exist before execution. These declarations also supply RTL layout. -/
def buffers : FixedMemory.Declarations := #[(0,4),(1,4),(2,4)]

def independent (s : HybridWord.State) : Option HybridWord.State := do
  let t ← s.copy 1 0 4
  let t ← t.write 0 0 99
  let t ← t.write 1 1 77
  t.copy 2 1 4
hls_fixed_program independent using buffers as independentHLS

def repeated (s : HybridWord.State) : Option HybridWord.State := do
  let mut t := s
  for i in HybridWord.range 0 3 1 do
    t ← t.copy 1 0 4
    let v ← (t.arrays 1)[i.toNat]?
    t ← t.write 0 i (v+1)
  return t
hls_fixed_program repeated using buffers as repeatedHLS

def swap (s : HybridWord.State) : Option HybridWord.State := do
  let t ← s.copy 2 0 4
  let t ← t.copy 0 1 4
  t.copy 1 2 4
hls_fixed_program swap using buffers as swapHLS

def nested (s : HybridWord.State) : Option HybridWord.State := do
  let mut t := s
  for i in HybridWord.range 1 (-1) (-1) do
    for j in HybridWord.range 0 2 1 do
      let v ← (t.arrays 0)[i.toNat]?
      if v != 0 then
        t ← t.copy 1 0 4
      else
        t ← t.copy 1 2 4
      t ← t.write 1 j (i+j)
  return t
hls_fixed_program nested using buffers as nestedHLS

def selfCopy (s : HybridWord.State) : Option HybridWord.State := do
  s.copy 0 0 4
hls_fixed_program selfCopy using buffers as selfHLS

def longRepeated (s : HybridWord.State) : Option HybridWord.State := do
  let mut t := s
  for i in HybridWord.range 0 1000 1 do
    t ← t.copy 1 0 4
    let v ← (t.arrays 1)[0]?
    t ← t.write 0 0 (v+i)
  return t
hls_fixed_program longRepeated using buffers as longHLS

def shortRepeated (s : HybridWord.State) : Option HybridWord.State := do
  let mut t := s
  for i in HybridWord.range 0 3 1 do
    t ← t.copy 1 0 4
    let v ← (t.arrays 1)[0]?
    t ← t.write 0 0 (v+i)
  return t
hls_fixed_program shortRepeated using buffers as shortHLS

/-- Equivalent BV32 type spellings must not turn a captured value into a
re-read of an old State after an update. -/
def explicitWidth (s : HybridWord.State) : Option HybridWord.State := do
  let old : BitVec 32 := s.regs 0
  let t := s.set 0 (old+1)
  pure (t.set 1 old)
hls_fixed_program explicitWidth using buffers as explicitWidthHLS

example : ∃ c, explicitWidthHLS.compile [] 4096 .rolled = .ok c :=
  explicitWidthHLS.generates [] 4096 .rolled rfl

def undeclared (s : HybridWord.State) : Option HybridWord.State := s.copy 3 0 4
hls_program undeclared as undeclaredHLS
example : FixedMemory.declared buffers undeclaredHLS.wordBody = false := by decide

def wrongLength (s : HybridWord.State) : Option HybridWord.State := s.copy 1 0 3
hls_program wrongLength as wrongLengthHLS
example : FixedMemory.declared buffers wrongLengthHLS.wordBody = false := by decide

example : FixedMemory.unique #[(0,4),(0,4)] = false := by decide
example : FixedMemory.declared buffers
    (.branch (.lit 0) (.copy 3 0 4) .skip) = false := by decide
example : FixedMemory.declared buffers (.repeat 0 (.copy 1 0 3)) = false := by decide

/-- error: fixed-memory input uses an undeclared array or a copy length different from its source/destination declarations -/
#guard_msgs in
hls_fixed_program undeclared using buffers as rejectedUndeclared

/-- error: fixed-memory input uses an undeclared array or a copy length different from its source/destination declarations -/
#guard_msgs in
hls_fixed_program wrongLength using buffers as rejectedLength

def duplicateBuffers : FixedMemory.Declarations := #[(0,4),(0,4)]
/-- error: fixed-memory declarations contain duplicate array identifiers -/
#guard_msgs in
hls_fixed_program selfCopy using duplicateBuffers as rejectedDuplicate

/-- A State alias is NOT an explicit copy into a declared destination. -/
def hiddenSnapshot (_i _x _y : Word) (s : HybridWord.State) : Option HybridWord.State := do
  let old := s
  let t ← s.write 0 0 99
  let v ← (old.arrays 0)[0]?
  t.write 1 0 v

/-- error: BV32 frontend could not construct the formal source connection. No unproved output was generated. -/
#guard_msgs in
hls_word hiddenSnapshot as rejectedSnapshot

def allocates (_i _x _y : Word) (s : HybridWord.State) : Option HybridWord.State :=
  some { s with arrays := fun a => if a = 3 then Array.replicate 4 0 else s.arrays a }

/-- error: BV32 frontend could not construct the formal source connection. No unproved output was generated. -/
#guard_msgs in
hls_word allocates as rejectedAllocation

/-- Region identifiers need not contain zero or be consecutive/sorted. -/
def sparseBuffers : FixedMemory.Declarations := #[(11,4),(7,4)]
def sparseCopy (s : HybridWord.State) : Option HybridWord.State := s.copy 11 7 4
hls_fixed_program sparseCopy using sparseBuffers as sparseHLS

def noBuffers : FixedMemory.Declarations := #[]
def scalarOnly (s : HybridWord.State) : Option HybridWord.State := pure (s.set 0 42)
hls_fixed_program scalarOnly using noBuffers as scalarHLS

def emptyBuffer : FixedMemory.Declarations := #[(7,0)]
def emptyCopy (s : HybridWord.State) : Option HybridWord.State := s.copy 7 7 0
hls_fixed_program emptyCopy using emptyBuffer as emptyHLS

/-- Capturing a scalar value is permitted; it is not a hidden array snapshot. -/
def capturedScalar (s : HybridWord.State) : Option HybridWord.State := do
  let v := s.regs 0
  let t := s.set 0 (v+1)
  pure (t.set 1 v)
hls_fixed_program capturedScalar using noBuffers as capturedHLS

def capturedLoop (s : HybridWord.State) : Option HybridWord.State := do
  let mut t := s
  for _i in HybridWord.range 0 3 1 do
    let v := t.regs 0
    t := t.set 0 (v+1)
    t := t.set 1 (t.regs 1+v)
  return t
hls_fixed_program capturedLoop using noBuffers as capturedLoopHLS

end IRComparison.FixedMemoryExamples
