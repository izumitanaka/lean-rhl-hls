import IRComparison.Frontend.LeanWordCommand

namespace IRComparison.WordFrontendExamples
open HybridWord

def writeSum (i x y : Word) (s : HybridWord.State) : Option HybridWord.State :=
  s.write 1 i (x+y)
hls_word writeSum as generatedSum

def filterPair (i _x _y : Word) (s : HybridWord.State) : Option HybridWord.State := do
  let a ← (s.arrays 0)[i.toNat]?
  let b ← (s.arrays 0)[(i+1).toNat]?
  s.write 1 i ((a+b)/2)
hls_word filterPair as generatedFilter

def repeatedWrite (i x y : Word) (s : HybridWord.State) : Option HybridWord.State := do
  let t ← s.write 1 i (x+y)
  t.write 1 i (x-y)
hls_word repeatedWrite as generatedWrites

def produce (i _x _y : Word) (s : HybridWord.State) : Option HybridWord.State := do
  let a ← (s.arrays 0)[i.toNat]?
  s.write 1 i (a+1)
hls_word produce as producer

def consume (i _x _y : Word) (s : HybridWord.State) : Option HybridWord.State := do
  let a ← (s.arrays 1)[i.toNat]?
  let b ← (s.arrays 1)[(i+1).toNat]?
  s.write 2 i (a+b)
hls_word consume as consumer

def conditional (i x y : Word) (s : HybridWord.State) : Option HybridWord.State :=
  if y != 0 then s.write 0 i x else pure s
hls_word conditional as conditionalCode

def loop (_i x y : Word) (s : HybridWord.State) : Option HybridWord.State := do
  let mut t := s
  for k in List.range y.toNat do
    t ← t.write 0 (BitVec.ofNat 32 k) x
  return t
hls_word loop as loopCode

def folded (_i x y : Word) (s : HybridWord.State) : Option HybridWord.State :=
  (List.range y.toNat).foldlM (fun t k => t.write 0 (BitVec.ofNat 32 k) x) s
hls_word folded as foldCode

def localArithmetic (i x y : Word) (s : HybridWord.State) : Option HybridWord.State :=
  let c := x+y
  s.write 0 i (-c*c)
hls_word localArithmetic as localCode

def captured (i _x _y : Word) (s : HybridWord.State) : Option HybridWord.State := do
  let a ← (s.arrays 0)[0]?
  let t ← s.write 0 0 (a+1)
  t.write 1 i a
hls_word captured as capturedCode

def indirect (i _x _y : Word) (s : HybridWord.State) : Option HybridWord.State := do
  let j ← (s.arrays 0)[i.toNat]?
  let v ← (s.arrays 1)[j.toNat]?
  s.write 2 i v
hls_word indirect as indirectCode

def rawBits (i x y : BitVec 32) (s : HybridWord.State) : Option HybridWord.State :=
  s.write 0 i (x+y)
hls_word rawBits as rawBitsCode

#print axioms generatedSum.wordBody_correct
#print axioms generatedFilter.wordBody_correct
#print axioms generatedWrites.wordBody_correct
#print axioms WordFrontend.Result.correct
#print axioms loopCode.wordBody_correct
#print axioms capturedCode.wordBody_correct
#print axioms HybridWord.program_finishes
end IRComparison.WordFrontendExamples
