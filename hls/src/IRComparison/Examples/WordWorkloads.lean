import IRComparison.Frontend.LeanWordCommand

namespace IRComparison.WordWorkloads
open HybridWord
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

namespace Window
def filter (i _x _y : Word) (s : HybridWord.State) : Option HybridWord.State := do
  let a ← (s.arrays 0)[(i).toNat]?
  let b ← (s.arrays 0)[(i+1).toNat]?
  let c ← (s.arrays 0)[(i+2).toNat]?
  s.write 1 i ((a+b+c)/3)
hls_word filter as filterCode

def filterAlt (i _x _y : Word) (s : HybridWord.State) : Option HybridWord.State := do
  let a ← (s.arrays 0)[(63-i).toNat]?
  let b ← (s.arrays 0)[(62-i).toNat]?
  let c ← (s.arrays 0)[(61-i).toNat]?
  s.write 1 i ((a+b+c)/3)
hls_word filterAlt as filterAltCode

def filterSkip (i _x _y : Word) (s : HybridWord.State) : Option HybridWord.State := do
  let a ← (s.arrays 0)[(2*i).toNat]?
  let b ← (s.arrays 0)[(2*i+1).toNat]?
  let c ← (s.arrays 0)[(2*i+2).toNat]?
  s.write 1 i ((a+b+c)/3)
hls_word filterSkip as filterSkipCode

def filterDilated (i _x _y : Word) (s : HybridWord.State) : Option HybridWord.State := do
  let a ← (s.arrays 0)[(2*i).toNat]?
  let b ← (s.arrays 0)[(2*i+2).toNat]?
  let c ← (s.arrays 0)[(2*i+4).toNat]?
  s.write 1 i ((a+b+c)/3)
hls_word filterDilated as filterDilatedCode

def filterDilatedAlt (i _x _y : Word) (s : HybridWord.State) : Option HybridWord.State := do
  let a ← (s.arrays 0)[((31-i)*2).toNat]?
  let b ← (s.arrays 0)[((30-i)*2).toNat]?
  let c ← (s.arrays 0)[((29-i)*2).toNat]?
  s.write 1 i ((a+b+c)/3)
hls_word filterDilatedAlt as filterDilatedAltCode

def filterDilatedRev (i _x _y : Word) (s : HybridWord.State) : Option HybridWord.State := do
  let a ← (s.arrays 0)[(i).toNat]?
  let b ← (s.arrays 0)[(i+2).toNat]?
  let c ← (s.arrays 0)[(i+4).toNat]?
  s.write 1 i ((a+b+c)/3)
hls_word filterDilatedRev as filterDilatedRevCode

end Window

namespace Global
def produceA (i _x _y : Word) (s : HybridWord.State) : Option HybridWord.State := s.write 1 i (i*i)
def produceB (i _x _y : Word) (s : HybridWord.State) : Option HybridWord.State := s.write 5 i (i+10)
def marker (_i _x _y : Word) (s : HybridWord.State) : Option HybridWord.State := s.write 3 0 7
def readMarker (_i _x _y : Word) (s : HybridWord.State) : Option HybridWord.State := do
  let v ← (s.arrays 1)[0]?
  s.write 3 0 v

def consumeA (i _x _y : Word) (s : HybridWord.State) : Option HybridWord.State := do
  let v ← (s.arrays 1)[i.toNat]?
  s.write 2 i v

def consumeB (i _x _y : Word) (s : HybridWord.State) : Option HybridWord.State := do
  let v ← (s.arrays 5)[i.toNat]?
  s.write 6 i v

def readFuture (i _x _y : Word) (s : HybridWord.State) : Option HybridWord.State := do
  let v ← (s.arrays 2)[i.toNat]?
  s.write 1 i (v+1)
def finalConsumer (i _x _y : Word) (s : HybridWord.State) : Option HybridWord.State := do
  let v ← (s.arrays 2)[i.toNat]?
  s.write 6 i v
hls_word readFuture as earlyReader
hls_word finalConsumer as finalSink

hls_word produceA as producerA
hls_word produceB as producerB
hls_word marker as independent
hls_word readMarker as observing
hls_word consumeA as consumerA
hls_word consumeB as consumerB

end Global

end IRComparison.WordWorkloads
