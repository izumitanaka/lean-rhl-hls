import IRComparison.Frontend.LeanHLSCommand

namespace IRComparison.CertifiedHLSExamples
open HybridWord Circuit CertifiedHLS

def filter (i _x _y : Word) (s : HybridWord.State) : Option HybridWord.State := do
  let a ← (s.arrays 0)[i.toNat]?
  let b ← (s.arrays 0)[(i+1).toNat]?
  let c ← (s.arrays 0)[(i+2).toNat]?
  s.write 1 i ((a+b+c)/3)
hls_certified filter as filterHLS

def conditional (i x y : Word) (s : HybridWord.State) : Option HybridWord.State :=
  if y != 0 then s.write 1 i x else pure s
hls_certified conditional as conditionalHLS

def producer (i _x _y : Word) (s : HybridWord.State) : Option HybridWord.State := do
  let a ← (s.arrays 0)[i.toNat]?
  s.write 1 i (a+1)
hls_certified producer as producerHLS

def consumer (i _x _y : Word) (s : HybridWord.State) : Option HybridWord.State := do
  let a ← (s.arrays 1)[i.toNat]?
  s.write 2 i (a*2)
hls_certified consumer as consumerHLS

def supply (_ : Unit) : List Int := [0,1,2,3,4]
def sizes (a : Nat) : Nat := if a < 3 then 5 else 0
def layout : Array (Nat × Nat) := #[(0,5),(1,5),(2,5)]

def chainSource : List Stage :=
  [producerHLS.entry.stage 5 0 0 1 5 supply,consumerHLS.entry.stage 5 1 0 1 5 supply]
def chainEntry : Entry chainSource := .cons producerHLS.entry (.cons consumerHLS.entry .nil)

/-- An example of using the GENERAL theorem. All input data, the generated
artifact and physical initial state remain universally quantified. -/
theorem filter_to_rtl
    {c : Compiled (filterHLS.entry.program 5 0 0 1 3 supply) [1] sizes layout 4096}
    (compiled : filterHLS.compile 5 0 0 1 3 supply [1] sizes layout 4096 = .ok c)
    (s : HybridWord.State) (x y : Word) (input : c.InputConditions s x y)
    (r : RTL.InterfaceState c.backend.artifact.storageShape) (running : r.Running)
    (same : StorageAgreement c.backend.artifact.storageShape r.core.decode (c.backend.initial s x y)) :
    ∃ cycles result,
      SystemVerilog.runText c.text c.backend.artifact.storageShape cycles r = some result ∧
      Observation c.backend.artifact.storageShape [1] result.core.decode
        (HybridWord.runSource filter x y 1 3 0 s) :=
  filterHLS.correct 5 0 0 1 3 supply [1] sizes layout 4096 compiled s x y input r running same

#print axioms filterHLS.correct
#print axioms conditionalHLS.correct
#print axioms filter_to_rtl

end IRComparison.CertifiedHLSExamples
