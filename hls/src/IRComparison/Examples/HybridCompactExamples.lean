import IRComparison.Hybrid.HybridInputs
import IRComparison.Hybrid.HybridCompactTransport

namespace IRComparison.HybridCompactExamples
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
hls_hybrid NativeWindowExamples.dilated as taps

def forward := (HybridSymbolicLoop.compile 13 0 taps.hybridBody 0 1 3).get (by decide +kernel)
def reverse := (HybridSymbolicLoop.compile 13 0 taps.hybridBody 2 (-1) 3).get (by decide +kernel)
def strided := (HybridSymbolicLoop.compile 13 0 taps.hybridBody 0 2 3).get (by decide +kernel)
def forwardFIFO := (HybridCompactFIFO.compile forward.code ⟨0,1,13⟩).get (by decide +kernel)
example : (HybridCompactFIFO.compile reverse.code ⟨0,1,13⟩).isSome = false := by decide +kernel
example : (HybridSymbolicLoop.compile 13 0 taps.hybridBody (-1) 1 3).isSome = false := by decide +kernel
example : forward.code.initial.length = 5 ∧ forward.code.refill.length = 5 := by decide +kernel
example : (forwardFIFO.code.eval 0 0 NativeWindowExamples.initial [1,2,3,4,5,6,7,8,9,10,11,12,13]).map
    (fun (s,q) => (s.arrays 1,q)) = some (#[9,12,15,0,0,0,0,0,0,0,0,0,0],[8,9,10,11,12,13]) := by decide +kernel

theorem native_correct (s : State) (hs : (s.arrays 0).size = 13) (q : List Int)
    (hq : CommunicationIR.Corresponds (arrayInput (s.arrays 0)) (CompactSequence.Seq.mk 0 1 13).entries q) (x y : Int) :
    (forwardFIFO.code.eval x y s q).map Prod.fst =
      Source.iterate (fun i => NativeWindowExamples.dilated i x y) 1 3 0 s := by
  rw [forwardFIFO.correct s q hq,forward.correct s hs]
  exact Source.iterate_congr _ _ (fun i t => taps.hybridBody_correct i x y t) 1 3 0 s

-- The state remains executable when a symbolic guard cannot be established.
example (s : State) (hs : (s.arrays 0).size = 13) (x y : Int) :
    (taps.hybridCompactWindow 13 0 (-1) 1 3).code.eval (arrayInput (s.arrays 0)) x y s =
      Source.iterate (fun i => NativeWindowExamples.dilated i x y) 1 3 (-1) s :=
  taps.hybridCompactWindow_correct 13 0 (-1) 1 3 s hs x y

end IRComparison.HybridCompactExamples
