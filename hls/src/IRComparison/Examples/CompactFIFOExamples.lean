import IRComparison.Memory.CompactFIFO
import IRComparison.Examples.SymbolicWindowExamples

namespace IRComparison.CompactFIFOExamples
open SymbolicWindowExamples NativeWindowExamples
set_option maxRecDepth 16384

def forwardFIFO := (CompactFIFO.compile forward.code ⟨0,1,13⟩).get (by decide +kernel)
def reverseFIFO := (CompactFIFO.compile reverse.code ⟨6,-1,7⟩).get (by decide +kernel)
def stridedFIFO := (CompactFIFO.compile strided.code ⟨0,1,13⟩).get (by decide +kernel)
def billionFIFO := (CompactFIFO.compile billion.code ⟨0,1,1000000004⟩).get (by decide +kernel)

example : billionFIFO.code.initial.length = 5 ∧ billionFIFO.code.refill.length = 5 := by decide +kernel
example : (forwardFIFO.code.eval 0 0 initial [1,2,3,4,5,6,7,8,9,10,11,12,13]).map (fun (s,q) => (s.arrays 1,q)) =
    some (#[9,12,15,0,0,0,0,0,0,0,0,0,0],[8,9,10,11,12,13]) := by decide +kernel
example : (reverseFIFO.code.eval 0 0 initial [7,6,5,4,3,2,1]).map (fun (s,q) => (s.arrays 1,q)) =
    some (#[9,12,15,0,0,0,0,0,0,0,0,0,0],[]) := by decide +kernel
example : (stridedFIFO.code.eval 0 0 initial [1,2,3,4,5,6,7,8,9,10,11,12,13]).map (fun (s,q) => (s.arrays 1,q)) =
    some (#[9,0,15,0,21,0,0,0,0,0,0,0,0],[10,11,12,13]) := by decide +kernel

example : (CompactFIFO.compile reverse.code ⟨0,1,13⟩).isSome = false := by decide +kernel

theorem native_correct (s : State) (hs : (s.arrays 0).size = 13) (q : List Int)
    (hq : CommunicationIR.Corresponds (arrayInput (s.arrays 0)) (CompactSequence.Seq.mk 0 1 13).entries q) (x y : Int) :
    (forwardFIFO.code.eval x y s q).map Prod.fst = Source.iterate (fun i => dilated i x y) 1 3 0 s := by
  rw [forwardFIFO.correct s q hq,forward.correct s hs]
  exact Source.iterate_congr _ _ (fun i t => taps.imperativeBody_correct i x y t) 1 3 0 s

example : CompactFIFOControl.run forwardFIFO.code 0 0 1000
    (.start initial [1,2,3,4,5,6,7,8,9,10,11,12,13]) =
    .stopped (forwardFIFO.code.eval 0 0 initial [1,2,3,4,5,6,7,8,9,10,11,12,13]) := by rfl

end IRComparison.CompactFIFOExamples
