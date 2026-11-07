import PaperCore.Language

namespace PaperCore.WindowStrideShifts

def trim : Nat → List Var → List Var
  | 0, buffers => buffers
  | n+1, buffers => trim n buffers.dropLast

theorem trim_eq_take : trim n buffers = buffers.take (buffers.length-n) := by
  induction n generalizing buffers with
  | zero => simp [trim]
  | succ n ih =>
    rw [trim,ih,List.length_dropLast,List.dropLast_eq_take,List.take_take]
    congr 1
    omega

theorem trim_suffix : trim suffix.length (initialBuffers ++ suffix) = initialBuffers := by
  rw [trim_eq_take]
  simp


end PaperCore.WindowStrideShifts
