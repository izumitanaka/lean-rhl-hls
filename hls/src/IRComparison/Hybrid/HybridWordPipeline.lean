import IRComparison.Hybrid.HybridWordCommand
import IRComparison.Hybrid.HybridWindowTransport
import IRComparison.Hybrid.HybridCommandControl
import IRComparison.Hybrid.HybridPipeline
import IRComparison.Hybrid.HybridBlocksControl

namespace IRComparison.HybridWord

def iterate (body : Cmd) (x y : Word) (stride : Int) : Nat → Int → State → Option State
  | 0,_,s => some s
  | n+1,i,s => do
    let t ← body.eval (BitVec.ofInt 32 i) x y s []
    iterate body x y stride n (i+stride) t

theorem iterate_correct (body : Cmd) (s : State) :
    Source.iterate (fun i => body.lower.eval i (encode x) (encode y)) stride count start s.encode =
      (iterate body x y stride count start s).map State.encode := by
  induction count generalizing start s with
  | zero => rfl
  | succ n ih =>
    rw [Source.iterate, iterate]
    have h := Cmd.lower_correct_int (x:=x) (y:=y) start body s []
    simp only [List.map_nil] at h
    rw [h]
    cases body.eval (BitVec.ofInt 32 start) x y s [] <;> simp [ih]

def compile (size array : Nat) (body : Cmd) (stride : Int) (count : Nat)
    (start : Int) (producer : List Int) :=
  HybridWindowTransport.compile size array body.lower stride count start producer

theorem compile_correct (body : Cmd) (s : State)
    (sized : (s.arrays array).size = size)
    (q : List Int)
    (contract : (compile size array body stride count start producer).Contract (s.encode.arrays array) q) :
    (compile size array body stride count start producer).eval (s.encode.arrays array)
      (encode x) (encode y) s.encode q =
      (iterate body x y stride count start s).map State.encode := by
  rw [HybridWindowTransport.Selected.correct _ s.encode
    (by simpa [State.encode] using sized) _ _ _ contract]
  exact iterate_correct body s

theorem control_finishes (body : Cmd) (s : State) (ls : List Word) (q : List Int) :
    ∃ n, HybridCommandControl.run (encode i) (encode x) (encode y) n
      (.running [(body.lower.target,ls.map encode)] s.encode q) =
      .stopped ((body.eval i x y s ls).map (fun t => (t.encode,q))) := by
  obtain ⟨n,h⟩ := HybridCommandControl.finishes (i:=encode i) (x:=encode x) (y:=encode y)
    body.lower.target s.encode q (ls.map encode)
  refine ⟨n, ?_⟩
  simpa [HybridIR.MemoryCmd.target_correct, Cmd.lower_correct, Option.map_map, Function.comp_def] using h

/-- Optimized buffer/FIFO blocks run on the existing sequential controller. -/
theorem optimized_control_finishes (body : Cmd) (s : State)
    (sized : (s.arrays array).size = size)
    (q : List Int)
    (contract : (compile size array body stride count start producer).Contract (s.encode.arrays array) q) :
    let selected := compile size array body stride count start producer
    ∃ n result, HybridBlocksControl.run (arrayInput (s.encode.arrays array)) (encode x) (encode y) n
      (.start (HybridIR.memoryBlocks selected.code) [] s.encode q []) = .stopped result ∧
      result.map (fun t => t.1) = (iterate body x y stride count start s).map State.encode := by
  dsimp only
  obtain ⟨n,h⟩ := HybridBlocksControl.finishes
    (input:=arrayInput (s.encode.arrays array)) (x:=encode x) (y:=encode y)
    (HybridIR.memoryBlocks (compile size array body stride count start producer).code) [] s.encode q []
  refine ⟨n,_,h,?_⟩
  rw [HybridIR.memoryBlocks_correct]
  simp only [Option.map_map, Function.comp_def]
  rw [HybridWindowTransport.Selected.code_correct]
  exact compile_correct body s sized q contract

end IRComparison.HybridWord
