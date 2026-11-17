import IRComparison.Frontend.LeanBodyCommand
import IRComparison.Hybrid.HybridUnifiedPipeline
import IRComparison.Hybrid.HybridCompactTransport

namespace IRComparison
open Lean Elab Command

/-- Normalize the unoptimized Lean body to explicit reads, then keep it in mixed IR. -/
elab "hls_hybrid " source:ident " as " target:ident : command => do
  elabCommand (← `(hls_body $source as $target))
  let base := target.getId
  let input := mkIdent (.str base "imperativeBody")
  let inputProof := mkIdent (.str base "imperativeBody_correct")
  let body := mkIdent (.str base "hybridBody")
  let proof := mkIdent (.str base "hybridBody_correct")
  let kernel := mkIdent (.str base "hybridKernel")
  elabCommand (← `(def $body : HybridIR.MemoryCmd := HybridIR.MemoryCmd.fromImperative $input))
  elabCommand (← `(theorem $proof (i x y : Int) (s : State) :
      ($body).eval i x y s [] = $source i x y s := by
    exact (HybridIR.MemoryCmd.fromImperative_correct $input (i:=i) (x:=x) (y:=y) (s:=s) (ls:=[])).trans ($inputProof i x y s)))
  elabCommand (← `(def $kernel (size array : Nat) (start stride : Int) (count : Nat)
      (supplier : Unit → List Int) : HybridIR.Kernel :=
    { body := $body, native := $source, correct := $proof,
      size := size, array := array, start := start, stride := stride,
      count := count, supplier := supplier }))
  let compact := mkIdent (.str base "hybridCompactWindow")
  let compactProof := mkIdent (.str base "hybridCompactWindow_correct")
  elabCommand (← `(def $compact (size array : Nat) (start stride : Int) (count : Nat) :=
    HybridSymbolicLoop.select size array $body start stride count))
  elabCommand (← `(theorem $compactProof (size array : Nat) (start stride : Int) (count : Nat)
      (s : State) (sized : (s.arrays array).size = size) (x y : Int) :
      ($compact size array start stride count).code.eval (arrayInput (s.arrays array)) x y s =
        Source.iterate (fun i => $source i x y) stride count start s := by
    rw [HybridSymbolicLoop.Selected.correct _ s sized]
    exact Source.iterate_congr _ _ (fun i t => $proof i x y t) stride count start s))
end IRComparison
