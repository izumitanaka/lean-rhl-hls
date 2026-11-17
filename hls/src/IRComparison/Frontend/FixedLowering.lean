import IRComparison.Hybrid.FixedMemory
import IRComparison.Circuit.Layout

namespace IRComparison.FixedMemory
open Circuit

/-- Affine loop-index substitution cannot introduce an array identifier. -/
theorem affine_read_arrays (e : HybridIR.ReadCode) :
    readArrays (e.affineLocal slot start stride) = readArrays e := by
  induction e <;> simp_all [HybridIR.ReadCode.affineLocal,readArrays]

theorem affine_command_arrays (c : HybridIR.MemoryCmd) :
    allCommandArrays (c.affineLocal slot start stride).target = allCommandArrays c.target := by
  induction c generalizing slot <;>
    simp_all [HybridIR.MemoryCmd.affineLocal,HybridIR.MemoryCmd.target,
      allCommandArrays,affine_read_arrays]

/-- The independently checked fixed-buffer declarations cover every read in
the lowered expression, including both arms of a conditional. -/
theorem expr_lower_declared (e : HybridWord.Expr) (h : exprDeclared ds e = true) :
    (readArrays e.lower).all (fun a => (lookup ds a).isSome) = true := by
  induction e <;>
    simp_all [exprDeclared,HybridWord.Expr.lower,readArrays,List.all_append,Bool.and_eq_true]

/-- Covers all syntax combinations, not a list of successful source examples.
Copy lowering and the administrative counter add no undeclared source arrays. -/
theorem lower_declared (c : HybridWord.Cmd) (h : declared ds c = true) :
    (allCommandArrays c.lower.target).all (fun a => (lookup ds a).isSome) = true := by
  induction c <;>
    simp_all [declared,HybridWord.Cmd.lower,HybridIR.MemoryCmd.target,
      allCommandArrays,readArrays,affine_command_arrays,List.all_append,
      expr_lower_declared,Bool.and_eq_true]

theorem lookup_mem (h : lookup ds a = some n) : (a,n) ∈ ds.toList := by
  obtain ⟨before,after,eq,_⟩ := List.lookup_eq_some_iff.mp h
  rw [eq]
  simp

end IRComparison.FixedMemory
