import IRComparison.Frontend.LeanLibrary

namespace IRComparison.LeanProofApplication
open Lean4Lean LeanTyped

structure Typed (env : VEnv) (U : Nat) (context : List VExpr) where
  term : VExpr
  type : VExpr
  correct : env.HasType U context term type

/-- Use the exact type of an existing monomorphic native theorem. No new
    equality is inserted into the environment by this operation. -/
def constant (native : Lean.Environment) (env : VEnv) (U : Nat)
    (context : List VExpr) (name : Lean.Name) : Option (Typed env U context) := do
  let info ← native.find? name
  if info.levelParams = [] then
    let type ← translate info.type
    if registered : env.constants name = some ⟨0,type.val⟩ then
      have h := VEnv.HasType.const (U := U) (Γ := context) (ls := []) registered (by simp) rfl
      return ⟨.const name [],type.val,by simpa only [type.property.instL_empty] using h⟩
    else none
  else none

/-- Instantiate a universal theorem with an already typed argument, including
    a proof produced by another proved compiler stage. -/
def apply (f a : Typed env U context) : Option (Typed env U context) :=
  match f.type, f.correct with
  | .forallE domain codomain, hf =>
      if same : a.type = domain then
        some ⟨.app f.term a.term, codomain.inst a.term, .app hf (same ▸ a.correct)⟩
      else none
  | _, _ => none

end IRComparison.LeanProofApplication
