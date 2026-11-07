import IRComparison.Frontend.LeanTypeAliases

namespace IRComparison.LeanUniverseConversion
open Lean4Lean LeanTypeInference

theorem closed_eval (u : VLevel) (closed : u.WF 0) (values : List Nat) :
    u.eval values = u.eval [] := by
  induction u <;> simp_all [VLevel.WF, VLevel.eval]

def conversion (env : VEnv) : Conversion env := fun U context actual expected => do
  match actual, expected with
  | .sort u, .sort v =>
      if hu : u.WF U then
        if hv : v.WF U then
          if cu : u.WF 0 then
            if cv : v.WF 0 then
              if same : u.eval [] = v.eval [] then
                let eq : u ≈ v := by
                  apply funext
                  intro values
                  rw [closed_eval u cu values, closed_eval v cv values, same]
                return ⟨.succ u, .sortDF hu hv eq⟩
              else none
            else none
          else none
        else none
      else none
  | _, _ => none

def orElse (first second : Conversion env) : Conversion env := fun U context a b =>
  (first U context a b).orElse (fun _ => second U context a b)

end IRComparison.LeanUniverseConversion
