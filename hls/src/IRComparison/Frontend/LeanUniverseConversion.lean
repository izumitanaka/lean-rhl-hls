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

theorem wf_of_closed {u : VLevel} (closed : u.WF 0) (U : Nat) : u.WF U := by
  induction u <;> simp_all [VLevel.WF]

/-- Closed universe expressions with the same value are accepted by the
actual converter. This includes imax/max expressions introduced by dependent
function types, without a bound on their syntactic nesting. -/
theorem conversion_complete (left : u.WF 0) (right : v.WF 0)
    (same : u.eval [] = v.eval []) (env : VEnv) (U : Nat) (ctx : List VExpr) :
    ∃ result, conversion env U ctx (.sort u) (.sort v) = some result := by
  simp only [conversion,dif_pos (wf_of_closed left U),dif_pos (wf_of_closed right U),
    dif_pos left,dif_pos right,dif_pos same]
  exact ⟨_,rfl⟩

def orElse (first second : Conversion env) : Conversion env := fun U context a b =>
  (first U context a b).orElse (fun _ => second U context a b)

end IRComparison.LeanUniverseConversion
