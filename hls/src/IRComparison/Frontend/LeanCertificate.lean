import IRComparison.Frontend.LeanScalarPipeline

namespace IRComparison.LeanCertificate
open Lean4Lean

/-- Serialize the formal proof term back into native Lean syntax. The compiler's
    general proof does not depend on running a per-program equivalence checker.
    This exporter also permits independent kernel regression checks. -/
def level : VLevel → Lean.Level
  | .zero => .zero
  | .succ u => .succ (level u)
  | .max u v => .max (level u) (level v)
  | .imax u v => .imax (level u) (level v)
  | .param n => .param (.num `u n)

def expression : VExpr → Lean.Expr
  | .bvar n => .bvar n
  | .sort u => .sort (level u)
  | .const name us => .const name (us.map level)
  | .app f a => .app (expression f) (expression a)
  | .lam ty b => .lam `arg (expression ty) (expression b) .default
  | .forallE ty b => .forallE `arg (expression ty) (expression b) .default

theorem level_roundtrip (u : VLevel) (closed : u.WF 0) :
    LeanTyped.level (level u) = some u := by
  induction u with
  | zero => rfl
  | succ u ih => simp [level, LeanTyped.level, ih closed]
  | max u v hu hv => simp [level, LeanTyped.level, hu closed.1, hv closed.2]
  | imax u v hu hv => simp [level, LeanTyped.level, hu closed.1, hv closed.2]
  | param n => exact False.elim (Nat.not_lt_zero n closed)

private theorem levels_roundtrip (us : List VLevel) (closed : ∀ u ∈ us, u.WF 0) :
    (us.map level).mapM LeanTyped.level = some us := by
  induction us with
  | nil => rfl
  | cons u us ih =>
      simp [List.mapM_cons, level_roundtrip u (closed u (by simp)),
        ih (fun v hv => closed v (by simp [hv]))]

/-- Export preserves the formal term for every expression with closed universe
    levels, not just the certificates exercised in regression tests. -/
theorem expression_represents (e : VExpr) (closed : e.LevelWF 0) :
    LeanTyped.Represents (expression e) e := by
  induction e with
  | bvar n => exact .bvar
  | sort u => exact .sort (level_roundtrip u closed)
  | const name us => exact .constant (levels_roundtrip us closed)
  | app f a hf ha => exact .app (hf closed.1) (ha closed.2)
  | lam ty b ht hb => exact .lam (ht closed.1) (hb closed.2)
  | forallE ty b ht hb => exact .forallE (ht closed.1) (hb closed.2)

/-- Export the already constructed proof; native Lean validates this declaration
    using its kernel when the caller installs it with addDecl. -/
def declaration (proofName : Lean.Name) (result : LeanScalarPipeline.Result native sourceName)
    (backend : LeanScalarPipeline.Backend) : Lean.Declaration :=
  let proof := match backend with
    | .imperative => result.imperativeProof.term
    | .functional => result.functionalProof.term
  .thmDecl {
    name := proofName
    levelParams := []
    type := expression (LeanScalarPipeline.specification backend sourceName result.source.entry.compiled.body.emitted)
    value := expression proof }

end IRComparison.LeanCertificate
