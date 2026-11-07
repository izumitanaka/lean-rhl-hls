import IRComparison.Frontend.LeanLoopNormalization

namespace IRComparison.ReadHoistingFacts

/-- Option has no externally observable effects. An independent read can be
    captured before an update; either failure is still failure. -/
theorem commute (update : Option State) (read : Option Int)
    (next : State → Int → Option State) :
    (do let v ← read; let t ← update; next t v) =
    (do let t ← update; let v ← read; next t v) := by
  cases update <;> cases read <;> rfl

theorem transport (result normalized source : Option State)
    (h : result = normalized) (hn : normalized = source) : result = source := h.trans hn

end IRComparison.ReadHoistingFacts

namespace IRComparison.LeanReadHoisting
open Lean4Lean LeanTyped LeanIRQuotation LeanIREvaluation LeanBodyQuotation LeanTypeInference
variable {env : VEnv} {U : Nat} {context : List VExpr}

structure Artifact (source : Lean.Expr) where
  plain : Lean.Expr
  sourceCore : {v // Represents source v}
  plainCore : {v // Represents plain v}
  sourceTyped : env.HasType U context sourceCore.val optionState
  plainTyped : env.HasType U context plainCore.val optionState
  proof : VExpr
  correct : env.HasType U context proof (eqState plainCore.val sourceCore.val)

/-- Move an independent optional read across a state-producing computation.
    The type of `commute` must match the entire original and rewritten terms;
    in particular, a read of the newly produced state is not independent. -/
def compile (native : Lean.Environment) (conversion : Conversion env) (exposure : Exposure env)
    (source : Lean.Expr) : Option (Artifact (env := env) (U := U) (context := context) source) := do
  let .app (.app firstHead update) (.lam tn (.const ``State []) rest tb) := source | none
  let .app (.app readHead read) (.lam vn (.const ``Int []) body vb) := rest | none
  let source := Lean.Expr.app (.app firstHead update) (.lam tn (.const ``State []) (.app (.app readHead read) (.lam vn (.const ``Int []) body vb)) tb)
  let read := LeanBindings.instantiate (.bvar 0) read
  let continuation := Lean.Expr.lam tn (.const ``State []) (.lam vn (.const ``Int []) body vb) tb
  let updateCore ← translate update
  let readCore ← translate read
  let nextCore ← translate continuation
  let hu ← checkWith env conversion U context updateCore.val optionState exposure
  let hr ← checkWith env conversion U context readCore.val optionInt exposure
  let nt := VExpr.forallE stateType (.forallE intType optionState)
  let hn ← checkWith env conversion U context nextCore.val nt exposure
  let fact ← LeanLoopNormalization.args native ``ReadHoistingFacts.commute
    [⟨updateCore.val,optionState,hu.down⟩,⟨readCore.val,optionInt,hr.down⟩,⟨nextCore.val,nt,hn.down⟩]
  let swapped := LeanBindings.rename (fun n => match n with | 0 => 1 | 1 => 0 | n+2 => n+2) body
  let plain := Lean.mkAppN (LeanLoopNormalization.bindHead (.const ``Int []) (.const ``State []))
    #[read,.lam vn (.const ``Int [])
      (Lean.mkAppN (LeanLoopNormalization.bindHead (.const ``State []) (.const ``State []))
        #[LeanBindings.rename Nat.succ update,.lam tn (.const ``State []) swapped tb]) vb]
  let sc ← translate source
  let pc ← translate plain
  let hs ← checkWith env conversion U context sc.val optionState exposure
  let hp ← checkWith env conversion U context pc.val optionState exposure
  let q ← LeanLoopNormalization.cast conversion fact (eqState pc.val sc.val)
  return ⟨plain,sc,pc,hs.down,hp.down,q.val,q.property⟩

end IRComparison.LeanReadHoisting
