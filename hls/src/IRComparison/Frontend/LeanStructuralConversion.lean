import IRComparison.Frontend.LeanRetainedConversion

namespace IRComparison.LeanStructuralConversion
open Lean4Lean LeanTypeInference

structure Equation (env : VEnv) (U : Nat) (context : List VExpr) (a b : VExpr) where
  type : VExpr
  correct : env.IsDefEq U context a b type

/-- Share the recursive conversion callback with the completeness proof.
The fallback accepts only sort-valued equations, as before. -/
def withSearch (base : Conversion env)
    (search : (U : Nat) → (ctx : List VExpr) → (a b : VExpr) → Option (Equation env U ctx a b)) :
    Conversion env := fun U ctx a b => do
  if let some h := base U ctx a b then return h
  let h ← search U ctx a b
  match h.type,h.correct with
  | .sort u,h => return ⟨u,h⟩
  | _,_ => none

/-- Typed congruence and beta computation, including inside predicate lambdas.
    Used for elaborated dependent indexing instances, whose predicates can
    differ by beta redexes. Every success carries an explicit derivation. -/
def prove (env : VEnv) (base : Conversion env) (exposure : Exposure env) (U : Nat) :
    Nat → (context : List VExpr) → (a b : VExpr) → Option (Equation env U context a b)
  | 0, _, _, _ => none
  | fuel+1, ctx, a, b => do
    -- Type aliases can occur below an application (e.g. Add Word versus
    -- Add (BitVec 32)), not only at the outermost conversion request.
    if let some h := base U ctx a b then return ⟨.sort h.val,h.property⟩
    let nested := withSearch base (fun levels context left right =>
      prove env base exposure levels fuel context left right)
    if same : a = b then
      let typed ← inferWith env nested U ctx a exposure
      return ⟨typed.val,by simpa only [same] using typed.property⟩
    -- Administrative lets commonly differ by exactly one beta step. Check
    -- both directions before recursively normalizing either side; otherwise
    -- a long chain is repeatedly explored in the wrong direction.
    let left := LeanTypeReduction.step [] nested U ctx exposure a
    let right := LeanTypeReduction.step [] nested U ctx exposure b
    if let some reduced := left then
      if same : reduced.val.1 = b then
        return ⟨reduced.val.2,same ▸ reduced.property⟩
    if let some reduced := right then
      if same : reduced.val.1 = a then
        return ⟨reduced.val.2,same ▸ reduced.property.symm⟩
    if let some left := left then
      if let some rest := prove env base exposure U fuel ctx left.val.1 b then
        if same : rest.type = left.val.2 then
          return ⟨left.val.2,left.property.trans (same ▸ rest.correct)⟩
    if let some right := right then
      if let some rest := prove env base exposure U fuel ctx a right.val.1 then
        if same : rest.type = right.val.2 then
          return ⟨right.val.2,(same ▸ rest.correct).trans right.property.symm⟩
    match a, b with
    | .app fa xa, .app fb xb =>
      let f ← prove env base exposure U fuel ctx fa fb
      match f.type, f.correct with
      | .forallE domain codomain, hf =>
        let arg ← prove env base exposure U fuel ctx xa xb
        if same : arg.type = domain then
          return ⟨codomain.inst xa,.appDF hf (same ▸ arg.correct)⟩
        else
          let cast ← nested U ctx arg.type domain
          return ⟨codomain.inst xa,.appDF hf (.defeqDF cast.property arg.correct)⟩
      | _, _ => none
    | .lam da ba, .lam db bb =>
      let domain ← prove env base exposure U fuel ctx da db
      match domain.type, domain.correct with
      | .sort u, hd =>
        let body ← prove env base exposure U fuel (da :: ctx) ba bb
        return ⟨.forallE da body.type,VEnv.IsDefEq.lamDF hd body.correct⟩
      | _, _ => none
    | .forallE da ba, .forallE db bb =>
      let domain ← prove env base exposure U fuel ctx da db
      match domain.type, domain.correct with
      | .sort u, hd =>
        let body ← prove env base exposure U fuel (da :: ctx) ba bb
        match body.type, body.correct with
        | .sort v, hb => return ⟨.sort (.imax u v),VEnv.IsDefEq.forallEDF hd hb⟩
        | _, _ => none
      | _, _ => none
    | _, _ => none

def ordinary (env : VEnv) (base : Conversion env) (exposure : Exposure env := noExposure env) : Conversion env := fun U ctx a b => do
  if let some h := base U ctx a b then return h
  let eq ← prove env base exposure U 64 ctx a b
  match eq.type, eq.correct with
  | .sort u, h => return ⟨u,h⟩
  | _, _ => none

/-- Preserve ordinary conversion and then try structurally bounded transport
of administrative lets. Both paths return checked typed equalities. -/
def conversion (env : VEnv) (base : Conversion env) (exposure : Exposure env := noExposure env) : Conversion env :=
  fun U ctx actual expected =>
    (ordinary env base exposure U ctx actual expected).orElse fun _ =>
      WordFrontend.RetainedConversion.automatic (ordinary env base exposure) exposure U ctx actual expected

theorem conversion_of_ordinary
    (success : ordinary env base exposure U ctx actual expected = some result) :
    conversion env base exposure U ctx actual expected = some result := by
  simp only [conversion,success,Option.orElse_some]

theorem conversion_of_retained
    (success : WordFrontend.RetainedConversion.automatic (ordinary env base exposure) exposure
      U ctx actual expected = some result) :
    ∃ converted, conversion env base exposure U ctx actual expected = some converted := by
  cases first : ordinary env base exposure U ctx actual expected with
  | some converted => exact ⟨converted,conversion_of_ordinary first⟩
  | none => simp only [conversion,first,Option.orElse_none,success]; exact ⟨_,rfl⟩


end IRComparison.LeanStructuralConversion
