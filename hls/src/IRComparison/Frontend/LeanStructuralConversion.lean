import IRComparison.Frontend.LeanTypeReduction

namespace IRComparison.LeanStructuralConversion
open Lean4Lean LeanTypeInference

structure Equation (env : VEnv) (U : Nat) (context : List VExpr) (a b : VExpr) where
  type : VExpr
  correct : env.IsDefEq U context a b type

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
    let nested : Conversion env := fun levels context left right => do
      if let some h := base levels context left right then return h
      let h ← prove env base exposure levels fuel context left right
      match h.type, h.correct with
      | .sort u, h => return ⟨u,h⟩
      | _, _ => none
    if same : a = b then
      let typed ← inferWith env nested U ctx a exposure
      return ⟨typed.val,by simpa only [same] using typed.property⟩
    if let some left := LeanTypeReduction.step [] nested U ctx exposure a then
      if let some rest := prove env base exposure U fuel ctx left.val.1 b then
        if same : rest.type = left.val.2 then
          return ⟨left.val.2,left.property.trans (same ▸ rest.correct)⟩
    if let some right := LeanTypeReduction.step [] nested U ctx exposure b then
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
      if same : da = db then
        let td ← inferWith env nested U ctx da exposure
        match td.val, td.property with
        | .sort u, hd =>
          let body ← prove env base exposure U fuel (da :: ctx) ba bb
          return ⟨.forallE da body.type,by simpa only [same] using VEnv.IsDefEq.lamDF hd body.correct⟩
        | _, _ => none
      else none
    | .forallE da ba, .forallE db bb =>
      if same : da = db then
        let td ← inferWith env nested U ctx da exposure
        match td.val, td.property with
        | .sort u, hd =>
          let body ← prove env base exposure U fuel (da :: ctx) ba bb
          match body.type, body.correct with
          | .sort v, hb =>
            return ⟨.sort (.imax u v),by simpa only [same] using VEnv.IsDefEq.forallEDF hd hb⟩
          | _, _ => none
        | _, _ => none
      else none
    | _, _ => none

def conversion (env : VEnv) (base : Conversion env) (exposure : Exposure env := noExposure env) : Conversion env := fun U ctx a b => do
  if let some h := base U ctx a b then return h
  let eq ← prove env base exposure U 64 ctx a b
  match eq.type, eq.correct with
  | .sort u, h => return ⟨u,h⟩
  | _, _ => none

end IRComparison.LeanStructuralConversion
