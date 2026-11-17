import IRComparison.Frontend.LeanTypeReduction

/-! Runtime operations for typed administrative-let transport. Kept below
source-specific completeness proofs so the ordinary converter can reuse them. -/
namespace IRComparison.WordFrontend.RetainedConversion
open Lean4Lean LeanTyped LeanTypeInference LeanTypeReduction

/-- Stop as soon as the known endpoint of the argument bindings is reached.
Every step carries its typed equality. An insufficient argument count returns
none; the caller never assumes that equality follows from the count alone. -/
def reducePrefix (conv : Conversion env) (exposure : Exposure env) (U : Nat) (ctx : List VExpr)
    (target ty : VExpr) (targetTyped : env.HasType U ctx target ty) :
    Nat → (source : VExpr) → Option (PLift (env.IsDefEq U ctx source target ty))
  | count, source => do
    if same : source = target then return ⟨same ▸ targetTyped⟩
    match count with
    | 0 => none
    | count+1 =>
      let first ← step [] conv U ctx exposure source
      if sameType : first.val.2 = ty then
        let rest ← reducePrefix conv exposure U ctx target ty targetTyped count first.val.1
        return ⟨(sameType ▸ first.property).trans rest.down⟩
      else none

/-- A helper application reduces its whole lambda spine in one structural
step. The retained lets reduce to the same endpoint. Congruence lifts this
value equality through the existing certificate's equality prefix. -/
def conversion (conv : Conversion env) (exposure : Exposure env) (argumentCount : Nat) : Conversion env :=
  fun U ctx actual expected => do
    let .app leftPrefix left := actual | none
    let .app rightPrefix right := expected | none
    if samePrefix : leftPrefix = rightPrefix then
      let reduced ← step [] conv U ctx exposure right
      let equality ← reducePrefix conv exposure U ctx reduced.val.1 reduced.val.2
        (reduced.property.symm.trans reduced.property) argumentCount left
      let head ← inferWith env conv U ctx leftPrefix exposure
      match head.val,head.property with
      | .forallE domain codomain,headTyped =>
        if sameDomain : reduced.val.2 = domain then
          let values := (sameDomain ▸ equality.down).trans (sameDomain ▸ reduced.property.symm)
          let whole := VEnv.IsDefEq.appDF headTyped values
          match codomain.inst left,whole with
          | .sort level,proved => return ⟨level,by simpa only [samePrefix] using proved⟩
          | _,_ => none
        else none
      | _,_ => none
    else none

/-- Number of consecutive administrative binders in the source expression.
This follows the binder bodies, never unrolls a program loop, and does not
normalize arbitrary Lean definitions. -/
def prefixLength : VExpr → Nat
  | .app (.lam _ body) _ => prefixLength body + 1
  | _ => 0

def automatic (conv : Conversion env) (exposure : Exposure env) : Conversion env :=
  fun U ctx actual expected =>
    match actual with
    | .app head left => conversion conv exposure (prefixLength left) U ctx (.app head left) expected
    | _ => none

end IRComparison.WordFrontend.RetainedConversion
