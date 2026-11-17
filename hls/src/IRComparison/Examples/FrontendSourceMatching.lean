import Lean

namespace IRComparison.FrontendSourceMatching
/-- Test-side matching of fixed library headers. The body syntax is checked
separately, by source judgments; this does not run the HLS parser. -/
def sameClosedHeader : (expected actual : Lean.Expr) → Option (PLift (actual = expected))
  | .const n [], .const m []
  | .const n [.zero], .const m [.zero]
  | .const n [.zero,.zero], .const m [.zero,.zero]
  | .const n [.zero,.zero,.zero], .const m [.zero,.zero,.zero]
  | .const n [.zero,.zero,.zero,.zero], .const m [.zero,.zero,.zero,.zero]
  | .const n [.succ .zero], .const m [.succ .zero] =>
    if h : m = n then some ⟨by subst m; rfl⟩ else none
  | .bvar n, .bvar m => if h : m = n then some ⟨by subst m; rfl⟩ else none
  | .lit (.natVal n), .lit (.natVal m) => if h : m = n then some ⟨by subst m; rfl⟩ else none
  | .app f a, .app g b => do
    let hf ← sameClosedHeader f g
    let ha ← sameClosedHeader a b
    return ⟨by rw [hf.down,ha.down]⟩
  | .lam n t b .default, .lam m u c .default =>
    if h : m = n then do
      let ht ← sameClosedHeader t u
      let hb ← sameClosedHeader b c
      return ⟨by rw [h,ht.down,hb.down]⟩
    else none
  | .forallE n t b .default, .forallE m u c .default =>
    if h : m = n then do
      let ht ← sameClosedHeader t u
      let hb ← sameClosedHeader b c
      return ⟨by rw [h,ht.down,hb.down]⟩
    else none
  | .letE n t v b flag, .letE m u w c otherFlag =>
    if h : m = n then
      if hf : otherFlag = flag then do
        let ht ← sameClosedHeader t u
        let hv ← sameClosedHeader v w
        let hb ← sameClosedHeader b c
        return ⟨by rw [h,hf,ht.down,hv.down,hb.down]⟩
      else none
    else none
  | _, _ => none

end IRComparison.FrontendSourceMatching
