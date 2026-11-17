import IRComparison.Memory.WindowCoverage

namespace IRComparison.NativeWindowExpr
open WindowSchedule

/-- Static address arithmetic, including Lean's explicit Int.toNat clamp. -/
def address (i : Int) : Expr → Option Int
  | .lit n => some n
  | .index => some i
  | .natIndex e => return Int.ofNat (← address i e).toNat
  | .add a b => do return (← address i a)+(← address i b)
  | .sub a b => do return (← address i a)-(← address i b)
  | .mul a b => do return (← address i a)*(← address i b)
  | .div a b => do return (← address i a)/(← address i b)
  | _ => none

theorem address_correct (h : address i e = some v) (x y : Int) (s : State) (ls : List Int) :
    e.eval i x y s ls = some v := by
  induction e generalizing v with
  | lit | index => exact h
  | natIndex e ih =>
    cases he : address i e <;> simp [address,he] at h
    subst v
    simp [Expr.eval,ih he]
  | add a b ha hb | sub a b ha hb | mul a b ha hb | div a b ha hb =>
    cases h₁ : address i a <;> simp [address,h₁] at h
    cases h₂ : address i b <;> simp [h₂] at h
    subst v
    simp [Expr.eval,ha h₁,hb h₂]
  | left | right | «local» | reg | select | read => simp [address] at h

structure Compiled (i : Int) (array depth : Nat) (keys : List Int) (source : Expr) where
  code : Expr
  correct : ∀ (data : Array Int) (values locals : List Int) (s : State) (x y : Int),
    s.arrays array = data → Matches (arrayInput data) keys values → locals.length = depth →
    code.eval i x y s (locals++values) = source.eval i x y s locals

def compile (i : Int) (array depth : Nat) (keys : List Int) :
    (source : Expr) → Option (Compiled i array depth keys source)
  | .lit n => some ⟨.lit n,by intros; rfl⟩
  | .index => some ⟨.index,by intros; rfl⟩
  | .left => some ⟨.left,by intros; rfl⟩
  | .right => some ⟨.right,by intros; rfl⟩
  | .reg r => some ⟨.reg r,by intros; rfl⟩
  | .local n =>
      if bound : n < depth then some ⟨.local n,by
        intro data values locals s x y frozen held len
        simp [Expr.eval,List.getElem?_append,show n < locals.length by omega]⟩ else none
  | .natIndex e => do
      let c ← compile i array depth keys e
      return ⟨.natIndex c.code,by
        intro data values locals s x y frozen held len
        simp only [Expr.eval,c.correct data values locals s x y frozen held len]⟩
  | .add a b => do
      let ca ← compile i array depth keys a
      let cb ← compile i array depth keys b
      return ⟨.add ca.code cb.code,by
        intro data values locals s x y frozen held len
        simp only [Expr.eval,ca.correct data values locals s x y frozen held len,cb.correct data values locals s x y frozen held len]⟩
  | .sub a b => do
      let ca ← compile i array depth keys a
      let cb ← compile i array depth keys b
      return ⟨.sub ca.code cb.code,by
        intro data values locals s x y frozen held len
        simp only [Expr.eval,ca.correct data values locals s x y frozen held len,cb.correct data values locals s x y frozen held len]⟩
  | .mul a b => do
      let ca ← compile i array depth keys a
      let cb ← compile i array depth keys b
      return ⟨.mul ca.code cb.code,by
        intro data values locals s x y frozen held len
        simp only [Expr.eval,ca.correct data values locals s x y frozen held len,cb.correct data values locals s x y frozen held len]⟩
  | .div a b => do
      let ca ← compile i array depth keys a
      let cb ← compile i array depth keys b
      return ⟨.div ca.code cb.code,by
        intro data values locals s x y frozen held len
        simp only [Expr.eval,ca.correct data values locals s x y frozen held len,cb.correct data values locals s x y frozen held len]⟩
  | .select e a b => do
      let ce ← compile i array depth keys e
      let ca ← compile i array depth keys a
      let cb ← compile i array depth keys b
      return ⟨.select ce.code ca.code cb.code,by
        intro data values locals s x y frozen held len
        simp only [Expr.eval,ce.correct data values locals s x y frozen held len,ca.correct data values locals s x y frozen held len,cb.correct data values locals s x y frozen held len]⟩
  | .read a e =>
      if same : a = array then
        match ha : address i e with
        | none => none
        | some key => do
          let j ← slot key keys
          return ⟨.local (depth+j.val),by
            intro data values locals s x y frozen held len
            obtain ⟨length,point⟩ := held
            obtain ⟨v,hv,hi⟩ := point j.val key j.property
            have hs : (if key < 0 then none else (s.arrays a)[key.toNat]?) = some v := by
              simpa [arrayInput,same,frozen] using hi
            simp only [Expr.eval,address_correct ha x y s locals,Option.bind_some]
            rw [List.getElem?_append_right (by omega)]
            simpa [len,hv] using hs.symm⟩
      else do
        let c ← compile i array depth keys e
        return ⟨.read a c.code,by
          intro data values locals s x y frozen held len
          simp only [Expr.eval,c.correct data values locals s x y frozen held len]⟩

end IRComparison.NativeWindowExpr
