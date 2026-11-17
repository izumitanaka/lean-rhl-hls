import IRComparison.Core.AffineAddress

namespace IRComparison.SymbolicWindowExpr
open WindowSchedule AffineAddress

def keys (coefficient : Int) (offsets : List Int) (i : Int) : List Int :=
  offsets.map (fun offset => coefficient*i+offset)

structure Compiled (array depth : Nat) (coefficient : Int) (offsets : List Int) (source : Expr) where
  code : Expr
  guards : List Linear
  correct : ∀ i, Valid guards i → ∀ (data : Array Int) (values locals : List Int) (s : State) (x y : Int),
    s.arrays array = data → Matches (arrayInput data) (keys coefficient offsets i) values → locals.length = depth →
    code.eval i x y s (locals++values) = source.eval i x y s locals

def compile (array depth : Nat) (coefficient : Int) (offsets : List Int) :
    (source : Expr) → Option (Compiled array depth coefficient offsets source)
  | .lit n => some ⟨.lit n,[],by intros; rfl⟩
  | .index  => some ⟨.index ,[],by intros; rfl⟩
  | .left  => some ⟨.left ,[],by intros; rfl⟩
  | .right  => some ⟨.right ,[],by intros; rfl⟩
  | .reg r => some ⟨.reg r,[],by intros; rfl⟩
  | .local n =>
    if bound : n < depth then some ⟨.local n,[],by
      intro i valid data values locals s x y frozen held len
      simp [Expr.eval,List.getElem?_append,show n < locals.length by omega]⟩ else none
  | .natIndex e => do
    let c ← compile array depth coefficient offsets e
    return ⟨.natIndex c.code,c.guards,by
      intro i valid data values locals s x y frozen held len
      simp only [Expr.eval,c.correct i valid data values locals s x y frozen held len]⟩
  | .add a b => do
    let ca ← compile array depth coefficient offsets a
    let cb ← compile array depth coefficient offsets b
    return ⟨.add ca.code cb.code,ca.guards++cb.guards,by
      intro i valid data values locals s x y frozen held len
      obtain ⟨ha,hb⟩ := valid_append.mp valid
      simp only [Expr.eval,ca.correct i ha data values locals s x y frozen held len,
        cb.correct i hb data values locals s x y frozen held len]⟩
  | .sub a b => do
    let ca ← compile array depth coefficient offsets a
    let cb ← compile array depth coefficient offsets b
    return ⟨.sub ca.code cb.code,ca.guards++cb.guards,by
      intro i valid data values locals s x y frozen held len
      obtain ⟨ha,hb⟩ := valid_append.mp valid
      simp only [Expr.eval,ca.correct i ha data values locals s x y frozen held len,
        cb.correct i hb data values locals s x y frozen held len]⟩
  | .mul a b => do
    let ca ← compile array depth coefficient offsets a
    let cb ← compile array depth coefficient offsets b
    return ⟨.mul ca.code cb.code,ca.guards++cb.guards,by
      intro i valid data values locals s x y frozen held len
      obtain ⟨ha,hb⟩ := valid_append.mp valid
      simp only [Expr.eval,ca.correct i ha data values locals s x y frozen held len,
        cb.correct i hb data values locals s x y frozen held len]⟩
  | .div a b => do
    let ca ← compile array depth coefficient offsets a
    let cb ← compile array depth coefficient offsets b
    return ⟨.div ca.code cb.code,ca.guards++cb.guards,by
      intro i valid data values locals s x y frozen held len
      obtain ⟨ha,hb⟩ := valid_append.mp valid
      simp only [Expr.eval,ca.correct i ha data values locals s x y frozen held len,
        cb.correct i hb data values locals s x y frozen held len]⟩
  | .select e a b => do
    let ce ← compile array depth coefficient offsets e
    let ca ← compile array depth coefficient offsets a
    let cb ← compile array depth coefficient offsets b
    return ⟨.select ce.code ca.code cb.code,ce.guards++(ca.guards++cb.guards),by
      intro i valid data values locals s x y frozen held len
      obtain ⟨he,hab⟩ := valid_append.mp valid
      obtain ⟨ha,hb⟩ := valid_append.mp hab
      simp only [Expr.eval,ce.correct i he data values locals s x y frozen held len,
        ca.correct i ha data values locals s x y frozen held len,cb.correct i hb data values locals s x y frozen held len]⟩
  | .read a e =>
    if same : a = array then do
      let view ← AffineAddress.parse e
      if hc : view.linear.coefficient = coefficient then
        let j ← slot view.linear.offset offsets
        return ⟨.local (depth+j.val),view.guards,by
          intro i valid data values locals s x y frozen held len
          have keyAt : (keys coefficient offsets i)[j.val]? = some (coefficient*i+view.linear.offset) := by
            simp [keys,List.getElem?_map,j.property]
          obtain ⟨length,point⟩ := held
          obtain ⟨v,hv,hi⟩ := point j.val _ keyAt
          have hs : (if coefficient*i+view.linear.offset < 0 then none else
              (s.arrays a)[(coefficient*i+view.linear.offset).toNat]?) = some v := by
            simpa [arrayInput,same,frozen] using hi
          simp only [Expr.eval,view.correct i x y s locals valid,Option.bind_some,Linear.eval,hc]
          rw [List.getElem?_append_right (by omega)]
          simpa [len,hv] using hs.symm⟩
      else none
    else do
      let c ← compile array depth coefficient offsets e
      return ⟨.read a c.code,c.guards,by
        intro i valid data values locals s x y frozen held len
        simp only [Expr.eval,c.correct i valid data values locals s x y frozen held len]⟩

end IRComparison.SymbolicWindowExpr
