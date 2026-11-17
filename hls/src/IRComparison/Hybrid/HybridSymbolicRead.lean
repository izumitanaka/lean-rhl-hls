import IRComparison.Hybrid.HybridAffine
import IRComparison.Memory.SymbolicWindowExpr
import IRComparison.Hybrid.WordTyping
import IRComparison.Hybrid.References

namespace IRComparison.HybridSymbolicRead
open HybridIR WindowSchedule AffineAddress SymbolicWindowExpr HybridWindowRead

structure Compiled (array depth : Nat) (coefficient : Int) (offsets : List Int)
    (known : HybridAffine.Known) (source : ReadCode) where
  code : ReadCode
  guards : List Linear
  arrays : ∀ allowed, source.ArraysWithin allowed → code.ArraysWithin allowed
  word : ∀ locals temps, WordRead locals temps source → WordRead (bufferWords depth locals) temps code
  correct : ∀ i, Valid guards i → ∀ (data : Array Int) (values locals temps : List Int) (s : State) (x y : Int),
    s.arrays array = data → Matches (arrayInput data) (keys coefficient offsets i) values → locals.length = depth →
    HybridAffine.Matches known temps i x y s locals →
    code.eval i x y s (locals++values) temps = source.eval i x y s locals temps

def compile (array depth : Nat) (coefficient : Int) (offsets : List Int) (known : HybridAffine.Known) :
    (source : ReadCode) → Option (Compiled array depth coefficient offsets known source)
  | .pure v => if hb : bounded depth v = true then
      some ⟨.pure v,[],by intros; trivial,by intro locals temps typed; exact typed.weaken bufferWords_keep,
        by intro i valid data values locals temps s x y frozen held len hm; exact bounded_correct v hb len⟩ else none
  | .register r => some ⟨.register r,[],by intros; trivial,by intros; exact .register r,by intros; rfl⟩
  | .memory a address =>
    if same : a = array then do
      let expression ← HybridAffine.value known address
      let view ← AffineAddress.parse expression
      if hc : view.linear.coefficient = coefficient then
        let j ← slot view.linear.offset offsets
        -- Retain the reconstruction equation to connect the symbolic address.
        if he : HybridAffine.value known address = some expression then
          return ⟨.pure (.local (depth+j.val)),view.guards,by intros; trivial,by
            intros; exact .pure (.local _ (by simp [bufferWords,show ¬ depth+j.val < depth from by omega])),by
            intro i valid data values locals temps s x y frozen held len hm
            have keyAt : (keys coefficient offsets i)[j.val]? = some (coefficient*i+view.linear.offset) := by
              simp [keys,List.getElem?_map,j.property]
            obtain ⟨actual,ha,hexpr⟩ := HybridAffine.value_correct address he hm
            have eq := view.correct i x y s locals valid
            rw [hexpr] at eq
            have haddr : address.eval i x y locals temps = some (coefficient*i+view.linear.offset) := by
              rw [ha,eq]; simp [Linear.eval,hc]
            subst a
            exact HybridWindowRead.readMem_rule (by simpa [frozen] using held) keyAt len haddr⟩
        else none
      else none
    else if hb : bounded depth address = true then
      some ⟨.memory a address,[],by intro allowed h; exact h,by intros; exact .memory a address,by
        intro i valid data values locals temps s x y frozen held len hm
        simp only [ReadCode.eval,bounded_correct address hb len]⟩
    else none
  | .bind first next => do
    let a ← compile array depth coefficient offsets known first
    let b ← compile array depth coefficient offsets (HybridAffine.read known first::known) next
    return ⟨.bind a.code b.code,a.guards++b.guards,by
      intro allowed h; exact ⟨a.arrays _ h.1,b.arrays _ h.2⟩,by
      intro locals temps typed
      cases typed with | bind ha hb => exact .bind (a.word _ _ ha) (b.word _ _ hb),by
      intro i valid data values locals temps s x y frozen held len hm
      obtain ⟨ha,hb⟩ := valid_append.mp valid
      simp only [ReadCode.eval,a.correct i ha data values locals temps s x y frozen held len hm]
      cases he : first.eval i x y s locals temps with
      | none => rfl
      | some v => exact b.correct i hb data values locals (v::temps) s x y frozen held len (HybridAffine.after_read hm he)⟩
  | .branch c yes no =>
    if hb : bounded depth c = true then do
      let a ← compile array depth coefficient offsets known yes
      let b ← compile array depth coefficient offsets known no
      return ⟨.branch c a.code b.code,a.guards++b.guards,by
        intro allowed h; exact ⟨a.arrays _ h.1,b.arrays _ h.2⟩,by
        intro locals temps typed
        cases typed with | branch ha hb => exact .branch (a.word _ _ ha) (b.word _ _ hb),by
        intro i valid data values locals temps s x y frozen held len hm
        obtain ⟨ha,hb'⟩ := valid_append.mp valid
        simp only [ReadCode.eval,bounded_correct c hb len,
          a.correct i ha data values locals temps s x y frozen held len hm,
          b.correct i hb' data values locals temps s x y frozen held len hm]⟩
    else none

def accesses (array : Nat) (known : HybridAffine.Known) : ReadCode → Option (List Linear)
  | .pure .. | .register .. => some []
  | .memory a j => if a = array then return [(← AffineAddress.parse (← HybridAffine.value known j)).linear] else some []
  | .bind first next => return (← accesses array known first) ++
      (← accesses array (HybridAffine.read known first::known) next)
  | .branch _ yes no => return (← accesses array known yes) ++ (← accesses array known no)

structure RootCompiled (array depth : Nat) (coefficient : Int) (offsets : List Int) (source : ReadCode) where
  code : ReadCode
  guards : List Linear
  arrays : ∀ allowed, source.ArraysWithin allowed → code.ArraysWithin allowed
  word : ∀ locals temps, WordRead locals temps source → WordRead (bufferWords depth locals) temps code
  correct : ∀ i, Valid guards i → ∀ (data : Array Int) (values locals : List Int) (s : State) (x y : Int),
    s.arrays array = data → Matches (arrayInput data) (keys coefficient offsets i) values → locals.length = depth →
    code.eval i x y s (locals++values) [] = source.eval i x y s locals []

def compileRoot (array depth : Nat) (coefficient : Int) (offsets : List Int) (source : ReadCode) :
    Option (RootCompiled array depth coefficient offsets source) := do
  let c ← compile array depth coefficient offsets [] source
  return ⟨c.code,c.guards,c.arrays,c.word,by
    intro i valid data values locals s x y hf hh hl
    exact c.correct i valid data values locals [] s x y hf hh hl (by intro k v h; simp at h)⟩
end IRComparison.HybridSymbolicRead
