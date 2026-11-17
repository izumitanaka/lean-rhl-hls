import IRComparison.Hybrid.HybridAddress
import IRComparison.Memory.WindowCoverage
import IRComparison.Memory.BufferRules

namespace IRComparison.HybridWindowRead
open HybridIR WindowSchedule

def bounded (depth : Nat) : Value → Bool
  | .local n => n < depth
  | .wrap32 e => bounded depth e
  | .natIndex e => bounded depth e
  | .add a b | .sub a b | .mul a b | .div a b => bounded depth a && bounded depth b
  | _ => true

theorem bounded_correct (e : Value) (h : bounded depth e = true) (len : locals.length = depth) :
    e.eval i x y (locals++values) temps = e.eval i x y locals temps := by
  induction e with
  | lit | index | left | right | temp => rfl
  | «local» n =>
    have hn : n < locals.length := by simpa [bounded,len] using h
    simp [Value.eval,List.getElem?_append,hn]
  | natIndex e ih | wrap32 e ih => simp only [Value.eval,ih h]
  | add a b ha hb | sub a b ha hb | mul a b ha hb | div a b ha hb =>
    simp only [bounded,Bool.and_eq_true] at h
    simp only [Value.eval,ha h.1,hb h.2]

structure Compiled (i : Int) (array depth : Nat) (keys : List Int) (known : HybridAddress.Known) (source : ReadCode) where
  code : ReadCode
  correct : ∀ (data : Array Int) (values locals temps : List Int) (s : State) (x y : Int),
    s.arrays array = data → Matches (arrayInput data) keys values → locals.length = depth →
    HybridAddress.Matches known temps →
    code.eval i x y s (locals++values) temps = source.eval i x y s locals temps

/-- Tr-ReadMem instantiated with the lexical binding representation of the
mixed IR. The buffer shape and the address-analysis strategy are not rules. -/
theorem readMem_rule (held : Matches (arrayInput (s.arrays array)) keys values)
    (found : keys[k]? = some key) (len : locals.length = depth)
    (addressValue : address.eval i x y locals temps = some key) :
    (ReadCode.pure (.local (depth+k))).eval i x y s (locals++values) temps =
      (ReadCode.memory array address).eval i x y s locals temps := by
  obtain ⟨_,point⟩ := held
  obtain ⟨v,hv,hi⟩ := point k key found
  have primitive := BufferRules.readMem_rule hi
  have equality := Relational.eq_of_translation
    (Relational.consequence primitive (fun _ _ (_ : Eq _ _) => True.intro) (fun _ _ h => h)) ()
  simp only [ReadCode.eval,Value.eval,addressValue]
  rw [List.getElem?_append_right (by omega)]
  simpa [len,hv,arrayInput] using equality.symm

def compile (i : Int) (array depth : Nat) (keys : List Int) (known : HybridAddress.Known) :
    (source : ReadCode) → Option (Compiled i array depth keys known source)
  | .pure v => if hb : bounded depth v = true then
      some ⟨.pure v,by intro data values locals temps s x y frozen held len hm; exact bounded_correct v hb len⟩ else none
  | .register r => some ⟨.register r,by intros; rfl⟩
  | .memory a address =>
    if same : a = array then
      match ha : HybridAddress.value i known address with
      | none => none
      | some key => do
        let j ← slot key keys
        return ⟨.pure (.local (depth+j.val)),by
          intro data values locals temps s x y frozen held len hm
          subst a
          exact readMem_rule (by simpa [frozen] using held) j.property len
            (HybridAddress.value_correct address ha hm)⟩
    else if hb : bounded depth address = true then
      some ⟨.memory a address,by
        intro data values locals temps s x y frozen held len hm
        simp only [ReadCode.eval,bounded_correct address hb len]⟩
    else none
  | .bind first next => do
    let a ← compile i array depth keys known first
    let b ← compile i array depth keys (HybridAddress.read i known first::known) next
    return ⟨.bind a.code b.code,by
      intro data values locals temps s x y frozen held len hm
      simp only [ReadCode.eval,a.correct data values locals temps s x y frozen held len hm]
      cases he : first.eval i x y s locals temps with
      | none => rfl
      | some v => exact b.correct data values locals (v::temps) s x y frozen held len (HybridAddress.after_read hm he)⟩
  | .branch c yes no =>
    if hb : bounded depth c = true then do
      let a ← compile i array depth keys known yes
      let b ← compile i array depth keys known no
      return ⟨.branch c a.code b.code,by
        intro data values locals temps s x y frozen held len hm
        simp only [ReadCode.eval,bounded_correct c hb len,
          a.correct data values locals temps s x y frozen held len hm,
          b.correct data values locals temps s x y frozen held len hm]⟩
    else none

/-- Inspect the mixed read operations directly, including both conditional
    branches. Unknown addresses are misses, not a restriction on the source. -/
def accesses (i : Int) (array : Nat) (known : HybridAddress.Known) : ReadCode → Option (List Int)
  | .pure .. | .register .. => some []
  | .memory a j => if a = array then return [← HybridAddress.value i known j] else some []
  | .bind first next => return (← accesses i array known first) ++
      (← accesses i array (HybridAddress.read i known first::known) next)
  | .branch _ yes no => return (← accesses i array known yes) ++ (← accesses i array known no)

structure RootCompiled (i : Int) (array depth : Nat) (keys : List Int) (source : ReadCode) where
  code : ReadCode
  correct : ∀ (data : Array Int) (values locals : List Int) (s : State) (x y : Int),
    s.arrays array = data → Matches (arrayInput data) keys values → locals.length = depth →
    code.eval i x y s (locals++values) [] = source.eval i x y s locals []

def compileRoot (i : Int) (array depth : Nat) (keys : List Int) (source : ReadCode) :
    Option (RootCompiled i array depth keys source) := do
  let c ← compile i array depth keys [] source
  return ⟨c.code,by
    intro data values locals s x y hf hh hl
    exact c.correct data values locals [] s x y hf hh hl (by intro k v h; simp at h)⟩

end IRComparison.HybridWindowRead
