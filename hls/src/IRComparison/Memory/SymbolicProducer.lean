import IRComparison.Memory.StreamProducer
import IRComparison.Core.AffineAddress

namespace IRComparison.SymbolicProducer
open StreamState StreamProducer AffineAddress

def keys (writes : List Linear) (i : Int) : List Int := writes.map (fun a => a.eval i)

inductive Safe (size : Nat) : List Int → List Int → Prop where
  | nil : Safe size before []
  | cons : 0 ≤ key → key < (size:Int) → key ∉ before → Safe size (before++[key]) rest →
      Safe size before (key::rest)

theorem Safe.append (h : Safe size before (a++b)) :
    Safe size before a ∧ Safe size (before++a) b := by
  induction a generalizing before with
  | nil => simpa using And.intro (Safe.nil (before:=before) (size:=size)) h
  | cons key rest ih =>
    cases h with
    | cons lo hi fresh next =>
      obtain ⟨ha,hb⟩ := ih next
      exact ⟨.cons lo hi fresh ha,by simpa [List.append_assoc] using hb⟩

structure Compiled (array size : Nat) (source : Imperative.Cmd) where
  code : StreamProducer.Cmd
  writes : List Linear
  guards : List Linear
  correct : ∀ i, Valid guards i → ∀ before s t q x y ls,
    Safe size before (keys writes i) → Related array size before s t q →
    StreamState.Result array size (before++keys writes i) (source.eval i x y s ls) (code.eval i x y t q ls)

def sequence (a : Compiled array size first) (b : Compiled array size second) :
    Compiled array size (.seq first second) where
  code := .seq a.code b.code
  writes := a.writes++b.writes
  guards := a.guards++b.guards
  correct := by
    intro i valid before s t q x y ls safe h
    simp only [keys,List.map_append] at safe ⊢
    obtain ⟨ha,hb⟩ := safe.append
    have ar := a.correct i (fun g hg => valid g (List.mem_append_left _ hg)) before s t q x y ls ha h
    cases hs : first.eval i x y s ls <;> cases ht : a.code.eval i x y t q ls <;>
      simp only [hs,ht] at ar
    · simp only [Imperative.Cmd.eval,StreamProducer.Cmd.eval,hs,ht,bind,Option.bind]; exact .none
    · cases ar
    · cases ar
    · rename_i u pair
      obtain ⟨v,qs⟩ := pair
      cases ar with
      | some hr =>
        simpa only [Imperative.Cmd.eval,StreamProducer.Cmd.eval,hs,ht,bind,Option.bind,keys,List.append_assoc] using
          b.correct i (fun g hg => valid g (List.mem_append_right _ hg)) _ u v qs x y ls hb hr

def compile (array size : Nat) : (source : Imperative.Cmd) → Option (Compiled array size source)
  | .skip => some ⟨.skip,[],[],by intro i valid before s t q x y ls safe h; simpa [keys] using StreamState.Result.some h⟩
  | .assign r e =>
    if safe : avoids array e = true then
      some ⟨.assign r e,[],[],by
        intro i valid before s t q x y ls trace h
        simp only [Imperative.Cmd.eval,StreamProducer.Cmd.eval,← expr_correct e safe h.agree,keys,List.map_nil,List.append_nil]
        cases he : e.eval i x y s ls with
        | none => exact .none
        | some v => exact .some (h.set r v)⟩
    else none
  | .store a j e =>
    if safe : avoids array e = true then
      if same : a = array then do
        let address ← AffineAddress.parse j
        return ⟨.send e,[address.linear],address.guards,by
          intro i valid before s t q x y ls trace h
          have hj := address.correct i x y s ls valid
          simp only [keys,List.map_cons,List.map_nil] at trace
          cases trace with
          | cons lo hi fresh next =>
            simp only [Imperative.Cmd.eval,StreamProducer.Cmd.eval,← expr_correct e safe h.agree,hj,bind,Option.bind,same,keys,List.map_cons,List.map_nil]
            cases he : e.eval i x y s ls with
            | none => exact .none
            | some v => exact h.send ⟨lo,hi⟩ fresh v⟩
      else if safeJ : avoids array j = true then
        some ⟨.store a j e,[],[],by
          intro i valid before s t q x y ls trace h
          simp only [Imperative.Cmd.eval,StreamProducer.Cmd.eval,← expr_correct e safe h.agree,← expr_correct j safeJ h.agree,keys,List.map_nil,List.append_nil]
          cases hj : j.eval i x y s ls with
          | none => exact .none
          | some index =>
            cases he : e.eval i x y s ls with
            | none => exact .none
            | some value =>
              have hw := h.write_other same index value
              cases hh : t.write a index value <;> simpa [hh] using hw⟩
      else none
    else none
  | .letValue e body =>
    if safe : avoids array e = true then do
      let cb ← compile array size body
      return ⟨.letValue e cb.code,cb.writes,cb.guards,by
        intro i valid before s t q x y ls trace h
        simp only [Imperative.Cmd.eval,StreamProducer.Cmd.eval,← expr_correct e safe h.agree]
        cases he : e.eval i x y s ls with
        | none => exact .none
        | some v => exact cb.correct i valid before s t q x y (v::ls) trace h⟩
    else none
  | .seq a b => do return sequence (← compile array size a) (← compile array size b)
  | .branch e a b =>
    if safe : avoids array e = true then do
      let ca ← compile array size a
      let cb ← compile array size b
      if same : ca.writes = cb.writes then
        return ⟨.branch e ca.code cb.code,ca.writes,ca.guards++cb.guards,by
          intro i valid before s t q x y ls trace h
          simp only [Imperative.Cmd.eval,StreamProducer.Cmd.eval,← expr_correct e safe h.agree]
          cases he : e.eval i x y s ls with
          | none => exact .none
          | some v =>
            simp only [bind,Option.bind]
            split
            · exact ca.correct i (fun g hg => valid g (List.mem_append_left _ hg)) before s t q x y ls trace h
            · rw [same] at trace ⊢
              exact cb.correct i (fun g hg => valid g (List.mem_append_right _ hg)) before s t q x y ls trace h⟩
      else none
    else none
  | .repeat .. | .forRange .. => none

end IRComparison.SymbolicProducer
