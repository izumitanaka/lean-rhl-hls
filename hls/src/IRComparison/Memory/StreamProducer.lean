import IRComparison.Memory.StreamState

namespace IRComparison.StreamProducer
open StreamState

/-- `send` transmits a value only. Its source index and bounds are proved at
    compilation and are absent from the executable instruction. -/
inductive Cmd where
  | skip
  | letValue (value : Expr) (body : Cmd)
  | assign (reg : Nat) (value : Expr)
  | store (array : Nat) (address value : Expr)
  | send (value : Expr)
  | seq (first second : Cmd)
  | branch (condition : Expr) (yes no : Cmd)
  deriving Repr, DecidableEq

def Cmd.eval (i x y : Int) : Cmd → State → List Int → List Int → Option (State × List Int)
  | .skip,s,q,_ => some (s,q)
  | .letValue e b,s,q,ls => do b.eval i x y s q ((← e.eval i x y s ls)::ls)
  | .assign r e,s,q,ls => do return (s.set r (← e.eval i x y s ls),q)
  | .store a j e,s,q,ls => do return (← s.write a (← j.eval i x y s ls) (← e.eval i x y s ls),q)
  | .send e,s,q,ls => do return (s,q++[← e.eval i x y s ls])
  | .seq a b,s,q,ls => do
      let (t,qs) ← a.eval i x y s q ls
      b.eval i x y t qs ls
  | .branch e a b,s,q,ls => do
      if (← e.eval i x y s ls) != 0 then a.eval i x y s q ls else b.eval i x y s q ls

structure Compiled (i : Int) (array size : Nat) (before : List Int) (source : Imperative.Cmd) where
  code : Cmd
  after : List Int
  correct : ∀ s t q x y ls, Related array size before s t q →
    Result array size after (source.eval i x y s ls) (code.eval i x y t q ls)

def sequence (a : Compiled i array size before first) (b : Compiled i array size a.after second) :
    Compiled i array size before (.seq first second) where
  code := .seq a.code b.code
  after := b.after
  correct := by
    intro s t q x y ls h
    have ha := a.correct s t q x y ls h
    cases hs : first.eval i x y s ls <;> cases ht : a.code.eval i x y t q ls <;>
      simp only [hs,ht] at ha
    · simp only [Imperative.Cmd.eval,Cmd.eval,hs,ht,bind,Option.bind]; exact .none
    · cases ha
    · cases ha
    · rename_i u pair
      obtain ⟨v,qs⟩ := pair
      cases ha with
      | some hr =>
        simpa only [Imperative.Cmd.eval,Cmd.eval,hs,ht,bind,Option.bind] using b.correct u v qs x y ls hr

def compile (i : Int) (array size : Nat) (before : List Int) :
    (source : Imperative.Cmd) → Option (Compiled i array size before source)
  | .skip => some ⟨.skip,before,by intro s t q x y ls h; exact .some h⟩
  | .assign r e =>
    if safe : avoids array e = true then
      some ⟨.assign r e,before,by
        intro s t q x y ls h
        simp only [Imperative.Cmd.eval,Cmd.eval,← expr_correct e safe h.agree]
        cases he : e.eval i x y s ls with
        | none => exact .none
        | some v => exact .some (h.set r v)⟩
    else none
  | .store a j e =>
    if safe : avoids array e = true then
      if same : a = array then do
        let key ← NativeWindowExpr.address i j
        if address : NativeWindowExpr.address i j = some key then
          if bounds : 0 ≤ key ∧ key < (size:Int) then
            if fresh : key ∉ before then
              return ⟨.send e,before++[key],by
                intro s t q x y ls h
                have hj := NativeWindowExpr.address_correct address (s:=s) (ls:=ls) (x:=x) (y:=y)
                simp only [Imperative.Cmd.eval,Cmd.eval,← expr_correct e safe h.agree,hj,bind,Option.bind,same]
                cases he : e.eval i x y s ls with
                | none => exact .none
                | some v => exact h.send bounds fresh v⟩
            else none
          else none
        else none
      else if safeJ : avoids array j = true then
        some ⟨.store a j e,before,by
          intro s t q x y ls h
          simp only [Imperative.Cmd.eval,Cmd.eval,← expr_correct e safe h.agree,← expr_correct j safeJ h.agree]
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
      let cb ← compile i array size before body
      return ⟨.letValue e cb.code,cb.after,by
        intro s t q x y ls h
        simp only [Imperative.Cmd.eval,Cmd.eval,← expr_correct e safe h.agree]
        cases he : e.eval i x y s ls with
        | none => exact .none
        | some v => exact cb.correct s t q x y (v::ls) h⟩
    else none
  | .seq a b => do
    let ca ← compile i array size before a
    let cb ← compile i array size ca.after b
    return sequence ca cb
  | .branch e a b =>
    if safe : avoids array e = true then do
      let ca ← compile i array size before a
      let cb ← compile i array size before b
      if same : ca.after = cb.after then
        return ⟨.branch e ca.code cb.code,ca.after,by
          intro s t q x y ls h
          simp only [Imperative.Cmd.eval,Cmd.eval,← expr_correct e safe h.agree]
          cases he : e.eval i x y s ls with
          | none => exact .none
          | some v =>
            simp only [bind,Option.bind]
            split
            · exact ca.correct s t q x y ls h
            · exact same ▸ cb.correct s t q x y ls h⟩
      else none
    else none
  | .repeat .. | .forRange .. => none

end IRComparison.StreamProducer
