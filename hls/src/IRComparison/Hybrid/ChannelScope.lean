import IRComparison.Hybrid.ChannelBody

namespace IRComparison.ChannelScope
open HybridIR

/-- Move the varying task index into a lexical slot. Missing source locals
remain missing even though the target has extra private loop bindings. -/
def value (width padding : Nat) : Value → Value
  | .index => .local width
  | .local n => .local (if n < width then n else width+padding)
  | .wrap32 e => .wrap32 (value width padding e)
  | .natIndex e => .natIndex (value width padding e)
  | .add a b => .add (value width padding a) (value width padding b)
  | .sub a b => .sub (value width padding a) (value width padding b)
  | .mul a b => .mul (value width padding a) (value width padding b)
  | .div a b => .div (value width padding a) (value width padding b)
  | e => e

def read (width padding : Nat) : ReadCode → ReadCode
  | .pure e => .pure (value width padding e)
  | .memory a e => .memory a (value width padding e)
  | .register r => .register r
  | .bind a b => .bind (read width padding a) (read width padding b)
  | .branch c a b => .branch (value width padding c) (read width padding a) (read width padding b)

def body (width padding : Nat) : MemoryCmd → MemoryCmd
  | .skip => .skip
  | .assign r e => .assign r (read width padding e)
  | .store a j e => .store a (read width padding j) (read width padding e)
  | .seq a b => .seq (body width padding a) (body width padding b)
  | .branch e a b => .branch (read width padding e) (body width padding a) (body width padding b)
  | .letValue e b => .letValue (read width padding e) (body (width+1) padding b)
  | .repeat n b => .repeat n (body width padding b)
  | .forRange e b => .forRange (read width padding e) (body (width+1) padding b)

theorem value_correct (e : Value) (size : ls.length = width) (extraSize : extra.length = padding)
    (index : extra[0]? = some i) :
    (value width padding e).eval outer x y (ls++extra) ts = e.eval i x y ls ts := by
  induction e with
  | index =>
    simp only [value,Value.eval,← size]
    rw [List.getElem?_append_right (by omega : ls.length ≤ ls.length)]
    simpa using index
  | «local» n =>
    by_cases hn : n < width
    · simp [value,Value.eval,hn,List.getElem?_append_left (by omega : n < ls.length)]
    · have hnone : ls[n]? = none := List.getElem?_eq_none (by omega)
      simp only [value,Value.eval,hn,ite_false,hnone]
      exact List.getElem?_eq_none (by simp [size,extraSize])
  | lit | left | right | temp => rfl
  | natIndex e ih | wrap32 e ih => simp only [value,Value.eval,ih]
  | add a b ia ib | sub a b ia ib | mul a b ia ib | div a b ia ib =>
    simp only [value,Value.eval,ia,ib]

theorem read_correct (e : ReadCode) (size : ls.length = width) (extraSize : extra.length = padding)
    (index : extra[0]? = some i) :
    (read width padding e).eval outer x y s (ls++extra) ts = e.eval i x y s ls ts := by
  induction e generalizing ts with
  | pure e => exact value_correct e size extraSize index
  | register => rfl
  | memory a e => simp only [read,ReadCode.eval,value_correct e size extraSize index]
  | bind a b ia ib => simp only [read,ReadCode.eval,ia,ib]
  | branch c a b ia ib => simp only [read,ReadCode.eval,value_correct c size extraSize index,ia,ib]

private theorem fold_eq (items : List α) (f g : State → α → Option State)
    (same : ∀ s a, f s a = g s a) : items.foldlM f s = items.foldlM g s := by
  have eq : f = g := funext fun s => funext (same s)
  rw [eq]

theorem body_correct (c : MemoryCmd) (size : ls.length = width) (extraSize : extra.length = padding)
    (index : extra[0]? = some i) :
    (body width padding c).eval outer x y s (ls++extra) = c.eval i x y s ls := by
  induction c generalizing width ls s with
  | skip => rfl
  | assign r e => simp only [body,MemoryCmd.eval,read_correct e size extraSize index]
  | store a j e => simp only [body,MemoryCmd.eval,read_correct j size extraSize index,read_correct e size extraSize index]
  | seq a b ia ib => simp only [body,MemoryCmd.eval,ia size,ib size]
  | branch e a b ia ib => simp only [body,MemoryCmd.eval,read_correct e size extraSize index,ia size,ib size]
  | letValue e b ih =>
    simp only [body,MemoryCmd.eval,read_correct e size extraSize index]
    cases e.eval i x y s ls [] with
    | none => rfl
    | some v => simpa only [bind,Option.bind,List.cons_append] using ih (ls:=v::ls) (by simp [size])
  | «repeat» n b ih =>
    exact fold_eq _ _ _ (fun s _ => ih (s:=s) size)
  | forRange e b ih =>
    simp only [body,MemoryCmd.eval,read_correct e size extraSize index]
    cases e.eval i x y s ls [] with
    | none => rfl
    | some n =>
      apply fold_eq
      intro s k
      simpa only [List.cons_append] using ih (s:=s) (ls:=(k:Int)::ls) (by simp [size])

end IRComparison.ChannelScope
