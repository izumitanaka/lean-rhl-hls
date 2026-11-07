import IRComparison.Hybrid.HybridWordRead
import IRComparison.Hybrid.HybridSource

namespace IRComparison.HybridWord

def State.set (s : State) (r : Nat) (v : Word) : State :=
  { s with regs := fun k => if k = r then v else s.regs k }

def State.write (s : State) (a : Nat) (j v : Word) : Option State :=
  if h : j.toNat < (s.arrays a).size then
    some { s with arrays := fun k => if k = a then (s.arrays a).set j.toNat v h else s.arrays k }
  else none

theorem State.encode_set (s : State) :
    (s.set r v).encode = s.encode.set r (HybridWord.encode v) := by
  unfold set encode IRComparison.State.set
  congr 1
  funext k
  split <;> simp_all

theorem State.encode_write (s : State) :
    s.encode.write a (HybridWord.encode j) (HybridWord.encode v) = (s.write a j v).map State.encode := by
  simp only [IRComparison.State.write, HybridWord.encode,
    Int.not_lt_of_ge (Int.natCast_nonneg _), ↓reduceIte, Int.toNat_natCast,
    State.encode, Array.size_map, State.write]
  split
  · simp only [Option.map_some]
    congr 2
    funext k
    split <;> simp_all [Array.map_set, HybridWord.encode]
  · rfl

inductive Cmd where
  | skip
  | assign (reg : Nat) (value : Expr)
  | store (array : Nat) (address value : Expr)
  | letValue (value : Expr) (body : Cmd)
  | seq (first second : Cmd)
  | branch (condition : Expr) (yes no : Cmd)
  | repeat (count : Nat) (body : Cmd)
  | forRange (count : Expr) (body : Cmd)

def Cmd.eval (i x y : Word) : Cmd → State → List Word → Option State
  | .skip,s,_ => some s
  | .assign r e,s,ls => do return s.set r (← e.eval i x y s ls)
  | .store a j e,s,ls => do s.write a (← j.eval i x y s ls) (← e.eval i x y s ls)
  | .letValue e b,s,ls => do b.eval i x y s ((← e.eval i x y s ls)::ls)
  | .seq a b,s,ls => do b.eval i x y (← a.eval i x y s ls) ls
  | .branch c a b,s,ls => do
    if (← c.eval i x y s ls) != 0 then a.eval i x y s ls else b.eval i x y s ls
  | .repeat n b,s,ls => (List.range n).foldlM (fun t _ => b.eval i x y t ls) s
  | .forRange e b,s,ls => do
    let n ← e.eval i x y s ls
    (List.range n.toNat).foldlM (fun t k => b.eval i x y t (BitVec.ofNat 32 k::ls)) s

def Cmd.lower : Cmd → HybridIR.MemoryCmd
  | .skip => .skip
  | .assign r e => .assign r e.lower
  | .store a j e => .store a j.lower e.lower
  | .letValue e b => .letValue e.lower b.lower
  | .seq a b => .seq a.lower b.lower
  | .branch c a b => .branch c.lower a.lower b.lower
  | .repeat n b => .repeat n b.lower
  | .forRange e b => .forRange e.lower b.lower

theorem fold_encode (f : State → α → Option State)
    (g : IRComparison.State → α → Option IRComparison.State)
    (h : ∀ s a, g s.encode a = (f s a).map State.encode) (items : List α) (s : State) :
    items.foldlM g s.encode = (items.foldlM f s).map State.encode := by
  induction items generalizing s with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.foldlM_cons, h]
    cases f s a <;> simp_all

theorem fold_encode_on (f : State → α → Option State)
    (g : IRComparison.State → α → Option IRComparison.State) (items : List α)
    (h : ∀ a ∈ items, ∀ s, g s.encode a = (f s a).map State.encode) (s : State) :
    items.foldlM g s.encode = (items.foldlM f s).map State.encode := by
  induction items generalizing s with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.foldlM_cons, h a (by simp)]
    cases f s a <;> simp_all

theorem Cmd.lower_correct_int (i : Int) (c : Cmd) (s : State) (ls : List Word) :
    c.lower.eval i (encode x) (encode y) s.encode (ls.map encode) =
      (c.eval (BitVec.ofInt 32 i) x y s ls).map State.encode := by
  induction c generalizing s ls with
  | skip => rfl
  | assign r e =>
    simp only [lower, HybridIR.MemoryCmd.eval, Expr.lower_correct_int, eval]
    cases e.eval (BitVec.ofInt 32 i) x y s ls <;> simp [State.encode_set]
  | store a j e =>
    simp only [lower, HybridIR.MemoryCmd.eval, Expr.lower_correct_int, eval]
    cases j.eval (BitVec.ofInt 32 i) x y s ls <;> cases e.eval (BitVec.ofInt 32 i) x y s ls <;> simp [State.encode_write]
  | letValue e b ih =>
    simp only [lower, HybridIR.MemoryCmd.eval, Expr.lower_correct_int, eval]
    cases e.eval (BitVec.ofInt 32 i) x y s ls <;> simp [← List.map_cons, ih]
  | seq a b ha hb =>
    simp only [lower, HybridIR.MemoryCmd.eval, ha, eval]
    cases a.eval (BitVec.ofInt 32 i) x y s ls <;> simp [hb]
  | branch e a b ha hb =>
    simp only [lower, HybridIR.MemoryCmd.eval, Expr.lower_correct_int, eval]
    cases e.eval (BitVec.ofInt 32 i) x y s ls <;> simp [encode_eq_zero, ha, hb]
    split <;> rfl
  | «repeat» n b ih =>
    exact fold_encode _ _ (fun s _ => ih s ls) _ s
  | forRange e b ih =>
    simp only [lower, HybridIR.MemoryCmd.eval, Expr.lower_correct_int, eval]
    cases he : e.eval (BitVec.ofInt 32 i) x y s ls with
    | none => rfl
    | some n =>
      simp only [Option.map_some, bind, Option.bind, encode, Int.toNat_natCast]
      apply fold_encode_on
      intro k hk t
      have hk' : k < 2^32 := Nat.lt_trans (List.mem_range.mp hk) n.isLt
      have encoded : encode (BitVec.ofNat 32 k) = Int.ofNat k := by
        simp [encode, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk']
      simpa only [List.map_cons, encoded] using ih t (BitVec.ofNat 32 k::ls)

theorem Cmd.lower_correct (c : Cmd) (s : State) (ls : List Word) :
    c.lower.eval (encode i) (encode x) (encode y) s.encode (ls.map encode) =
      (c.eval i x y s ls).map State.encode := by
  simpa only [decode_encode] using c.lower_correct_int (encode i) s ls

end IRComparison.HybridWord
