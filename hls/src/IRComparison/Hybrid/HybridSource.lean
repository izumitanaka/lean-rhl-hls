import IRComparison.Hybrid.HybridCommands

namespace IRComparison.HybridIR

/-- The mixed computation IR before communication lowering. ReadCode exposes
    reads; pure Value nodes never contain state or communication operations. -/
inductive MemoryCmd where
  | skip
  | letValue (value : ReadCode) (body : MemoryCmd)
  | assign (reg : Nat) (value : ReadCode)
  | store (array : Nat) (address value : ReadCode)
  | seq (first second : MemoryCmd)
  | branch (condition : ReadCode) (yes no : MemoryCmd)
  | repeat (count : Nat) (body : MemoryCmd)
  | forRange (count : ReadCode) (body : MemoryCmd)
  deriving Repr, DecidableEq

def MemoryCmd.eval (i x y : Int) (command : MemoryCmd) (state : State) (locals : List Int := []) : Option State :=
  match command,state,locals with
  | .skip,s,_ => some s
  | .letValue e b,s,ls => do b.eval i x y s ((← e.eval i x y s ls [])::ls)
  | .assign r e,s,ls => do return s.set r (← e.eval i x y s ls [])
  | .store a j e,s,ls => do s.write a (← j.eval i x y s ls []) (← e.eval i x y s ls [])
  | .seq a b,s,ls => do b.eval i x y (← a.eval i x y s ls) ls
  | .branch e a b,s,ls => do
      if (← e.eval i x y s ls []) != 0 then a.eval i x y s ls else b.eval i x y s ls
  | .repeat n b,s,ls => (List.range n).foldlM (fun t _ => b.eval i x y t ls) s
  | .forRange e b,s,ls => do
      let n ← e.eval i x y s ls []
      (List.range n.toNat).foldlM (fun t k => b.eval i x y t (Int.ofNat k::ls)) s

/-- Reuse only the unoptimized input parser, not its window/FIFO passes. -/
def MemoryCmd.fromImperative : Imperative.Cmd → MemoryCmd
  | .skip => .skip
  | .letValue e b => .letValue (extract e) (fromImperative b)
  | .assign r e => .assign r (extract e)
  | .store a j e => .store a (extract j) (extract e)
  | .seq a b => .seq (fromImperative a) (fromImperative b)
  | .branch e a b => .branch (extract e) (fromImperative a) (fromImperative b)
  | .repeat n b => .repeat n (fromImperative b)
  | .forRange e b => .forRange (extract e) (fromImperative b)

theorem MemoryCmd.fromImperative_correct (c : Imperative.Cmd) :
    (fromImperative c).eval i x y s ls = c.eval i x y s ls := by
  induction c generalizing s ls with
  | skip => rfl
  | assign | store => simp [fromImperative,eval,Imperative.Cmd.eval,extract_correct]
  | letValue e b ih => simp [fromImperative,eval,Imperative.Cmd.eval,extract_correct,ih]
  | seq a b ha hb => simp [fromImperative,eval,Imperative.Cmd.eval,ha,hb]
  | branch e a b ha hb => simp [fromImperative,eval,Imperative.Cmd.eval,extract_correct,ha,hb]
  | «repeat» n b ih => simp [fromImperative,eval,Imperative.Cmd.eval,ih]
  | forRange e b ih => simp [fromImperative,eval,Imperative.Cmd.eval,extract_correct,ih]

def MemoryCmd.target : MemoryCmd → Cmd
  | .skip => .skip
  | .letValue e b => .letValue e b.target
  | .assign r e => .assign r e
  | .store a j e => .store a j e
  | .seq a b => .seq a.target b.target
  | .branch e a b => .branch e a.target b.target
  | .repeat n b => .repeat n b.target
  | .forRange e b => .forRange e b.target

theorem MemoryCmd.target_correct (c : MemoryCmd) :
    c.target.eval i x y s q ls = (c.eval i x y s ls).map (fun t => (t,q)) := by
  induction c generalizing s q ls with
  | skip => rfl
  | assign r e => simp only [target,Cmd.eval,eval]; cases e.eval i x y s ls [] <;> rfl
  | store a j e =>
    simp only [target,Cmd.eval,eval]
    cases j.eval i x y s ls [] with
    | none => rfl
    | some k =>
      cases e.eval i x y s ls [] with
      | none => rfl
      | some v => simp only [bind,Option.bind]; cases s.write a k v <;> rfl
  | letValue e b ih =>
    simp only [target,Cmd.eval,eval]
    cases e.eval i x y s ls [] with
    | none => rfl
    | some v => exact ih
  | seq a b ha hb =>
    simp only [target,Cmd.eval,eval,ha]
    cases a.eval i x y s ls with
    | none => rfl
    | some t => exact hb
  | branch e a b ha hb =>
    simp only [target,Cmd.eval,eval]
    cases e.eval i x y s ls [] with
    | none => rfl
    | some v => simp only [bind,Option.bind]; split <;> simp [ha,hb]
  | «repeat» n b ih => exact fold_lift (fun s q _ => ih (s:=s) (q:=q) (ls:=ls)) _ s q
  | forRange e b ih =>
    simp only [target,Cmd.eval,eval]
    cases e.eval i x y s ls [] with
    | none => rfl
    | some n => exact fold_lift (fun s q k => ih (s:=s) (q:=q) (ls:=Int.ofNat k::ls)) _ s q

end IRComparison.HybridIR
