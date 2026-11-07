import IRComparison.Hybrid.HybridValues
import IRComparison.Memory.StreamProducer

namespace IRComparison.HybridIR

/-- State updates and send operations are sequenced. Queue values are not
    operands in Value or ReadCode, so source code cannot reuse an old queue. -/
inductive Cmd where
  | skip
  | letValue (value : ReadCode) (body : Cmd)
  | assign (reg : Nat) (value : ReadCode)
  | store (array : Nat) (address value : ReadCode)
  | send (value : ReadCode)
  | seq (first second : Cmd)
  | branch (condition : ReadCode) (yes no : Cmd)
  | repeat (count : Nat) (body : Cmd)
  | forRange (count : ReadCode) (body : Cmd)
  deriving Repr, DecidableEq

def Cmd.eval (i x y : Int) : Cmd → State → List Int → List Int → Option (State × List Int)
  | .skip,s,q,_ => some (s,q)
  | .letValue e b,s,q,ls => do b.eval i x y s q ((← e.eval i x y s ls [])::ls)
  | .assign r e,s,q,ls => do return (s.set r (← e.eval i x y s ls []),q)
  | .store a j e,s,q,ls => do return (← s.write a (← j.eval i x y s ls []) (← e.eval i x y s ls []),q)
  | .send e,s,q,ls => do return (s,q++[← e.eval i x y s ls []])
  | .seq a b,s,q,ls => do
      let (t,qs) ← a.eval i x y s q ls
      b.eval i x y t qs ls
  | .branch e a b,s,q,ls => do
      if (← e.eval i x y s ls []) != 0 then a.eval i x y s q ls else b.eval i x y s q ls
  | .repeat n b,s,q,ls => (List.range n).foldlM (fun (t,qs) _ => b.eval i x y t qs ls) (s,q)
  | .forRange e b,s,q,ls => do
      let n ← e.eval i x y s ls []
      (List.range n.toNat).foldlM (fun (t,qs) k => b.eval i x y t qs (Int.ofNat k::ls)) (s,q)

theorem fold_lift {f : State → α → Option State} {g : State × List Int → α → Option (State × List Int)}
    (h : ∀ s q a, g (s,q) a = (f s a).map (fun t => (t,q))) (as : List α) (s : State) (q : List Int) :
    as.foldlM g (s,q) = (as.foldlM f s).map (fun t => (t,q)) := by
  induction as generalizing s with
  | nil => rfl
  | cons a as ih =>
    simp only [List.foldlM_cons,h]
    cases f s a with
    | none => rfl
    | some t => exact ih t

end IRComparison.HybridIR
