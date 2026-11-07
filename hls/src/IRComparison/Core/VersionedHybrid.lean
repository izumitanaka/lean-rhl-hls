import IRComparison.Hybrid.HybridSource
import IRComparison.Core.Functional

namespace IRComparison.VersionedHybrid

/-- Each environment entry is an immutable state value. Binding a new value
    preserves older versions, accessible by their de Bruijn index. -/
inductive Term where
  | letValue (version : Nat) (value : HybridIR.ReadCode) (next : Term)
  | yield (version : Nat)
  | letSet (version reg : Nat) (value : HybridIR.ReadCode) (next : Term)
  | letWrite (version array : Nat) (address value : HybridIR.ReadCode) (next : Term)
  | letResult (version : Nat) (body next : Term)
  | bindResult (body next : Term)
  | branch (version : Nat) (condition : HybridIR.ReadCode) (yes no : Term)
  | iterate (version count : Nat) (body next : Term)
  | forRange (version : Nat) (count : HybridIR.ReadCode) (body next : Term)
  | forRangeCaptured (version : Nat) (count : HybridIR.ReadCode) (body next : Term)
  deriving Repr

def Term.eval (i x y : Int) (term : Term) (env : List State) (locals : List Int := []) : Option State :=
  match term with
  | .yield v => env[v]?
  | .letValue v e b => do
      let s ← env[v]?
      let value ← e.eval i x y s locals []
      b.eval i x y env (value :: locals)
  | .letSet v r e b => do
      let s ← env[v]?
      let value ← e.eval i x y s locals []
      b.eval i x y (s.set r value :: env) locals
  | .letWrite v a j e b => do
      let s ← env[v]?
      let t ← s.write a (← j.eval i x y s locals []) (← e.eval i x y s locals [])
      b.eval i x y (t :: env) locals
  | .bindResult body next => do
      let t ← body.eval i x y env locals
      next.eval i x y (t :: env) locals
  | .letResult v body next => do
      let s ← env[v]?
      let t ← body.eval i x y [s] locals
      next.eval i x y (t :: env) locals
  | .branch v e a b => do
      let s ← env[v]?
      if (← e.eval i x y s locals []) != 0 then a.eval i x y env locals else b.eval i x y env locals
  | .iterate v n body next => do
      let s ← env[v]?
      let t ← (List.range n).foldlM (fun t _ => body.eval i x y [t] locals) s
      next.eval i x y (t :: env) locals
  | .forRange v count body next => do
      let s ← env[v]?
      let n ← count.eval i x y s locals []
      let t ← (List.range n.toNat).foldlM (fun t k => body.eval i x y [t] (Int.ofNat k :: locals)) s
      next.eval i x y (t :: env) locals
  | .forRangeCaptured v count body next => do
      let s ← env[v]?
      let n ← count.eval i x y s locals []
      let t ← (List.range n.toNat).foldlM (fun t k => body.eval i x y (t :: env) (Int.ofNat k :: locals)) s
      next.eval i x y (t :: env) locals


def ofFunctional : Functional.Term → Term
  | .yield v => .yield v
  | .letValue v e b => .letValue v (HybridIR.extract e) (ofFunctional b)
  | .letSet v r e b => .letSet v r (HybridIR.extract e) (ofFunctional b)
  | .letWrite v a j e b => .letWrite v a (HybridIR.extract j) (HybridIR.extract e) (ofFunctional b)
  | .bindResult b n => .bindResult (ofFunctional b) (ofFunctional n)
  | .letResult v b n => .letResult v (ofFunctional b) (ofFunctional n)
  | .branch v e a b => .branch v (HybridIR.extract e) (ofFunctional a) (ofFunctional b)
  | .iterate v n b next => .iterate v n (ofFunctional b) (ofFunctional next)
  | .forRange v e b next => .forRange v (HybridIR.extract e) (ofFunctional b) (ofFunctional next)
  | .forRangeCaptured v e b next => .forRangeCaptured v (HybridIR.extract e) (ofFunctional b) (ofFunctional next)

theorem ofFunctional_correct (term : Functional.Term) :
    (ofFunctional term).eval i x y env ls = term.eval i x y env ls := by
  induction term generalizing env ls <;>
    simp_all [ofFunctional,Term.eval,Functional.Term.eval,HybridIR.extract_correct]

end IRComparison.VersionedHybrid
