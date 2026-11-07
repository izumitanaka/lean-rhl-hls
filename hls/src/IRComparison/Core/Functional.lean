import IRComparison.Core.Common

namespace IRComparison.Functional

/-- Each environment entry is an immutable state value. Binding a new value
    preserves older versions, accessible by their de Bruijn index. -/
inductive Term where
  | letValue (version : Nat) (value : Expr) (next : Term)
  | yield (version : Nat)
  | letSet (version reg : Nat) (value : Expr) (next : Term)
  | letWrite (version array : Nat) (address value : Expr) (next : Term)
  | letResult (version : Nat) (body next : Term)
  | bindResult (body next : Term)
  | branch (version : Nat) (condition : Expr) (yes no : Term)
  | iterate (version count : Nat) (body next : Term)
  | forRange (version : Nat) (count : Expr) (body next : Term)
  | forRangeCaptured (version : Nat) (count : Expr) (body next : Term)
  deriving Repr

def Term.eval (i x y : Int) (term : Term) (env : List State) (locals : List Int := []) : Option State :=
  match term with
  | .yield v => env[v]?
  | .letValue v e b => do
      let s ← env[v]?
      let value ← e.eval i x y s locals
      b.eval i x y env (value :: locals)
  | .letSet v r e b => do
      let s ← env[v]?
      let value ← e.eval i x y s locals
      b.eval i x y (s.set r value :: env) locals
  | .letWrite v a j e b => do
      let s ← env[v]?
      let t ← s.write a (← j.eval i x y s locals) (← e.eval i x y s locals)
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
      if (← e.eval i x y s locals) != 0 then a.eval i x y env locals else b.eval i x y env locals
  | .iterate v n body next => do
      let s ← env[v]?
      let t ← (List.range n).foldlM (fun t _ => body.eval i x y [t] locals) s
      next.eval i x y (t :: env) locals
  | .forRange v count body next => do
      let s ← env[v]?
      let n ← count.eval i x y s locals
      let t ← (List.range n.toNat).foldlM (fun t k => body.eval i x y [t] (Int.ofNat k :: locals)) s
      next.eval i x y (t :: env) locals
  | .forRangeCaptured v count body next => do
      let s ← env[v]?
      let n ← count.eval i x y s locals
      let t ← (List.range n.toNat).foldlM (fun t k => body.eval i x y (t :: env) (Int.ofNat k :: locals)) s
      next.eval i x y (t :: env) locals


/-- The target carries a pair (previous input value, user state).
    No imperative Machine or imperative correctness theorem is used. -/
def carriedLoop (input : Input) (step : Step σ) (stride : Int) :
    Nat → Int → (Int × σ) → Option (Int × σ)
  | 0, _, state => some state
  | n+1, i, state => do
      let next ← input (i + stride)
      let result ← step i state.1 next state.2
      carriedLoop input step stride n (i + stride) (next,result)

theorem carriedLoop_correct (input : Input) (step : Step σ) (stride : Int)
    (n : Nat) (i prev : Int) (s : σ) (h : input i = some prev) :
    (carriedLoop input step stride n i (prev,s)).map Prod.snd =
      sourceLoop input step stride n i s := by
  induction n generalizing i prev s with
  | zero => rfl
  | succ n ih =>
      simp only [carriedLoop, sourceLoop, h]
      cases hr : input (i + stride) with
      | none => simp
      | some next =>
          cases ht : step i prev next s with
          | none => simp [ht]
          | some t => simpa [ht] using ih (i + stride) next t hr

def runCarried (input : Input) (step : Step σ) (stride : Int)
    (n : Nat) (i : Int) (s : σ) : Option σ :=
  match n with
  | 0 => some s
  | n+1 => do
      let first ← input i
      (carriedLoop input step stride (n+1) i (first,s)).map Prod.snd

theorem runCarried_correct (input : Input) (step : Step σ) (stride : Int)
    (n : Nat) (i : Int) (s : σ) :
    runCarried input step stride n i s = sourceLoop input step stride n i s := by
  cases n with
  | zero => rfl
  | succ n =>
      simp only [runCarried]
      cases h : input i with
      | none => simp [sourceLoop, h]
      | some first => exact carriedLoop_correct input step stride (n+1) i first s h

inductive Program where
  | loop (start stride : Int) (count : Nat) (leftOffset rightOffset : Int) (body : Term)
  | carried (start stride : Int) (count : Nat) (offset : Int) (body : Term)
  | value (body : Term)
  | letResult (first next : Program)
  | branch (reg : Nat) (yes no : Program)

def Program.eval (input : Input) : Program → State → Option State
  | .loop i d n l r b, s => readLoop input (fun i x y s => b.eval i x y [s]) d l r n i s
  | .carried i d n offset b, s =>
      runCarried (fun j => input (j + offset)) (fun i x y s => b.eval i x y [s]) d n i s
  | .value b, s => b.eval 0 0 0 [s]
  | .letResult a b, s => do b.eval input (← a.eval input s)
  | .branch r a b, s => if s.regs r != 0 then a.eval input s else b.eval input s

def transform : Program → Program
  | .loop i d n l r b =>
      if r = l + d then .carried i d n l b else .loop i d n l r b
  | .carried i d n l b => .carried i d n l b
  | .value b => .value b
  | .letResult a b => .letResult (transform a) (transform b)
  | .branch r a b => .branch r (transform a) (transform b)

theorem transform_correct (p : Program) (input : Input) (s : State) :
    (transform p).eval input s = p.eval input s := by
  induction p generalizing s with
  | loop i d n l r b =>
      by_cases h : r = l + d
      · subst r
        simp [transform, Program.eval, runCarried_correct, readLoop_overlap]
      · simp [transform, h]
  | carried => rfl
  | value => rfl
  | letResult a b ha hb => simp [transform, Program.eval, ha, hb]
  | branch r a b ha hb => simp [transform, Program.eval, ha, hb]

end IRComparison.Functional
