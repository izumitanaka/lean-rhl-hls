import IRComparison.Core.Common

namespace IRComparison.Imperative

inductive Cmd where
  | skip
  | letValue (value : Expr) (body : Cmd)
  | assign (reg : Nat) (value : Expr)
  | store (array : Nat) (address value : Expr)
  | seq (first second : Cmd)
  | branch (condition : Expr) (yes no : Cmd)
  | repeat (count : Nat) (body : Cmd)
  | forRange (count : Expr) (body : Cmd)
  deriving Repr

def Cmd.eval (i x y : Int) (command : Cmd) (s : State) (locals : List Int := []) : Option State :=
  match command with
  | .skip => some s
  | .letValue e b => do
      let v ← e.eval i x y s locals
      b.eval i x y s (v :: locals)
  | .assign r e => do return s.set r (← e.eval i x y s locals)
  | .store a j e => do s.write a (← j.eval i x y s locals) (← e.eval i x y s locals)
  | .seq a b => do b.eval i x y (← a.eval i x y s locals) locals
  | .branch e a b => do
      if (← e.eval i x y s locals) != 0 then a.eval i x y s locals else b.eval i x y s locals
  | .repeat n b => (List.range n).foldlM (fun t _ => b.eval i x y t locals) s
  | .forRange count b => do
      let n ← count.eval i x y s locals
      (List.range n.toNat).foldlM (fun t k => b.eval i x y t (Int.ofNat k :: locals)) s

/-- The private buffer is separate from every source-visible register. -/
structure Machine (σ : Type) where
  data : σ
  buffer : Int

/-- One target iteration: load next; execute body; retain next.
    The buffer is private, so the body cannot overwrite it. -/
def bufferedLoop (input : Input) (step : Step σ) (stride : Int) :
    Nat → Int → Machine σ → Option (Machine σ)
  | 0, _, m => some m
  | n+1, i, m => do
      let next ← input (i + stride)
      let t ← step i m.buffer next m.data
      bufferedLoop input step stride n (i + stride) ⟨t, next⟩

theorem bufferedLoop_correct (input : Input) (step : Step σ) (stride : Int)
    (n : Nat) (i : Int) (m : Machine σ) (h : input i = some m.buffer) :
    (bufferedLoop input step stride n i m).map Machine.data =
      sourceLoop input step stride n i m.data := by
  induction n generalizing i m with
  | zero => rfl
  | succ n ih =>
      simp only [bufferedLoop, sourceLoop, h]
      cases hr : input (i + stride) with
      | none => simp
      | some next =>
          cases ht : step i m.buffer next m.data with
          | none => simp [ht]
          | some t =>
              simpa [ht] using ih (i + stride) ⟨t, next⟩ hr

def runBuffered (input : Input) (step : Step σ) (stride : Int)
    (n : Nat) (i : Int) (s : σ) : Option σ :=
  match n with
  | 0 => some s
  | n+1 => do
      let first ← input i
      (bufferedLoop input step stride (n+1) i ⟨s,first⟩).map Machine.data

theorem runBuffered_correct (input : Input) (step : Step σ) (stride : Int)
    (n : Nat) (i : Int) (s : σ) :
    runBuffered input step stride n i s = sourceLoop input step stride n i s := by
  cases n with
  | zero => rfl
  | succ n =>
      simp only [runBuffered]
      cases h : input i with
      | none => simp [sourceLoop, h]
      | some first =>
          exact bufferedLoop_correct input step stride (n+1) i ⟨s,first⟩ h

/-- A small loop IR with explicit two-read preludes; the body is arbitrary.
    This is a subset of the proposed full IR, not a parser for arbitrary loops. -/
inductive Program where
  | loop (start stride : Int) (count : Nat) (leftOffset rightOffset : Int) (body : Cmd)
  | buffered (start stride : Int) (count : Nat) (offset : Int) (body : Cmd)
  | effect (body : Cmd)
  | seq (a b : Program)
  | branch (reg : Nat) (a b : Program)

def Program.eval (input : Input) : Program → State → Option State
  | .loop i d n l r b, s => readLoop input (fun i x y => b.eval i x y) d l r n i s
  | .buffered i d n offset b, s =>
      runBuffered (fun j => input (j + offset)) (fun i x y => b.eval i x y) d n i s
  | .effect b, s => b.eval 0 0 0 s
  | .seq a b, s => do b.eval input (← a.eval input s)
  | .branch r a b, s => if s.regs r != 0 then a.eval input s else b.eval input s

def transform : Program → Program
  | .loop i d n l r b =>
      if r = l + d then .buffered i d n l b else .loop i d n l r b
  | .buffered i d n l b => .buffered i d n l b
  | .effect b => .effect b
  | .seq a b => .seq (transform a) (transform b)
  | .branch r a b => .branch r (transform a) (transform b)

theorem transform_correct (p : Program) (input : Input) (s : State) :
    (transform p).eval input s = p.eval input s := by
  induction p generalizing s with
  | loop i d n l r b =>
      by_cases h : r = l + d
      · subst r
        simp [transform, Program.eval, runBuffered_correct, readLoop_overlap]
      · simp [transform, h]
  | buffered => rfl
  | effect => rfl
  | seq a b ha hb => simp [transform, Program.eval, ha, hb]
  | branch r a b ha hb => simp [transform, Program.eval, ha, hb]

end IRComparison.Imperative
