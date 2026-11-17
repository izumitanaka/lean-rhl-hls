import IRComparison.Core.Bridge

namespace IRComparison.Source

/-- Ordinary source expressions have no special left/right window operands. -/
inductive Scalar where
  | lit (n : Int)
  | index
  | reg (r : Nat)
  | add (a b : Scalar)
  | sub (a b : Scalar)
  | mul (a b : Scalar)
  | div (a b : Scalar)
  | read (array : Nat) (address : Scalar)
  deriving Repr

def Scalar.lower : Scalar → Expr
  | .lit n => .lit n
  | .index => .index
  | .reg r => .reg r
  | .add a b => .add a.lower b.lower
  | .sub a b => .sub a.lower b.lower
  | .mul a b => .mul a.lower b.lower
  | .div a b => .div a.lower b.lower
  | .read a e => .read a e.lower

def Scalar.eval (i : Int) (s : State) (e : Scalar) : Option Int :=
  e.lower.eval i 0 0 s

theorem Scalar.lower_correct (e : Scalar) (i x y : Int) (s : State) :
    e.lower.eval i x y s = e.eval i s := by
  induction e with
  | lit | index | reg => rfl
  | add a b ha hb | sub a b ha hb | mul a b ha hb | div a b ha hb =>
      simp_all [Scalar.lower, Scalar.eval, Expr.eval]
  | read a e he => simp_all [Scalar.lower, Scalar.eval, Expr.eval]

/-- Iteration count is explicit; each nested loop binds its own index. -/
def iterate (step : Int → State → Option State) (stride : Int) :
    Nat → Int → State → Option State
  | 0, _, s => some s
  | n+1, i, s => do iterate step stride n (i + stride) (← step i s)

theorem iterate_congr (f g : Int → State → Option State)
    (h : ∀ i s, f i s = g i s) (stride : Int) (n : Nat) (i : Int) (s : State) :
    iterate f stride n i s = iterate g stride n i s := by
  have : f = g := funext fun i => funext (h i)
  rw [this]

inductive Cmd where
  | skip
  | assign (reg : Nat) (value : Scalar)
  | store (array : Nat) (address value : Scalar)
  | load (reg : Nat) (address : Scalar)
  | seq (first second : Cmd)
  | branch (condition : Scalar) (yes no : Cmd)
  | loop (start stride : Int) (count : Nat) (body : Cmd)
  deriving Repr

def Cmd.eval (input : Input) (i : Int) : Cmd → State → Option State
  | .skip, s => some s
  | .assign r e, s => do return s.set r (← e.eval i s)
  | .store a j e, s => do s.write a (← j.eval i s) (← e.eval i s)
  | .load r e, s => do return s.set r (← input (← e.eval i s))
  | .seq a b, s => do b.eval input i (← a.eval input i s)
  | .branch e a b, s => do
      if (← e.eval i s) != 0 then a.eval input i s else b.eval input i s
  | .loop start stride n b, s => iterate (fun j => b.eval input j) stride n start s

/-- Syntactic extraction of a residual body with no further input loads.
    Failure is an optimization miss, not a source-language rejection. -/
def localBody : Cmd → Option Imperative.Cmd
  | .skip => some .skip
  | .assign r e => some (.assign r e.lower)
  | .store a j e => some (.store a j.lower e.lower)
  | .seq a b => do return .seq (← localBody a) (← localBody b)
  | .branch e a b => do return .branch e.lower (← localBody a) (← localBody b)
  | .load .. | .loop .. => none

theorem localBody_correct (p : Cmd) (q : Imperative.Cmd) (h : localBody p = some q)
    (input : Input) (i x y : Int) (s : State) :
    q.eval i x y s = p.eval input i s := by
  induction p generalizing q s with
  | skip => cases h; rfl
  | assign r e => cases h; simp [Imperative.Cmd.eval, Cmd.eval, Scalar.lower_correct]
  | store a j e => cases h; simp [Imperative.Cmd.eval, Cmd.eval, Scalar.lower_correct]
  | load | loop => simp [localBody] at h
  | seq a b ha hb =>
      cases h₁ : localBody a with
      | none => simp [localBody, h₁] at h
      | some a' =>
          cases h₂ : localBody b with
          | none => simp [localBody, h₁, h₂] at h
          | some b' =>
              simp [localBody, h₁, h₂] at h
              cases h
              simp [Imperative.Cmd.eval, Cmd.eval, ha _ h₁, hb _ h₂]
  | branch e a b ha hb =>
      cases h₁ : localBody a with
      | none => simp [localBody, h₁] at h
      | some a' =>
          cases h₂ : localBody b with
          | none => simp [localBody, h₁, h₂] at h
          | some b' =>
              simp [localBody, h₁, h₂] at h
              cases h
              simp [Imperative.Cmd.eval, Cmd.eval, Scalar.lower_correct, ha _ h₁, hb _ h₂]

def offset : Scalar → Option Int
  | .index => some 0
  | .add .index (.lit k) => some k
  | .sub .index (.lit k) => some (-k)
  | _ => none

theorem offset_correct (e : Scalar) (k : Int) (h : offset e = some k)
    (i : Int) (s : State) : e.eval i s = some (i + k) := by
  unfold offset at h
  split at h <;> simp_all [Scalar.eval, Scalar.lower, Expr.eval, Int.sub_eq_add_neg] <;> omega

structure Extracted where
  leftOffset : Int
  rightOffset : Int
  body : Imperative.Cmd

/-- Match actual load instructions and retain their destinations, including aliases. -/
def extract : Cmd → Option Extracted
  | .seq (.load r₁ e₁) (.seq (.load r₂ e₂) tail) => do
      let l ← offset e₁
      let r ← offset e₂
      let b ← localBody tail
      return ⟨l, r, .seq (.assign r₁ .left) (.seq (.assign r₂ .right) b)⟩
  | _ => none

theorem extract_correct (p : Cmd) (q : Extracted) (h : extract p = some q)
    (input : Input) (i : Int) (s : State) :
    p.eval input i s = (do
      let x ← input (i + q.leftOffset)
      let y ← input (i + q.rightOffset)
      q.body.eval i x y s) := by
  unfold extract at h
  split at h
  next r₁ e₁ r₂ e₂ tail =>
    cases hl : offset e₁ with
    | none => simp [hl] at h
    | some l =>
      cases hr : offset e₂ with
      | none => simp [hl, hr] at h
      | some r =>
        cases hb : localBody tail with
        | none => simp [hl, hr, hb] at h
        | some b =>
          simp [hl, hr, hb] at h
          cases h
          have bodyEq := localBody_correct tail b hb input i
          simp [Cmd.eval, offset_correct _ _ hl, offset_correct _ _ hr,
            Imperative.Cmd.eval, Expr.eval, bodyEq, Option.bind_assoc]
  next => simp at h

theorem extracted_loop_correct (p : Cmd) (q : Extracted) (h : extract p = some q)
    (input : Input) (stride : Int) (n : Nat) (i : Int) (s : State) :
    iterate (fun j => p.eval input j) stride n i s =
      readLoop input (fun j x y => q.body.eval j x y) stride
        q.leftOffset q.rightOffset n i s := by
  induction n generalizing i s with
  | zero => rfl
  | succ n ih =>
      simp [iterate, readLoop, extract_correct _ _ h, ih, Option.bind_assoc]

end IRComparison.Source
