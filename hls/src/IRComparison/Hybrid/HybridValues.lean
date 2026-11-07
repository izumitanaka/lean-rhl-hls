import IRComparison.Core.Common

namespace IRComparison.HybridIR

/-- Pure values cannot access registers, arrays, buffers, or channels.
    Locals are lexical bindings; temporaries belong to the read computation. -/
inductive Value where
  | lit (n : Int)
  | index | left | right
  | local (slot : Nat)
  | temp (slot : Nat)
  | natIndex (v : Value)
  | add (a b : Value)
  | sub (a b : Value)
  | mul (a b : Value)
  | div (a b : Value)
  deriving Repr, DecidableEq

def Value.eval (i x y : Int) (locals temps : List Int) : Value → Option Int
  | .lit n => some n
  | .index => some i
  | .left => some x
  | .right => some y
  | .local n => locals[n]?
  | .temp n => temps[n]?
  | .natIndex v => do return Int.ofNat (← v.eval i x y locals temps).toNat
  | .add a b => do return (← a.eval i x y locals temps) + (← b.eval i x y locals temps)
  | .sub a b => do return (← a.eval i x y locals temps) - (← b.eval i x y locals temps)
  | .mul a b => do return (← a.eval i x y locals temps) * (← b.eval i x y locals temps)
  | .div a b => do return (← a.eval i x y locals temps) / (← b.eval i x y locals temps)

/-- Reads are explicit ordered operations. Branches retain conditional reads;
    extracting a read never evaluates an unchosen branch. -/
inductive ReadCode where
  | pure (value : Value)
  | register (reg : Nat)
  | memory (array : Nat) (address : Value)
  | bind (first next : ReadCode)
  | branch (condition : Value) (yes no : ReadCode)
  deriving Repr, DecidableEq

def ReadCode.eval (i x y : Int) (s : State) (locals temps : List Int) : ReadCode → Option Int
  | .pure v => v.eval i x y locals temps
  | .register r => some (s.regs r)
  | .memory a j => do
      let k ← j.eval i x y locals temps
      if k < 0 then none else (s.arrays a)[k.toNat]?
  | .bind first next => do
      let v ← first.eval i x y s locals temps
      next.eval i x y s locals (v::temps)
  | .branch c yes no => do
      if (← c.eval i x y locals temps) != 0 then yes.eval i x y s locals temps
      else no.eval i x y s locals temps

def extract : Expr → ReadCode
  | .lit n => .pure (.lit n)
  | .index => .pure .index
  | .left => .pure .left
  | .right => .pure .right
  | .local n => .pure (.local n)
  | .reg r => .register r
  | .natIndex e => .bind (extract e) (.pure (.natIndex (.temp 0)))
  | .read a e => .bind (extract e) (.memory a (.temp 0))
  | .add a b => .bind (extract a) (.bind (extract b) (.pure (.add (.temp 1) (.temp 0))))
  | .sub a b => .bind (extract a) (.bind (extract b) (.pure (.sub (.temp 1) (.temp 0))))
  | .mul a b => .bind (extract a) (.bind (extract b) (.pure (.mul (.temp 1) (.temp 0))))
  | .div a b => .bind (extract a) (.bind (extract b) (.pure (.div (.temp 1) (.temp 0))))
  | .select c a b => .bind (extract c) (.branch (.temp 0) (extract a) (extract b))

theorem extract_correct (e : Expr) (i x y : Int) (s : State) (locals temps : List Int) :
    (extract e).eval i x y s locals temps = e.eval i x y s locals := by
  induction e generalizing temps with
  | lit | index | left | right | «local» | reg => rfl
  | natIndex e ih | read a e ih =>
    simp only [extract,ReadCode.eval,ih,Expr.eval]
    cases e.eval i x y s locals <;> simp [Value.eval]
  | add a b ha hb | sub a b ha hb | mul a b ha hb | div a b ha hb =>
    simp only [extract,ReadCode.eval,ha,hb,Expr.eval]
    cases a.eval i x y s locals <;> cases b.eval i x y s locals <;> simp [Value.eval]
  | select c a b hc ha hb =>
    simp only [extract,ReadCode.eval,hc,ha,hb,Expr.eval]
    cases c.eval i x y s locals <;> simp [Value.eval]

end IRComparison.HybridIR
