import IRComparison.Frontend.NativeLoop

namespace IRComparison.NativeBody

abbrev Value := Int → Int → Int → State → Option Int

/-- An output of a future proved expression frontend, indexed by the actual
    native computation, not just by an independently interpreted source AST. -/
structure ValueCode (native : Value) where
  expr : Expr
  correct : ∀ i x y s, expr.eval i x y s = native i x y s

def literal (n : Int) : ValueCode (fun _ _ _ _ => some n) := ⟨.lit n, by intros; rfl⟩
def index : ValueCode (fun i _ _ _ => some i) := ⟨.index, by intros; rfl⟩
def left : ValueCode (fun _ x _ _ => some x) := ⟨.left, by intros; rfl⟩
def right : ValueCode (fun _ _ y _ => some y) := ⟨.right, by intros; rfl⟩
def register (r : Nat) : ValueCode (fun _ _ _ s => some (s.regs r)) :=
  ⟨.reg r, by intros; rfl⟩

def add (a : ValueCode f) (b : ValueCode g) :
    ValueCode (fun i x y s => do return (← f i x y s) + (← g i x y s)) :=
  ⟨.add a.expr b.expr, by intros; simp [Expr.eval, a.correct, b.correct]⟩

def sub (a : ValueCode f) (b : ValueCode g) :
    ValueCode (fun i x y s => do return (← f i x y s) - (← g i x y s)) :=
  ⟨.sub a.expr b.expr, by intros; simp [Expr.eval, a.correct, b.correct]⟩

def mul (a : ValueCode f) (b : ValueCode g) :
    ValueCode (fun i x y s => do return (← f i x y s) * (← g i x y s)) :=
  ⟨.mul a.expr b.expr, by intros; simp [Expr.eval, a.correct, b.correct]⟩

def divide (a : ValueCode f) (b : ValueCode g) :
    ValueCode (fun i x y s => do return (← f i x y s) / (← g i x y s)) :=
  ⟨.div a.expr b.expr, by intros; simp [Expr.eval, a.correct, b.correct]⟩

def read (array : Nat) (address : ValueCode f) :
    ValueCode (fun i x y s => do
      let j ← f i x y s
      if j < 0 then none else (s.arrays array)[j.toNat]?) :=
  ⟨.read array address.expr, by intros; simp [Expr.eval, address.correct]⟩

/-- Two independent target bodies indexed by the same native Lean function.
    This is a frontend result specification, not an automatic parser. -/
structure Code (native : Step State) where
  imperative : Imperative.Cmd
  functional : Functional.Term
  imperative_correct : ∀ i x y s, imperative.eval i x y s = native i x y s
  functional_correct : ∀ i x y s, functional.eval i x y [s] = native i x y s

def skip : Code (fun _ _ _ s => some s) where
  imperative := .skip
  functional := .yield 0
  imperative_correct := by intros; rfl
  functional_correct := by intros; rfl

def assign (reg : Nat) (value : ValueCode f) :
    Code (fun i x y s => do return s.set reg (← f i x y s)) where
  imperative := .assign reg value.expr
  functional := .letSet 0 reg value.expr (.yield 0)
  imperative_correct := by intros; simp [Imperative.Cmd.eval, value.correct]
  functional_correct := by intros; simp [Functional.Term.eval, value.correct]

def store (array : Nat) (address : ValueCode f) (value : ValueCode g) :
    Code (fun i x y s => do s.write array (← f i x y s) (← g i x y s)) where
  imperative := .store array address.expr value.expr
  functional := .letWrite 0 array address.expr value.expr (.yield 0)
  imperative_correct := by intros; simp [Imperative.Cmd.eval, address.correct, value.correct]
  functional_correct := by intros; simp [Functional.Term.eval, address.correct, value.correct]

def seq (first : Code f) (second : Code g) :
    Code (fun i x y s => do g i x y (← f i x y s)) where
  imperative := .seq first.imperative second.imperative
  functional := .letResult 0 first.functional (.letResult 0 second.functional (.yield 0))
  imperative_correct := by intros; simp [Imperative.Cmd.eval, first.imperative_correct, second.imperative_correct]
  functional_correct := by
    intros
    simp [Functional.Term.eval, first.functional_correct, second.functional_correct]

def branch (test : ValueCode condition) (yes : Code f) (no : Code g) :
    Code (fun i x y s => do
      if (← condition i x y s) != 0 then f i x y s else g i x y s) where
  imperative := .branch test.expr yes.imperative no.imperative
  functional := .branch 0 test.expr yes.functional no.functional
  imperative_correct := by
    intros; simp [Imperative.Cmd.eval, test.correct, yes.imperative_correct, no.imperative_correct]
  functional_correct := by
    intros; simp [Functional.Term.eval, test.correct, yes.functional_correct, no.functional_correct]

def compileImperative (body : Code native) (start stride : Int) (count : Nat) (l r : Int) :
    Imperative.Program := Imperative.transform (.loop start stride count l r body.imperative)

def compileFunctional (body : Code native) (start stride : Int) (count : Nat) (l r : Int) :
    Functional.Program := Functional.transform (.loop start stride count l r body.functional)

theorem compileImperative_correct (body : Code native) (input : Input)
    (start stride : Int) (count : Nat) (l r : Int) (s : State) :
    (compileImperative body start stride count l r).eval input s =
      NativeLoop.run (NativeLoop.readBody input native l r) start stride count s :=
  NativeLoop.imperative_correct native body.imperative body.imperative_correct
    input start stride count l r s

theorem compileFunctional_correct (body : Code native) (input : Input)
    (start stride : Int) (count : Nat) (l r : Int) (s : State) :
    (compileFunctional body start stride count l r).eval input s =
      NativeLoop.run (NativeLoop.readBody input native l r) start stride count s :=
  NativeLoop.functional_correct native body.functional body.functional_correct
    input start stride count l r s

end IRComparison.NativeBody
