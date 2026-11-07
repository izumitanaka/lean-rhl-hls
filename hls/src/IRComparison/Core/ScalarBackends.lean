import IRComparison.Frontend.NativeBody

namespace IRComparison.ScalarBackends

/-- The two backends consume exactly the expression emitted by the frontend. -/
def value (e : Expr) : NativeBody.ValueCode (fun i x y s => e.eval i x y s) :=
  ⟨e, by intros; rfl⟩

def body (e : Expr) (reg : Nat) := NativeBody.assign reg (value e)

def imperative (e : Expr) (reg : Nat) (start stride : Int) (count : Nat) (l r : Int) :=
  NativeBody.compileImperative (body e reg) start stride count l r

def functional (e : Expr) (reg : Nat) (start stride : Int) (count : Nat) (l r : Int) :=
  NativeBody.compileFunctional (body e reg) start stride count l r

/-- The ordinary Lean loop to which both optimized programs are compared. -/
def runSource (f : Int → Int → Int → Int) (reg : Nat) (start stride : Int)
    (count : Nat) (l r : Int) (input : Input) (s : State) : Option State :=
  NativeLoop.run (NativeLoop.readBody input (fun i x y s => some (s.set reg (f i x y))) l r)
    start stride count s

/-- Fixed theorem, proved once, including the backend's buffer transformation.
    Its premise is constructed by the ordinary-Lean frontend. -/
theorem imperative_correct (e : Expr) (f : Int → Int → Int → Int)
    (h : ∀ (s : State) (i x y : Int), e.eval i x y s = some (f i x y))
    (reg : Nat) (start stride : Int) (count : Nat) (l r : Int) (input : Input) (s : State) :
    (imperative e reg start stride count l r).eval input s =
      runSource f reg start stride count l r input s := by
  unfold runSource
  apply NativeLoop.imperative_correct
  intro i x y s
  simp [body, value, NativeBody.assign, Imperative.Cmd.eval, h]

theorem functional_correct (e : Expr) (f : Int → Int → Int → Int)
    (h : ∀ (s : State) (i x y : Int), e.eval i x y s = some (f i x y))
    (reg : Nat) (start stride : Int) (count : Nat) (l r : Int) (input : Input) (s : State) :
    (functional e reg start stride count l r).eval input s =
      runSource f reg start stride count l r input s := by
  unfold runSource
  apply NativeLoop.functional_correct
  intro i x y s
  simp [body, value, NativeBody.assign, Functional.Term.eval, h]

end IRComparison.ScalarBackends
