import IRComparison.Frontend.NativeLoop

namespace IRComparison.BodyBackends

def imperative (body : Imperative.Cmd) (start stride : Int) (count : Nat) (l r : Int) :=
  Imperative.transform (.loop start stride count l r body)

def functional (body : Functional.Term) (start stride : Int) (count : Nat) (l r : Int) :=
  Functional.transform (.loop start stride count l r body)

def runSource (f : Int → Int → Int → State → Option State) (start stride : Int)
    (count : Nat) (l r : Int) (input : Input) (s : State) : Option State :=
  NativeLoop.run (NativeLoop.readBody input f l r) start stride count s

theorem imperative_correct (body : Imperative.Cmd) (f : Int → Int → Int → State → Option State)
    (h : ∀ (i x y : Int) (s : State), body.eval i x y s = f i x y s)
    (start stride : Int) (count : Nat) (l r : Int) (input : Input) (s : State) :
    (imperative body start stride count l r).eval input s = runSource f start stride count l r input s :=
  NativeLoop.imperative_correct f body h input start stride count l r s

theorem functional_correct (body : Functional.Term) (f : Int → Int → Int → State → Option State)
    (h : ∀ (i x y : Int) (s : State), body.eval i x y [s] = f i x y s)
    (start stride : Int) (count : Nat) (l r : Int) (input : Input) (s : State) :
    (functional body start stride count l r).eval input s = runSource f start stride count l r input s :=
  NativeLoop.functional_correct f body h input start stride count l r s

end IRComparison.BodyBackends
