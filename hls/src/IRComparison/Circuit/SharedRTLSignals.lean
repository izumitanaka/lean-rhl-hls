import IRComparison.Circuit.SharedRTL

namespace IRComparison.Circuit.Shared.LocalRTL

/-- Concrete combinational payloads remain total even when their associated
validity bit is false. No zero-on-failure assumption is imposed on hardware. -/
def fullRuntime (r : Runtime) (signals : Array Int) : Runtime :=
  {r with wires := fun n => signals[n]?.getD 0}

def Code.value (c : Code) (r : Runtime) (signals : Array Int) : Int :=
  match c with
  | .source e => e.value.eval r
  | .localNode e => e.value.eval (fullRuntime r signals)

def Code.valid (c : Code) (r : Runtime) (signals : Array Int) : Bool :=
  match c with
  | .source e => e.valid.eval r
  | .localNode e => e.valid.eval (fullRuntime r signals)

def fullValues (r : Runtime) : List Code → Array Int
  | [] => #[]
  | c::cs =>
    let values := fullValues r cs
    (values.push (c.value r values)).push (if c.valid r values then 1 else 0)

def Program.fullEval (p : Program) (r : Runtime) : Option Int :=
  let signals := fullValues r p.code
  if signals[2*p.result+1]?.getD 0 != 0 then some (signals[2*p.result]?.getD 0) else none

end IRComparison.Circuit.Shared.LocalRTL
