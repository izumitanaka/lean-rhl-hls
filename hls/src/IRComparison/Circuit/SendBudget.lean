import IRComparison.Hybrid.HybridRuntime

namespace IRComparison.Circuit

/-- Upper bound on sends per invocation. Data-dependent loops with no sends
have bound zero, regardless of their iteration count. Unknown means that this
simple analysis provides no finite bound; it never means a zero bound. -/
def sendBound : HybridIR.Cmd → Option Nat
  | .skip | .assign .. | .store .. => some 0
  | .send _ => some 1
  | .letValue _ b => sendBound b
  | .seq a b => do return (← sendBound a)+(← sendBound b)
  | .branch _ a b => do return max (← sendBound a) (← sendBound b)
  | .repeat n b => (sendBound b).map (n * ·)
  | .forRange _ b => if sendBound b = some 0 then some 0 else none

def blocksBudget : List HybridIR.Block → Option Nat
  | [] => some 0
  | b::bs => do return (← sendBound b.body)+(← blocksBudget bs)

def outputBudget (code : List HybridIR.Instruction) (array : Nat) : Nat :=
  code.foldl (fun n c => if c.output = some array then max n ((blocksBudget c.blocks).getD 0) else n) 0

end IRComparison.Circuit
