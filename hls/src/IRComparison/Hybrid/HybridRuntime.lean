import IRComparison.Hybrid.HybridCommands
import IRComparison.Memory.GlobalPipeline
namespace IRComparison.HybridIR
/-- Window loads are explicit effects: saved buffer value, memory load, or
    destructive discard/receive. Only their returned values enter the body. -/
structure Block where
  index : Int
  loads : List WindowFIFO.Load
  body : Cmd
  deriving Repr

def blocksEval (input : Input) (x y : Int) : List Block → List Int → State → List Int → List Int → Option (State × List Int × List Int)
  | [],_,s,qi,qo => some (s,qi,qo)
  | b::bs,old,s,qi,qo => do
      let (vs,rest) ← WindowFIFO.execute input old b.loads qi
      let (t,out) ← b.body.eval b.index x y s qo vs
      blocksEval input x y bs vs t rest out

/-- Channels are machine resources, never reusable scalar values. -/
structure Instruction where
  input : Nat
  mode : GlobalPipeline.InputMode
  output : Option Nat
  blocks : List Block
  deriving Repr

def Instruction.eval (c : Instruction) (x y : Int) (s : State) (qs : GlobalPipeline.Queues) :
    Option (State × GlobalPipeline.Queues) := do
  let q ← c.mode.eval s qs
  let initial := match c.output with | none => s | some a => StreamConsumer.erase a s
  let (t,_,qo) ← blocksEval (arrayInput (s.arrays c.input)) x y c.blocks [] initial q []
  match c.output with
  | none => return (t,GlobalPipeline.put qs c.input [])
  | some a => return (StreamConsumer.erase a t,GlobalPipeline.put (GlobalPipeline.put qs c.input []) a qo)

def execute (x y : Int) : List Instruction → State → GlobalPipeline.Queues → Option State
  | [],s,_ => some s
  | c::cs,s,qs => do
      let (t,rest) ← c.eval x y s qs
      execute x y cs t rest


end IRComparison.HybridIR
