import IRComparison.Circuit.Structured
import IRComparison.Memory.StreamConsumer

namespace IRComparison.Circuit

def Payload.clear (p : Payload) (q : Nat) : Payload :=
  { p with queues := fun n => if n = q then [] else p.queues n }

def Payload.erase (p : Payload) (a : Nat) : Payload :=
  { p with data := StreamConsumer.erase a p.data }

def Payload.snapshot (p : Payload) (a source : Nat) : Payload :=
  { p with data := { p.data with arrays := fun n => if n = a then p.data.arrays source else p.data.arrays n } }

theorem clear_eval (p : Payload) (q : Nat) : (Schedule.step (.clear q)).Eval cap p (some (p.clear q)) := .step

theorem erase_eval (p : Payload) (a : Nat) : (Schedule.step (.erase a)).Eval cap p (some (p.erase a)) := .step

theorem snapshot_eval (p : Payload) (a source : Nat) :
    (Schedule.step (.snapshot a source)).Eval cap p (some (p.snapshot a source)) := .step

end IRComparison.Circuit
