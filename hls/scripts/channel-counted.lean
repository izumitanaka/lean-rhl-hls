import IRComparison.Circuit.CountedBackend

open IRComparison HybridIR Circuit
set_option maxHeartbeats 8000000

def initialChannelState : ChannelState :=
  ⟨⟨fun _ => 0,fun _ => #[10,11,12,13,14,15,16,17]⟩,
    fun q => if q = 0 then [2,4,6,8,10,12] else if q = 1 then [100] else [71,72],
    fun _ => none⟩

def check (name : String) (first next : List Circuit.Load) (body : Cmd)
    (start stride : Int) (count : Nat) : IO Unit := do
  let s := initialChannelState
  let c := ChannelCounted.command 0 0 1 start stride count first next body
  let actual := c.eval 0 0 0 s []
  let expected := (HybridIR.blocksEval (arrayInput (s.data.arrays 0)) 0 0
    (referenceBlocks start stride count first next body) [] s.data (s.queues 0) (s.queues 1)).map
      (fun (t,rest,out) => (t,GlobalPipeline.put (GlobalPipeline.put s.queues 0 rest) 1 out))
  let observe := fun (p : State × (Nat → List Int)) =>
    (p.1.arrays 1,(List.range 3).map p.1.regs,(List.range 4).map p.2)
  unless actual.map (fun t => observe (t.data,t.queues)) == expected.map observe do
    throw (IO.userError s!"{name}: reference mismatch")
  let bounded := ChannelLower.bounded (fun q => if q = 1 then count+1 else 0) 0 0 0 c s []
  unless bounded.map (fun t => observe (t.data,t.queues)) == actual.map (fun t => observe (t.data,t.queues)) do
    throw (IO.userError s!"{name}: bounded mismatch")
  IO.println s!"PASS {name}: named counted body, failure and unrelated queues"

def main : IO Unit := do
  let output : Cmd := .seq (.store 1 (.pure .index) (.pure (.local 0))) (.send (.pure (.local 0)))
  check "memory" [.memory ⟨1,0⟩] [.memory ⟨1,0⟩] output 0 1 3
  check "reverse" [.memory ⟨1,0⟩] [.memory ⟨1,0⟩] output 4 (-1) 3
  check "different-widths" [.memory ⟨1,0⟩] [.saved 0,.memory ⟨1,0⟩] output 0 1 3
  check "FIFO" [.take ⟨0,0⟩] [.take ⟨0,1⟩] output 0 1 3
  check "missing-local" [.memory ⟨1,0⟩] [.memory ⟨1,0⟩] (.send (.pure (.local 1))) 0 1 3
  check "empty" [.memory ⟨1,0⟩] [.saved 99] output 99 1 0
