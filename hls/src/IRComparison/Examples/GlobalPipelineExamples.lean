import IRComparison.Examples.UnifiedPipelineExamples

namespace IRComparison.GlobalPipelineExamples
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def produceA (i _x _y : Int) (s : State) : Option State := s.write 1 i (i*i)
def produceB (i _x _y : Int) (s : State) : Option State := s.write 5 i (i+10)
def marker (_i _x _y : Int) (s : State) : Option State := s.write 3 0 7
def readMarker (_i _x _y : Int) (s : State) : Option State := do
  let v ← (s.arrays 1)[0]?
  s.write 3 0 v

def consumeA (i _x _y : Int) (s : State) : Option State := do
  let v ← (s.arrays 1)[i.toNat]?
  s.write 2 i v

def consumeB (i _x _y : Int) (s : State) : Option State := do
  let v ← (s.arrays 5)[i.toNat]?
  s.write 6 i v

def readFuture (i _x _y : Int) (s : State) : Option State := do
  let v ← (s.arrays 2)[i.toNat]?
  s.write 1 i (v+1)
def finalConsumer (i _x _y : Int) (s : State) : Option State := do
  let v ← (s.arrays 2)[i.toNat]?
  s.write 6 i v
hls_window readFuture as earlyReader
hls_window finalConsumer as finalSink

hls_window produceA as producerA
hls_window produceB as producerB
hls_window marker as independent
hls_window readMarker as observing
hls_window consumeA as consumerA
hls_window consumeB as consumerB

def kernels (functional : Bool) : List UnifiedPipeline.Kernel :=
  if functional then [
    producerA.functionalKernel 4 0 0 1 3 (fun _ => []),
    producerB.functionalKernel 4 0 0 1 3 (fun _ => []),
    consumerA.functionalKernel 4 1 0 1 3 (fun _ => [0,1,2]),
    consumerB.functionalKernel 4 5 0 1 3 (fun _ => [0,1,2])]
  else [
    producerA.imperativeKernel 4 0 0 1 3 (fun _ => []),
    producerB.imperativeKernel 4 0 0 1 3 (fun _ => []),
    consumerA.imperativeKernel 4 1 0 1 3 (fun _ => [0,1,2]),
    consumerB.imperativeKernel 4 5 0 1 3 (fun _ => [0,1,2])]

def independentKernel (functional : Bool) :=
  if functional then independent.functionalKernel 4 0 0 1 1 (fun _ => [])
  else independent.imperativeKernel 4 0 0 1 1 (fun _ => [])
def observingKernel (functional : Bool) :=
  if functional then observing.functionalKernel 4 0 0 1 1 (fun _ => [])
  else observing.imperativeKernel 4 0 0 1 1 (fun _ => [])

def separated (functional : Bool) := [(kernels functional)[0]'(by cases functional <;> decide),independentKernel functional,(kernels functional)[2]'(by cases functional <;> decide)]
def readBetween (functional : Bool) := [(kernels functional)[0]'(by cases functional <;> decide),observingKernel functional,(kernels functional)[2]'(by cases functional <;> decide)]
def publicOutput (functional : Bool) := [(kernels functional)[0]'(by cases functional <;> decide),independentKernel functional,(kernels functional)[2]'(by cases functional <;> decide)]
def beforeProducer (functional : Bool) := if functional then [
  earlyReader.functionalKernel 4 0 0 1 3 (fun _ => []),
  consumerA.functionalKernel 4 1 0 1 3 (fun _ => [0,1,2]),
  finalSink.functionalKernel 4 2 0 1 3 (fun _ => [0,1,2])]
  else [earlyReader.imperativeKernel 4 0 0 1 3 (fun _ => []),
    consumerA.imperativeKernel 4 1 0 1 3 (fun _ => [0,1,2]),
    finalSink.imperativeKernel 4 2 0 1 3 (fun _ => [0,1,2])]

def initial : State := ⟨fun _ => 0,fun _ => Array.replicate 4 0⟩

def policy {outputs sizes ks} : UnifiedPipeline.Plan outputs sizes ks → List Nat
  | .expanded (.global p) => p.policy
  | .expanded p => p.channels.map Prod.snd
  | @UnifiedPipeline.Plan.compact _ _ rest _ second _ => second.compact.array :: rest.map (fun k => k.compact.array)

def interleavedI := UnifiedPipeline.compile [2,3,6] (fun _ => 4) (kernels false)
def interleavedF := UnifiedPipeline.compile [2,3,6] (fun _ => 4) (kernels true)
example : policy interleavedI = [1,5] ∧ policy interleavedF = [1,5] := by decide +kernel
example : policy (UnifiedPipeline.compile [2,3] (fun _ => 4) (separated false)) = [1] := by decide +kernel
example : policy (UnifiedPipeline.compile [2,3] (fun _ => 4) (readBetween false)) = [] := by decide +kernel
example : policy (UnifiedPipeline.compile [1,2,3] (fun _ => 4) (publicOutput false)) = [] := by decide +kernel

example : policy (UnifiedPipeline.compile [6] (fun _ => 4) (beforeProducer false)) = [1] := by decide +kernel

/-- Same source order and both simultaneously live channels; no reordering. -/
example : (interleavedI.eval 0 0 initial).map (fun s => (s.arrays 1,s.arrays 5,s.arrays 2,s.arrays 6)) =
    some (#[],#[],#[0,1,4,0],#[10,11,12,0]) := by decide +kernel
example : (interleavedF.eval 0 0 initial).map (fun s => (s.arrays 1,s.arrays 5,s.arrays 2,s.arrays 6)) =
    some (#[],#[],#[0,1,4,0],#[10,11,12,0]) := by decide +kernel

end IRComparison.GlobalPipelineExamples
