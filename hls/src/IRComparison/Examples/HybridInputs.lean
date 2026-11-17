import IRComparison.Frontend.LeanHybridCommand
import IRComparison.Examples.GlobalPipelineExamples
import IRComparison.Examples.UnifiedWorkloads

namespace IRComparison.HybridInputs
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

namespace GlobalPipelineExamples
hls_hybrid IRComparison.GlobalPipelineExamples.readFuture as earlyReader
hls_hybrid IRComparison.GlobalPipelineExamples.finalConsumer as finalSink
hls_hybrid IRComparison.GlobalPipelineExamples.produceA as producerA
hls_hybrid IRComparison.GlobalPipelineExamples.produceB as producerB
hls_hybrid IRComparison.GlobalPipelineExamples.marker as independent
hls_hybrid IRComparison.GlobalPipelineExamples.readMarker as observing
hls_hybrid IRComparison.GlobalPipelineExamples.consumeA as consumerA
hls_hybrid IRComparison.GlobalPipelineExamples.consumeB as consumerB
end GlobalPipelineExamples

namespace WindowWorkloads
hls_hybrid IRComparison.WindowWorkloads.filter as filterCode
hls_hybrid IRComparison.WindowWorkloads.filterAlt as filterAltCode
hls_hybrid IRComparison.WindowWorkloads.filterSkip as filterSkipCode
hls_hybrid IRComparison.WindowWorkloads.filterDilated as filterDilatedCode
hls_hybrid IRComparison.WindowWorkloads.filterDilatedAlt as filterDilatedAltCode
hls_hybrid IRComparison.WindowWorkloads.filterDilatedRev as filterDilatedRevCode
end WindowWorkloads

namespace StreamWorkloads
hls_hybrid IRComparison.StreamWorkloads.consume as sink
end StreamWorkloads

namespace AutoPipelineExamples
hls_hybrid IRComparison.AutoPipelineExamples.third as stage3
hls_hybrid IRComparison.AutoPipelineExamples.fourth as stage4
hls_hybrid IRComparison.AutoPipelineExamples.marker as markerCode
hls_hybrid IRComparison.AutoPipelineExamples.anotherReader as shared
hls_hybrid IRComparison.AutoPipelineExamples.readsBoth as both
end AutoPipelineExamples

namespace AlternativeExamples
hls_hybrid IRComparison.AlternativeExamples.producer as native
end AlternativeExamples

namespace AlternativePipelineExamples
hls_hybrid IRComparison.AlternativePipelineExamples.consume as sink
end AlternativePipelineExamples

namespace GlobalPipelineExamples
def kernels (functional : Bool) : List HybridIR.Kernel :=
  if functional then [
    producerA.hybridKernel 4 0 0 1 3 (fun _ => []),
    producerB.hybridKernel 4 0 0 1 3 (fun _ => []),
    consumerA.hybridKernel 4 1 0 1 3 (fun _ => [0,1,2]),
    consumerB.hybridKernel 4 5 0 1 3 (fun _ => [0,1,2])]
  else [
    producerA.hybridKernel 4 0 0 1 3 (fun _ => []),
    producerB.hybridKernel 4 0 0 1 3 (fun _ => []),
    consumerA.hybridKernel 4 1 0 1 3 (fun _ => [0,1,2]),
    consumerB.hybridKernel 4 5 0 1 3 (fun _ => [0,1,2])]

def independentKernel (functional : Bool) :=
  if functional then independent.hybridKernel 4 0 0 1 1 (fun _ => [])
  else independent.hybridKernel 4 0 0 1 1 (fun _ => [])
def observingKernel (functional : Bool) :=
  if functional then observing.hybridKernel 4 0 0 1 1 (fun _ => [])
  else observing.hybridKernel 4 0 0 1 1 (fun _ => [])

def separated (functional : Bool) := [(kernels functional)[0]'(by cases functional <;> decide),independentKernel functional,(kernels functional)[2]'(by cases functional <;> decide)]
def readBetween (functional : Bool) := [(kernels functional)[0]'(by cases functional <;> decide),observingKernel functional,(kernels functional)[2]'(by cases functional <;> decide)]
def publicOutput (functional : Bool) := [(kernels functional)[0]'(by cases functional <;> decide),independentKernel functional,(kernels functional)[2]'(by cases functional <;> decide)]
def beforeProducer (functional : Bool) := if functional then [
  earlyReader.hybridKernel 4 0 0 1 3 (fun _ => []),
  consumerA.hybridKernel 4 1 0 1 3 (fun _ => [0,1,2]),
  finalSink.hybridKernel 4 2 0 1 3 (fun _ => [0,1,2])]
  else [earlyReader.hybridKernel 4 0 0 1 3 (fun _ => []),
    consumerA.hybridKernel 4 1 0 1 3 (fun _ => [0,1,2]),
    finalSink.hybridKernel 4 2 0 1 3 (fun _ => [0,1,2])]

end GlobalPipelineExamples

namespace UnifiedWorkloads
open WindowWorkloads AutoPipelineExamples
open IRComparison.WindowWorkloads (order)
structure Workload where
  name : String
  imperative : List HybridIR.Kernel
  functional : List HybridIR.Kernel

def tailI (start stride : Int) (count : Nat) : List HybridIR.Kernel :=
  let supply := fun _ : Unit => (List.range count).map (fun n => start + stride * Int.ofNat n)
  [StreamWorkloads.sink.hybridKernel 64 1 start stride count supply,
   stage3.hybridKernel 64 2 start stride count supply,stage4.hybridKernel 64 3 start stride count supply]
def tailF (start stride : Int) (count : Nat) : List HybridIR.Kernel :=
  let supply := fun _ : Unit => (List.range count).map (fun n => start + stride * Int.ofNat n)
  [StreamWorkloads.sink.hybridKernel 64 1 start stride count supply,
   stage3.hybridKernel 64 2 start stride count supply,stage4.hybridKernel 64 3 start stride count supply]

def workloads : List Workload := [
  ⟨"filter",
    filterCode.hybridKernel 64 0 0 (1) 62 (fun _ => order) :: tailI 0 (1) 62,
    filterCode.hybridKernel 64 0 0 (1) 62 (fun _ => order) :: tailF 0 (1) 62⟩,
  ⟨"filter_alt",
    filterAltCode.hybridKernel 64 0 0 (1) 62 (fun _ => order) :: tailI 0 (1) 62,
    filterAltCode.hybridKernel 64 0 0 (1) 62 (fun _ => order) :: tailF 0 (1) 62⟩,
  ⟨"filter_rev",
    filterCode.hybridKernel 64 0 61 (-1) 62 (fun _ => order) :: tailI 61 (-1) 62,
    filterCode.hybridKernel 64 0 61 (-1) 62 (fun _ => order) :: tailF 61 (-1) 62⟩,
  ⟨"filter_skip",
    filterSkipCode.hybridKernel 64 0 0 (1) 30 (fun _ => order) :: tailI 0 (1) 30,
    filterSkipCode.hybridKernel 64 0 0 (1) 30 (fun _ => order) :: tailF 0 (1) 30⟩,
  ⟨"filter_dilated",
    filterDilatedCode.hybridKernel 64 0 0 (1) 28 (fun _ => order) :: tailI 0 (1) 28,
    filterDilatedCode.hybridKernel 64 0 0 (1) 28 (fun _ => order) :: tailF 0 (1) 28⟩,
  ⟨"filter_dilated_alt",
    filterDilatedAltCode.hybridKernel 64 0 0 (1) 28 (fun _ => order) :: tailI 0 (1) 28,
    filterDilatedAltCode.hybridKernel 64 0 0 (1) 28 (fun _ => order) :: tailF 0 (1) 28⟩,
  ⟨"filter_dilated_rev",
    filterDilatedRevCode.hybridKernel 64 0 59 (-1) 60 (fun _ => order) :: tailI 59 (-1) 60,
    filterDilatedRevCode.hybridKernel 64 0 59 (-1) 60 (fun _ => order) :: tailF 59 (-1) 60⟩,
  ⟨"filter_dilated_skip",
    filterDilatedCode.hybridKernel 64 0 0 (1) 28 (fun _ => order) :: tailI 0 (1) 28,
    filterDilatedCode.hybridKernel 64 0 0 (1) 28 (fun _ => order) :: tailF 0 (1) 28⟩ ]

end UnifiedWorkloads
end IRComparison.HybridInputs
