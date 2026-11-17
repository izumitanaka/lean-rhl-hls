import IRComparison.Examples.UnifiedPipelineExamples
import IRComparison.Examples.StreamWorkloads

namespace IRComparison.UnifiedWorkloads
open WindowWorkloads AutoPipelineExamples

structure Workload where
  name : String
  imperative : List UnifiedPipeline.Kernel
  functional : List UnifiedPipeline.Kernel

def tailI (start stride : Int) (count : Nat) : List UnifiedPipeline.Kernel :=
  let supply := fun _ : Unit => (List.range count).map (fun n => start + stride * Int.ofNat n)
  [StreamWorkloads.sink.imperativeKernel 64 1 start stride count supply,
   stage3.imperativeKernel 64 2 start stride count supply,stage4.imperativeKernel 64 3 start stride count supply]
def tailF (start stride : Int) (count : Nat) : List UnifiedPipeline.Kernel :=
  let supply := fun _ : Unit => (List.range count).map (fun n => start + stride * Int.ofNat n)
  [StreamWorkloads.sink.functionalKernel 64 1 start stride count supply,
   stage3.functionalKernel 64 2 start stride count supply,stage4.functionalKernel 64 3 start stride count supply]

def workloads : List Workload := [
  ⟨"filter",
    filterCode.imperativeKernel 64 0 0 (1) 62 (fun _ => order) :: tailI 0 (1) 62,
    filterCode.functionalKernel 64 0 0 (1) 62 (fun _ => order) :: tailF 0 (1) 62⟩,
  ⟨"filter_alt",
    filterAltCode.imperativeKernel 64 0 0 (1) 62 (fun _ => order) :: tailI 0 (1) 62,
    filterAltCode.functionalKernel 64 0 0 (1) 62 (fun _ => order) :: tailF 0 (1) 62⟩,
  ⟨"filter_rev",
    filterCode.imperativeKernel 64 0 61 (-1) 62 (fun _ => order) :: tailI 61 (-1) 62,
    filterCode.functionalKernel 64 0 61 (-1) 62 (fun _ => order) :: tailF 61 (-1) 62⟩,
  ⟨"filter_skip",
    filterSkipCode.imperativeKernel 64 0 0 (1) 30 (fun _ => order) :: tailI 0 (1) 30,
    filterSkipCode.functionalKernel 64 0 0 (1) 30 (fun _ => order) :: tailF 0 (1) 30⟩,
  ⟨"filter_dilated",
    filterDilatedCode.imperativeKernel 64 0 0 (1) 28 (fun _ => order) :: tailI 0 (1) 28,
    filterDilatedCode.functionalKernel 64 0 0 (1) 28 (fun _ => order) :: tailF 0 (1) 28⟩,
  ⟨"filter_dilated_alt",
    filterDilatedAltCode.imperativeKernel 64 0 0 (1) 28 (fun _ => order) :: tailI 0 (1) 28,
    filterDilatedAltCode.functionalKernel 64 0 0 (1) 28 (fun _ => order) :: tailF 0 (1) 28⟩,
  ⟨"filter_dilated_rev",
    filterDilatedRevCode.imperativeKernel 64 0 59 (-1) 60 (fun _ => order) :: tailI 59 (-1) 60,
    filterDilatedRevCode.functionalKernel 64 0 59 (-1) 60 (fun _ => order) :: tailF 59 (-1) 60⟩,
  ⟨"filter_dilated_skip",
    filterDilatedCode.imperativeKernel 64 0 0 (1) 28 (fun _ => order) :: tailI 0 (1) 28,
    filterDilatedCode.functionalKernel 64 0 0 (1) 28 (fun _ => order) :: tailF 0 (1) 28⟩ ]

def checkPlan (name : String) (kernels : List UnifiedPipeline.Kernel)
    (p : UnifiedPipeline.Plan [4] (fun _ => 64) kernels) : IO Unit := do
  unless UnifiedPipelineExamples.isCompact p do throw (IO.userError s!"{name}: compact path not selected")
  let expected := (CompactStage.source 0 0 (UnifiedPipeline.compactStages kernels) initial).map
    (fun s => (#[],#[],#[],s.arrays 4))
  let observe := fun s : State => (s.arrays 1,s.arrays 2,s.arrays 3,s.arrays 4)
  unless expected.isSome && (p.eval 0 0 initial).map observe == expected do
    throw (IO.userError s!"{name}: source/target mismatch")
  match UnifiedPipeline.run 0 0 40000 (UnifiedPipeline.start (UnifiedPipeline.lower p) initial) with
  | .stopped r => unless r.map observe == expected do throw (IO.userError s!"{name}: control mismatch")
  | _ => throw (IO.userError s!"{name}: control did not finish")

#eval show IO Unit from do
  for w in workloads do
    for ks in [w.imperative,w.functional] do
      checkPlan w.name ks (UnifiedPipeline.compile [4] (fun _ => 64) ks)
  IO.println "Unified entry: 8 kernels x 2 IRs x 4 compact stages; all intermediate arrays erased; source, target and control agree"

end IRComparison.UnifiedWorkloads
