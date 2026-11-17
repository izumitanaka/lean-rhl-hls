import IRComparison.Examples.CompactChainExamples
import IRComparison.Examples.AlternativePipelineExamples

namespace IRComparison.UnifiedPipelineExamples
open NativeWindowExamples WindowPipelineExamples AutoPipelineExamples
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def kernelsI := [taps.imperativeKernel 13 0 0 1 3 (fun _ => ascending),
  downstream.imperativeKernel 13 1 0 1 2 (fun _ => [0,1,2]),
  stage3.imperativeKernel 13 2 0 1 2 (fun _ => [0,1]),
  stage4.imperativeKernel 13 3 0 1 2 (fun _ => [0,1])]
def kernelsF := [taps.functionalKernel 13 0 0 1 3 (fun _ => ascending),
  downstream.functionalKernel 13 1 0 1 2 (fun _ => [0,1,2]),
  stage3.functionalKernel 13 2 0 1 2 (fun _ => [0,1]),
  stage4.functionalKernel 13 3 0 1 2 (fun _ => [0,1])]
def planI := UnifiedPipeline.compile [4] sizes kernelsI
def planF := UnifiedPipeline.compile [4] sizes kernelsF

def isCompact {outputs : List Nat} {allocation : Nat → Nat} {ks : List UnifiedPipeline.Kernel} : UnifiedPipeline.Plan outputs allocation ks → Bool
  | .compact _ => true
  | .expanded _ => false
example : isCompact planI = true ∧ isCompact planF = true := by decide +kernel
example : (planI.eval 0 0 initial).map (fun s => (s.arrays 1,s.arrays 2,s.arrays 3,s.arrays 4)) =
    some (#[],#[],#[],#[62,74,0,0,0,0,0,0,0,0,0,0,0]) := by decide +kernel

def branchKernels := [AlternativeExamples.native.imperativeKernel 4 0 0 1 1 (fun _ => []),
  AlternativePipelineExamples.sink.imperativeKernel 4 1 0 1 1 (fun _ => [0,3])]
def branchPlan := UnifiedPipeline.compile [2] (fun _ => 4) branchKernels
example : isCompact branchPlan = false := by decide +kernel
example : (branchPlan.eval 10 0 AlternativeExamples.initial).map (fun s => (s.arrays 1,s.arrays 2)) =
    some (#[],#[23,0,0,0]) := by decide +kernel

def largeSupply (_ : Unit) : List Int := (List.range 1000000004).map Int.ofNat
def billionKernels := [taps.imperativeKernel 1000000004 0 0 1 1000000000 largeSupply,
  downstream.imperativeKernel 1000000004 1 0 1 999999999 largeSupply,
  stage3.imperativeKernel 1000000004 2 0 1 999999999 largeSupply,
  stage4.imperativeKernel 1000000004 3 0 1 999999999 largeSupply]
def billion := UnifiedPipeline.compile [4] (fun _ => 1000000004) billionKernels
-- The supply thunk is never evaluated on the compact path.
example : isCompact billion = true := by decide +kernel

theorem both_correct (s : State) (layout : PipelineShapes.Layout sizes s) (x y : Int) :
    (planI.eval x y s).map (PipelineUse.observe [4]) = (planF.eval x y s).map (PipelineUse.observe [4]) := by
  rw [planI.correct s layout (by trivial),planF.correct s layout (by trivial)]
  rfl

def observeControl : UnifiedPipeline.Config → Option (Option (Array Int))
  | .stopped r => some (r.map (fun s => s.arrays 4))
  | _ => none
example : observeControl (UnifiedPipeline.run 0 0 5000 (UnifiedPipeline.start (UnifiedPipeline.lower planI) initial)) =
    some (some #[62,74,0,0,0,0,0,0,0,0,0,0,0]) := by decide +kernel
example : observeControl (UnifiedPipeline.run 0 0 5000 (UnifiedPipeline.start (UnifiedPipeline.lower planF) initial)) =
    some (some #[62,74,0,0,0,0,0,0,0,0,0,0,0]) := by decide +kernel

end IRComparison.UnifiedPipelineExamples
