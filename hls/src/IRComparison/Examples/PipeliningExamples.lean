import IRComparison.Circuit.Pipelining.Word
import IRComparison.Frontend.LeanWordCommand

namespace IRComparison.PipeliningExamples
open Circuit Circuit.Pipelining

/-- Ordinary Lean input; the existing frontend is reused unchanged. -/
def filterPair (i _x _y : HybridWord.Word) (s : HybridWord.State) : Option HybridWord.State := do
  let a ← (s.arrays 0)[i.toNat]?
  let b ← (s.arrays 0)[(i+1).toNat]?
  s.write 1 i ((a+b)/2)

hls_word filterPair as filterCode

def gather (i _x _y : HybridWord.Word) (s : HybridWord.State) : Option HybridWord.State := do
  let j ← (s.arrays 0)[i.toNat]?
  let v ← (s.arrays 1)[j.toNat]?
  s.write 2 i (v+1)

hls_word gather as gatherCode

def filterKernel (n : Nat) (start : Int := 0) (stride : Int := 1) : HybridWord.Kernel :=
  filterCode.kernel (n+1) 0 start stride n (fun _ => [])

def filterPipeline (n ii : Nat) (start : Int := 0) (stride : Int := 1) :=
  pipelineWord (filterKernel n start stride) {} ii

/-- One general theorem covers every trip count, II, initial array value,
reverse stride, overflow and failure; these are not example-specific proofs. -/
theorem filter_pipeline_correct (n ii : Nat) (start stride : Int) (s : HybridWord.State) :
    ∃ result, (filterPipeline n ii start stride).1.Eval cap (wordPayload s 0 0) result ∧
      result.map Payload.data = ((filterKernel n start stride).source 0 0 s).map HybridWord.State.encode :=
  pipelineWord_correct _ {} (by decide) ii s 0 0

def initial (input : Array HybridWord.Word) (n : Nat) : HybridWord.State :=
  ⟨fun _ => 0, fun a => if a = 0 then input else if a = 1 then Array.replicate n 0 else #[]⟩

def transformedRun (t : Transformed) (cap : Nat → Nat) (p : Payload) : Option (Option Payload) :=
  match t with
  | .original _ => none -- a structured fallback is not an evaluation failure
  | .scheduled code plan => some (runCycles cap code plan.cycles p)

def wave (count depth : Nat) : Loop :=
  ⟨count,depth,fun i k => .wire (i*depth+k)
    (if k = 0 then .lit (Int.ofNat i) else .bin .add (.wire (i*depth+k-1)) (.lit 1))⟩

def recurrence (count : Nat) : Loop :=
  ⟨count,3,fun i k => match k with
    | 0 => .wire (2*i) (.reg 0)
    | 1 => .wire (2*i+1) (.bin .add (.wire (2*i)) (.lit 1))
    | _ => .assign 0 (.wire (2*i+1))⟩

def fifoLoop (count : Nat) : Loop :=
  ⟨count,3,fun i k => match k with
    | 0 => .receive 0 (2*i)
    | 1 => .wire (2*i+1) (.bin .add (.wire (2*i)) (.lit 1))
    | _ => .send 1 (.wire (2*i+1))⟩

def emptyPayload : Payload := ⟨⟨fun _ => 0,fun _ => #[]⟩,fun _ => 0,fun _ => []⟩

example : ((wave 4 3).pipeline 1).accepted = true := by decide
example : ((wave 4 3).pipeline 1).cycles = [[0],[1,3],[2,4,6],[5,7,9],[8,10],[11]] := by decide
example : ((recurrence 4).pipeline 1).accepted = false := by decide
example : ((recurrence 4).pipeline 3).accepted = true := by decide
example : ((fifoLoop 4).pipeline 1).accepted = true := by decide

-- Certificate checks are executable examples; compiler correctness above is
-- universal and uses neither native_decide nor these examples as a premise.
example : valid (wave 1 2).code [[0,1]] = false := by decide
example : valid (wave 1 2).code [[1],[0]] = false := by decide
example : valid (wave 1 2).code [[0],[0],[1]] = false := by decide
example : valid (wave 1 2).code [[0]] = false := by decide
example : valid (wave 1 2).code [[0],[1],[99]] = false := by decide

end IRComparison.PipeliningExamples
