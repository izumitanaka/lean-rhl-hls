import IRComparison.Frontend.LeanWordCommand

/-! Regressions for call-time scalar values. Every example uses the ordinary
Lean entry, with no compatibility fallback. The emitted correspondence
statements quantify over all indices, scalar inputs and initial States. -/
namespace IRComparison.RetainedArgumentExamples
open HybridWord
set_option maxRecDepth 65536
set_option maxHeartbeats 0

def updateArgument (_i _x _y : Word) (s : HybridWord.State) : Option HybridWord.State :=
  let update := fun (value : Word) (memory : HybridWord.State) =>
    let memory := memory.set 0 7
    some (memory.set 1 value)
  update (s.regs 0) s
hls_word updateArgument as updateArgumentHLS
example : updateArgumentHLS.wordBody = .letValue (.reg 0)
    (.seq (.assign 0 (.lit 7)) (.assign 1 (.local 0))) := rfl

theorem updateArgument_snapshot (i x y : Word) (s : HybridWord.State) :
    updateArgumentHLS.wordBody.eval i x y s [] =
      some ((s.set 0 7).set 1 (s.regs 0)) :=
  updateArgumentHLS.wordBody_correct i x y s

def severalArguments (_i _x _y : Word) (s : HybridWord.State) : Option HybridWord.State :=
  let update := fun (first : Word) (memory : HybridWord.State) (second : BitVec 32) =>
    let memory := memory.set 0 7
    let memory := memory.set 1 first
    some (memory.set 2 second)
  update (s.regs 0) s (s.regs 1 + 1)
hls_word severalArguments as severalArgumentsHLS
example : severalArgumentsHLS.wordBody = .letValue (.reg 0)
    (.letValue (.add (.reg 1) (.lit 1))
      (.seq (.assign 0 (.lit 7)) (.seq (.assign 1 (.local 1)) (.assign 2 (.local 0))))) := rfl

theorem severalArguments_snapshot (i x y : Word) (s : HybridWord.State) :
    severalArgumentsHLS.wordBody.eval i x y s [] =
      some (((s.set 0 7).set 1 (s.regs 0)).set 2 (s.regs 1 + 1)) :=
  severalArgumentsHLS.wordBody_correct i x y s

def capturedArgument (_i _x _y : Word) (s : HybridWord.State) : Option HybridWord.State :=
  let captured := s.regs 2
  let update := fun (value : BitVec 32) (memory : HybridWord.State) =>
    let memory := memory.set 0 7
    some (memory.set 1 (value + captured))
  update (s.regs 0) s
hls_word capturedArgument as capturedArgumentHLS

def nestedArgument (_i _x _y : Word) (s : HybridWord.State) : Option HybridWord.State :=
  let outer := fun (value : Word) (memory : HybridWord.State) =>
    let inner := fun (saved : BitVec 32) (memory : HybridWord.State) =>
      let memory := memory.set 0 7
      some (memory.set 1 (saved + value))
    inner (memory.regs 1) memory
  outer (s.regs 0) s
hls_word nestedArgument as nestedArgumentHLS

def branchArgument (_i _x _y : Word) (s : HybridWord.State) : Option HybridWord.State := do
  let update := fun (value : Word) (memory : HybridWord.State) =>
    let memory := memory.set 0 7
    some (memory.set 1 value)
  if s.regs 2 != 0 then
    let value ← (s.arrays 0)[0]?
    update value s
  else
    update (s.regs 0) s
hls_word branchArgument as branchArgumentHLS

def loopArgument (_i _x _y : Word) (s : HybridWord.State) : Option HybridWord.State := do
  let mut t := s
  for j in HybridWord.range 0 3 1 do
    let update := fun (value : Word) (memory : HybridWord.State) =>
      let memory := memory.set 0 (j+7)
      some (memory.set 1 value)
    t ← update (t.regs 0) t
  return t
hls_word loopArgument as loopArgumentHLS

def foldedArgument (_i _x _y : Word) (s : HybridWord.State) : Option HybridWord.State :=
  (List.range (3 : Word).toNat).foldlM (fun memory k =>
    let j := BitVec.ofNat 32 k
    let update := fun (value : Word) (memory : HybridWord.State) =>
      let memory := memory.set 0 (j+7)
      some (memory.set 1 value)
    update (memory.regs 0) memory) s
hls_word foldedArgument as foldedArgumentHLS

/-- The read is evaluated even if the helper never uses its scalar argument. -/
def unusedRead (_i _x _y : Word) (s : HybridWord.State) : Option HybridWord.State := do
  let unused ← (s.arrays 0)[0]?
  let ignore := fun (_value : Word) (memory : HybridWord.State) => some (memory.set 0 7)
  ignore unused s
hls_word unusedRead as unusedReadHLS

/-- A read in the unselected branch remains unobserved. -/
def unselectedRead (_i _x _y : Word) (s : HybridWord.State) : Option HybridWord.State := do
  let update := fun (value : Word) (memory : HybridWord.State) =>
    let memory := memory.set 0 7
    some (memory.set 1 value)
  if s.regs 2 != 0 then
    let value ← (s.arrays 0)[0]?
    update value s
  else
    return s
hls_word unselectedRead as unselectedReadHLS

def initial : HybridWord.State := ⟨fun r => if r = 0 then 3 else if r = 1 then 4 else 0,fun _ => #[]⟩
example : (updateArgumentHLS.wordBody.eval 0 0 0 initial []).map
    (fun t => (t.regs 0,t.regs 1)) = some (7,3) := by decide
example : (severalArgumentsHLS.wordBody.eval 0 0 0 initial []).map
    (fun t => (t.regs 0,t.regs 1,t.regs 2)) = some (7,3,5) := by decide
example : (unusedReadHLS.wordBody.eval 0 0 0 initial []).isNone = true := by decide
example : (unselectedReadHLS.wordBody.eval 0 0 0 initial []).map (fun t => t.regs 0) = some 3 := by decide
example : (branchArgumentHLS.wordBody.eval 0 0 0 (initial.set 2 1) []).isNone = true := by decide
example : (loopArgumentHLS.wordBody.eval 0 0 0 initial []).map (fun t => (t.regs 0,t.regs 1)) = some (9,8) := by decide
example : (foldedArgumentHLS.wordBody.eval 0 0 0 initial []).map (fun t => (t.regs 0,t.regs 1)) = some (9,8) := by decide
example : (nestedArgumentHLS.wordBody.eval 0 0 0 initial []).map (fun t => (t.regs 0,t.regs 1)) = some (7,7) := by decide

end IRComparison.RetainedArgumentExamples
