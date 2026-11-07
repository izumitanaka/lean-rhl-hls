import IRComparison.Hybrid.HybridRuntime
import IRComparison.Hybrid.HybridGlobal

namespace IRComparison.HybridIR

def memoryBlocks (bs : List HybridWindowTransport.Block) : List Block :=
  bs.map (fun b => ⟨b.index,b.loads,b.body.target⟩)
theorem memoryBlocks_correct (bs : List HybridWindowTransport.Block) :
    blocksEval input x y (memoryBlocks bs) old s qi qo =
      (HybridWindowTransport.eval input x y bs old s qi).map (fun (t,rest) => (t,rest,qo)) := by
  induction bs generalizing old s qi with
  | nil => rfl
  | cons b bs ih =>
    simp only [memoryBlocks,List.map_cons,blocksEval,HybridWindowTransport.eval]
    cases WindowFIFO.execute input old b.loads qi with
    | none => rfl
    | some pair =>
      obtain ⟨vs,rest⟩ := pair
      simp only [bind,Option.bind,MemoryCmd.target_correct]
      cases b.body.eval b.index x y s vs with
      | none => rfl
      | some t => exact ih

def lowerInstruction (c : HybridGlobal.Instruction) : Instruction :=
  match c.action with
  | .keep bs => ⟨c.input,c.mode,none,memoryBlocks bs⟩
  | .send a bs => ⟨c.input,c.mode,some a,bs⟩

theorem lowerInstruction_correct (c : HybridGlobal.Instruction) :
    (lowerInstruction c).eval x y s qs = c.eval x y s qs := by
  cases c with
  | mk input mode action =>
    cases action with
    | keep bs =>
      simp only [lowerInstruction,Instruction.eval,HybridGlobal.Instruction.eval,memoryBlocks_correct]
      cases mode.eval s qs with
      | none => rfl
      | some q =>
        simp only [bind,Option.bind,memoryBlocks_correct]
        cases HybridWindowTransport.eval (arrayInput (s.arrays input)) x y bs [] s q <;> rfl
    | send a bs => simp only [lowerInstruction,Instruction.eval,HybridGlobal.Instruction.eval]

def lower (code : List HybridGlobal.Instruction) := code.map lowerInstruction

theorem lower_correct (code : List HybridGlobal.Instruction) :
    execute x y (lower code) s qs = HybridGlobal.execute x y code s qs := by
  induction code generalizing s qs with
  | nil => rfl
  | cons c cs ih =>
    simp only [lower,List.map_cons,execute,HybridGlobal.execute,lowerInstruction_correct]
    cases c.eval x y s qs with
    | none => rfl
    | some pair => obtain ⟨t,rest⟩ := pair; exact ih

/-- Direct mixed-IR window and FIFO optimization, followed only by lowering
    mixed memory commands into the communication-capable mixed command type. -/
def Program (outputs : List Nat) (sizes : Nat → Nat) (stages : List HybridStage.Stage) :=
  HybridGlobal.Program outputs sizes stages

def Program.code (p : Program outputs sizes stages) := lower p.plan.code
def Program.eval (p : Program outputs sizes stages) (x y : Int) (s : State) :=
  execute x y p.code s (fun _ => [])

theorem Program.correct (p : Program outputs sizes stages) (s : State)
    (layout : PipelineShapes.Layout sizes s) (ready : HybridStage.Ready x y stages s) :
    (p.eval x y s).map (PipelineUse.observe outputs) =
      (HybridStage.source x y stages s).map (PipelineUse.observe outputs) := by
  unfold Program.eval Program.code
  rw [lower_correct]
  exact HybridGlobal.Program.correct p s layout ready

def compile (outputs : List Nat) (sizes : Nat → Nat) (stages : List HybridStage.Stage) :
    Option (Program outputs sizes stages) := HybridGlobal.compile outputs sizes stages

/-- A named Lean body enters mixed IR before any memory optimization. -/
structure Kernel where
  body : MemoryCmd
  native : Int → Int → Int → State → Option State
  correct : ∀ i x y s, body.eval i x y s [] = native i x y s
  size : Nat
  array : Nat
  start : Int
  stride : Int
  count : Nat
  supplier : Unit → List Int

def Kernel.source (k : Kernel) (x y : Int) (s : State) :=
  Source.iterate (fun i => k.native i x y) k.stride k.count k.start s

def Kernel.window (k : Kernel) := HybridWindowTransport.compile
  k.size k.array k.body k.stride k.count k.start (k.supplier ())

def Kernel.stage (k : Kernel) : HybridStage.Stage :=
  (HybridStage.ofSelected k.window).rebase k.source (by
    intro x y s
    exact Source.iterate_congr _ _ (fun i t => k.correct i x y t) k.stride k.count k.start s)

def stages (ks : List Kernel) := ks.map Kernel.stage

def source (x y : Int) : List Kernel → State → Option State
  | [],s => some s
  | k::ks,s => do source x y ks (← k.source x y s)

theorem stages_source (ks : List Kernel) : HybridStage.source x y (stages ks) s = source x y ks s := by
  induction ks generalizing s with
  | nil => rfl
  | cons k ks ih =>
    change (k.source x y s).bind (HybridStage.source x y (stages ks)) = (k.source x y s).bind (source x y ks)
    cases k.source x y s with
    | none => rfl
    | some t => exact ih

def compileKernels (outputs : List Nat) (sizes : Nat → Nat) (ks : List Kernel) :=
  compile outputs sizes (stages ks)

theorem kernels_correct (p : Program outputs sizes (stages ks)) (s : State)
    (layout : PipelineShapes.Layout sizes s) (ready : HybridStage.Ready x y (stages ks) s) :
    (Program.eval p x y s).map (PipelineUse.observe outputs) =
      (source x y ks s).map (PipelineUse.observe outputs) := by
  rw [Program.correct p s layout ready,stages_source]

end IRComparison.HybridIR
