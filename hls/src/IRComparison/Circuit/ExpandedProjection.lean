import IRComparison.Circuit.IterationProjection

namespace IRComparison.Circuit

def ModeScoped (limit : Nat) : GlobalPipeline.InputMode → Prop
  | .memory a _ _ | .channel a => a < limit

structure InstructionScoped (limit : Nat) (c : HybridIR.Instruction) : Prop where
  input : c.input < limit
  mode : ModeScoped limit c.mode
  body : ∀ block ∈ c.blocks, ∀ a ∈ allCommandArrays block.body, a < limit

theorem mode_trim (mode : GlobalPipeline.InputMode) (safe : ModeScoped limit mode) :
    mode.eval (trimState limit s) qs = mode.eval s qs := by
  cases mode with
  | channel => rfl
  | memory a order fifo => simp only [GlobalPipeline.InputMode.eval,trimState,show a < limit from safe,↓reduceIte]

theorem blocks_trim (blocks : List HybridIR.Block)
    (safe : ∀ block ∈ blocks, ∀ a ∈ allCommandArrays block.body, a < limit) :
    (HybridIR.blocksEval input x y blocks old s qi qo).map (trimTriple limit) =
      HybridIR.blocksEval input x y blocks old (trimState limit s) qi qo := by
  induction blocks generalizing old s qi qo with
  | nil => rfl
  | cons bl bs ih =>
    have first := safe bl (by simp)
    have rest : ∀ block ∈ bs, ∀ a ∈ allCommandArrays block.body, a < limit :=
      fun block hb => safe block (by simp [hb])
    rw [HybridIR.blocksEval,HybridIR.blocksEval]
    cases WindowFIFO.execute input old bl.loads qi with
    | none => rfl
    | some pair =>
      obtain ⟨values,remaining⟩ := pair
      simp only [bind,Option.bind,← command_trim bl.body first]
      cases bl.body.eval bl.index x y s qo values with
      | none => rfl
      | some pair => obtain ⟨t,out⟩ := pair; exact ih rest

def trimInstructionResult (limit : Nat) (p : State × GlobalPipeline.Queues) := (trimState limit p.1,p.2)

theorem instruction_trim (c : HybridIR.Instruction) (safe : InstructionScoped limit c) :
    (c.eval x y s qs).map (trimInstructionResult limit) = c.eval x y (trimState limit s) qs := by
  simp only [HybridIR.Instruction.eval,mode_trim c.mode safe.mode]
  cases c.mode.eval s qs with
  | none => rfl
  | some qi =>
    simp only [bind,Option.bind]
    have inputSame : arrayInput ((trimState limit s).arrays c.input) = arrayInput (s.arrays c.input) := by
      simp [trimState,safe.input]
    rw [inputSame]
    cases ho : c.output with
    | none =>
      simp only [← blocks_trim c.blocks safe.body]
      cases HybridIR.blocksEval (arrayInput (s.arrays c.input)) x y c.blocks [] s qi [] <;> rfl
    | some a =>
      simp only [← trim_erase,← blocks_trim c.blocks safe.body]
      cases HybridIR.blocksEval (arrayInput (s.arrays c.input)) x y c.blocks [] (StreamConsumer.erase a s) qi [] with
      | none => rfl
      | some triple =>
        obtain ⟨t,rest,out⟩ := triple
        simp only [Option.map_some,bind,Option.bind,pure,trimTriple,trimInstructionResult,trim_erase]

theorem execute_trim (code : List HybridIR.Instruction) (safe : ∀ c ∈ code, InstructionScoped limit c) :
    (HybridIR.execute x y code s qs).map (trimState limit) = HybridIR.execute x y code (trimState limit s) qs := by
  induction code generalizing s qs with
  | nil => rfl
  | cons c cs ih =>
    have first := safe c (by simp)
    have rest : ∀ c ∈ cs, InstructionScoped limit c := fun c hc => safe c (by simp [hc])
    rw [HybridIR.execute,HybridIR.execute,← instruction_trim c first]
    cases c.eval x y s qs with
    | none => rfl
    | some pair => obtain ⟨t,qs⟩ := pair; exact ih rest

end IRComparison.Circuit
