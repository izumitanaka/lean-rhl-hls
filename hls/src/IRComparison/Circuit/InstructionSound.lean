import IRComparison.Circuit.InstructionContract

namespace IRComparison.Circuit

/-- Connect the actual instruction schedule to the source instruction. The
state view hides fresh snapshots and maps physical FIFO IDs back to the
whole-array communication interface. -/
theorem instruction_schedule_correct
    (contract : InstructionContract ids mapping limit next cap a c)
    (channels : ChannelMap ids mapping next) (consistent : instructionChannels ids c)
    (scopeOK : InstructionScoped limit c) (outputScope : ∀ n ∈ c.output.toList, n < limit)
    (p : Payload) (hx : p.wires 0 = x) (hy : p.wires 1 = y) :
    ∃ r, (a.schedule c).Eval cap p r ∧
      r.map (instructionView ids mapping limit) =
        c.eval x y (trimState limit p.data) (channelView ids mapping p.queues) := by
  let base := p.snapshot a.frozen c.input
  have init := inputSetup_correct c.mode a.inputQueue base contract.preload
  rw [inputSetupResult_source p c.mode scopeOK.mode contract.fresh contract.inputMatch] at init
  have separate : ∀ n ∈ c.output.toList, n ≠ a.frozen := by
    intro n hn; have := outputScope n hn; have := contract.fresh; omega
  have inputSeparate : c.input ≠ a.frozen := by have := scopeOK.input; have := contract.fresh; omega
  have scheduleEq : a.schedule c = Schedule.seq (.step (.snapshot a.frozen c.input))
    (.seq (inputSetup c.mode a.inputQueue) (.seq (.step (.clear a.outputQueue))
      (.seq (eraseOutput c.output) (.seq a.body (.seq (eraseOutput c.output) (.step (.clear a.inputQueue))))))) := by
    cases hmode : c.mode <;> cases hout : c.output <;> simp [InstructionLayout.schedule,inputSetup,eraseOutput,hmode,hout]
  rw [scheduleEq]
  cases hm : c.mode.eval (trimState limit p.data) (channelView ids mapping p.queues) with
  | none =>
    rw [hm] at init
    refine ⟨none,.seq (snapshot_eval p a.frozen c.input) (.seq_error init),?_⟩
    simp [HybridIR.Instruction.eval,hm]
  | some inputValues =>
    rw [hm] at init
    let loaded := base.setQueue a.inputQueue inputValues
    let bodyInput := (loaded.clear a.outputQueue).eraseOutput c.output
    have inputQ : bodyInput.queues a.inputQueue = inputValues := by
      simp [bodyInput,eraseOutput_queues,Payload.clear,loaded,Payload.setQueue,contract.distinct]
    have outputQ : bodyInput.queues a.outputQueue = [] := by
      simp [bodyInput,eraseOutput_queues,Payload.clear]
    have inputArray : arrayInput (bodyInput.data.arrays a.frozen) = arrayInput ((trimState limit p.data).arrays c.input) := by
      simp only [bodyInput,eraseOutput_snapshot _ _ separate,Payload.clear,loaded,Payload.setQueue,base,Payload.snapshot]
      simp [trimState,scopeOK.input]
    have bodyState : trimState limit bodyInput.data = eraseData c.output (trimState limit p.data) := by
      dsimp only [bodyInput]
      rw [eraseOutput_data,eraseData_trim]
      change eraseData c.output (trimState limit (p.snapshot a.frozen c.input).data) = _
      rw [trim_snapshot_ge p c.input contract.fresh]
    have bx : bodyInput.wires 0 = x := by simpa [bodyInput,eraseOutput_wires,Payload.clear,loaded,Payload.setQueue,base,Payload.snapshot] using hx
    have by' : bodyInput.wires 1 = y := by simpa [bodyInput,eraseOutput_wires,Payload.clear,loaded,Payload.setQueue,base,Payload.snapshot] using hy
    obtain ⟨r,hr,ho⟩ := contract.body.correct bodyInput x y bx by' outputQ
    have correspondence := blocks_trim (input:=arrayInput (bodyInput.data.arrays a.frozen)) (x:=x) (y:=y)
      (old:=[]) (s:=bodyInput.data) (qi:=bodyInput.queues a.inputQueue) (qo:=[]) c.blocks scopeOK.body
    rw [inputQ,inputArray,bodyState] at correspondence
    cases hb : HybridIR.blocksEval (arrayInput (bodyInput.data.arrays a.frozen)) x y c.blocks [] bodyInput.data
        (bodyInput.queues a.inputQueue) [] with
    | none =>
      have rn : r = none := by
        cases r with
        | none => rfl
        | some q => simp [hb] at ho
      subst r
      have bodyFailure : HybridIR.blocksEval (arrayInput ((trimState limit p.data).arrays c.input)) x y c.blocks []
          (eraseData c.output (trimState limit p.data)) inputValues [] = none := by
        rw [inputQ,inputArray] at hb
        rw [hb] at correspondence
        exact correspondence.symm
      refine ⟨none,.seq (snapshot_eval p a.frozen c.input) (.seq init (.seq (clear_eval loaded a.outputQueue)
        (.seq (eraseOutput_eval (loaded.clear a.outputQueue) c.output) (.seq_error hr)))),?_⟩
      simp only [HybridIR.Instruction.eval,hm,bind,Option.bind]
      change none = (HybridIR.blocksEval _ _ _ _ _ (eraseData c.output _) _ _).bind _
      rw [bodyFailure]; rfl
    | some triple =>
      obtain ⟨t,remaining,out⟩ := triple
      cases r with
      | none => simp [hb] at ho
      | some q =>
        have obs : q.data = t ∧ q.queues = GlobalPipeline.put (GlobalPipeline.put bodyInput.queues a.inputQueue remaining) a.outputQueue out := by
          simpa only [hb,Option.map_some,Option.some.injEq,Prod.mk.injEq] using ho
        have sourceBody : HybridIR.blocksEval (arrayInput ((trimState limit p.data).arrays c.input)) x y c.blocks []
            (eraseData c.output (trimState limit p.data)) inputValues [] = some (trimState limit t,remaining,out) := by
          rw [inputQ,inputArray] at hb
          rw [hb] at correspondence
          exact correspondence.symm
        let final := (q.eraseOutput c.output).clear a.inputQueue
        have queueResult : final.queues = GlobalPipeline.put (GlobalPipeline.put p.queues a.inputQueue []) a.outputQueue out := by
          change GlobalPipeline.put (q.eraseOutput c.output).queues a.inputQueue [] = _
          rw [eraseOutput_queues,obs.2]
          have baseQueues : bodyInput.queues = GlobalPipeline.put (GlobalPipeline.put p.queues a.inputQueue inputValues) a.outputQueue [] := by
            dsimp only [bodyInput]
            rw [eraseOutput_queues]; rfl
          rw [baseQueues,queues_after_instruction p.queues contract.distinct]
        have viewQueue := channelView_output (physical:=GlobalPipeline.put p.queues a.inputQueue [])
          (values:=out) channels contract.outputMatch
        rw [channelView_input_clear channels consistent contract.inputMatch] at viewQueue
        refine ⟨some final,.seq (snapshot_eval p a.frozen c.input) (.seq init (.seq (clear_eval loaded a.outputQueue)
          (.seq (eraseOutput_eval (loaded.clear a.outputQueue) c.output) (.seq hr
            (.seq (eraseOutput_eval q c.output) (clear_eval (q.eraseOutput c.output) a.inputQueue)))))),?_⟩
        simp only [Option.map_some,instructionView,HybridIR.Instruction.eval,hm,bind,Option.bind]
        change some (trimState limit final.data,channelView ids mapping final.queues) =
          (HybridIR.blocksEval _ _ _ _ _ (eraseData c.output _) _ _).bind _
        rw [sourceBody]
        simp only [bind,Option.bind]
        rw [queueResult,viewQueue]
        have dataResult : trimState limit final.data = eraseData c.output (trimState limit t) := by
          change trimState limit (q.eraseOutput c.output).data = _
          rw [eraseOutput_data,eraseData_trim,obs.1]
        rw [dataResult]
        cases hout : c.output <;> simp [outputQueues,eraseData,hout]

end IRComparison.Circuit
