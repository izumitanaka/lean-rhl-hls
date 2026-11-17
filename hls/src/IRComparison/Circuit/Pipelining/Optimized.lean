import IRComparison.Circuit.Pipelining.StaticControl

namespace IRComparison.Circuit.Pipelining

/-- Greedy earliest-clock proposal. RAW/WAW edges require a later clock;
WAR-only edges allow the same clock, in source order, but never an earlier
one. Independent operations may move freely. The generally proved checker
still validates the entire proposal, including permutations and bundles. -/
def earliestProposal {α : Type} [ExpressionEvaluation α] [ExpressionDependencies α] (code : Array (Action α)) : Cycles := Id.run do
  let mut times : List (Nat × Nat) := []
  for i in List.range code.size do
    let t := times.foldl (fun n (j,t) =>
      if independent (actionAt code j) (actionAt code i) then n
      else if orderedCompatible (actionAt code j) (actionAt code i) then max n t
      else max n (t+1)) 0
    times := times ++ [(i,t)]
  return groupTimes times

theorem unified_schedule_correct_with (backend : CountedBackend) (p : HybridUnifiedPipeline.Plan outputs sizes ks)
    (layout : Array (Nat × Nat))
    (covered : layoutCovers layout (HybridUnifiedPipeline.lower p) = true)
    (known : hasSendBounds (HybridUnifiedPipeline.lower p) = true)
    (communication : checkCommunication (HybridUnifiedPipeline.lower p) = .ok ())
    (outputsSafe : ∀ a ∈ outputs, a < layoutLimit layout)
    (s : State) (x y : Int)
    (sized : PipelineShapes.Layout sizes s) (ready : p.Ready x y s) :
    ∃ result, (scheduleWith backend.build layout (HybridUnifiedPipeline.lower p)).schedule.Eval
      ((scheduleWith backend.build layout (HybridUnifiedPipeline.lower p)).schedule.assemble
        (scheduleWith backend.build layout (HybridUnifiedPipeline.lower p)).build.queues).capacity
        ⟨s,(fun n => if n = 0 then x else if n = 1 then y else 0),fun _ => []⟩ result ∧
      result.map (fun p => PipelineUse.observe outputs p.data) =
        (HybridIR.source x y ks s).map (PipelineUse.observe outputs) := by
  have connection : ∀ (result : Option Payload),
      result.map (fun p : Payload => PipelineUse.observe outputs p.data) =
        (p.eval x y s).map (PipelineUse.observe outputs) →
      result.map (fun p : Payload => PipelineUse.observe outputs p.data) =
        (HybridIR.source x y ks s).map (PipelineUse.observe outputs) := by
    intro result h
    exact h.trans (p.correct s sized ready)
  cases p with
  | symbolic program =>
    obtain ⟨result,he,ho⟩ := symbolic_pipeline_schedule_with backend layout program.plan.code covered known communication outputsSafe s x y
    exact ⟨result,he,connection result ho⟩
  | regions =>
    obtain ⟨result,he,ho⟩ := regions_pipeline_schedule layout _ covered outputsSafe s x y
    exact ⟨result,he,connection result ho⟩
  | expanded program =>
    obtain ⟨result,he,ho⟩ := expanded_pipeline_schedule layout program.code covered known communication outputsSafe
      s x y
    exact ⟨result,he,connection result ho⟩
  | compact program =>
    obtain ⟨result,he,ho⟩ := compact_pipeline_schedule layout _ covered known outputsSafe
      s x y
    refine ⟨result,he,connection result ?_⟩
    simpa only [HybridCompactChainControl.lowerRoot_correct] using ho

theorem optimized_schedule_correct_with (backend : CountedBackend) (p : HybridWord.Plan outputs sizes ks)
    (layout : Array (Nat × Nat))
    (covered : layoutCovers layout (HybridUnifiedPipeline.lower p) = true)
    (known : hasSendBounds (HybridUnifiedPipeline.lower p) = true)
    (communication : checkCommunication (HybridUnifiedPipeline.lower p) = .ok ())
    (outputsSafe : ∀ a ∈ outputs, a < layoutLimit layout)
    (s : HybridWord.State) (x y : HybridWord.Word)
    (sized : PipelineShapes.Layout sizes s.encode) (ready : p.Ready (HybridWord.encode x) (HybridWord.encode y) s.encode) :
    ∃ result, (scheduleWith backend.build layout (HybridUnifiedPipeline.lower p)).schedule.Eval
      ((scheduleWith backend.build layout (HybridUnifiedPipeline.lower p)).schedule.assemble
        (scheduleWith backend.build layout (HybridUnifiedPipeline.lower p)).build.queues).capacity (wordPayload s x y) result ∧
      result.map (fun p => PipelineUse.observe outputs p.data) =
        (HybridWord.source x y ks s).map (fun s => PipelineUse.observe outputs s.encode) := by
  obtain ⟨result,he,ho⟩ := unified_schedule_correct_with backend p layout covered known communication outputsSafe
    s.encode (HybridWord.encode x) (HybridWord.encode y) sized ready
  exact ⟨result,he,by simpa only [HybridWord.source_correct,Option.map_map,Function.comp_def] using ho⟩

abbrev unified_schedule_correct {outputs : List Nat} {sizes : Nat → Nat} {ks : List HybridIR.Kernel} :=
  unified_schedule_correct_with (outputs:=outputs) (sizes:=sizes) (ks:=ks) CountedBackend.legacy
abbrev optimized_schedule_correct {outputs : List Nat} {sizes : Nat → Nat} {ks : List HybridWord.Kernel} :=
  optimized_schedule_correct_with (outputs:=outputs) (sizes:=sizes) (ks:=ks) CountedBackend.legacy

def compileOptimizedScheduled (p : HybridWord.Plan outputs sizes ks) (layout : Array (Nat × Nat))
    (fuel : Nat := 4096) : Except String WordCircuit := do
  let source := HybridUnifiedPipeline.lower p
  checkLayout layout source
  checkSendBudgets source
  checkCommunication source
  let g := schedule layout source
  let some (actions,_) := linearize fuel [] g.schedule
    | throw "control is data-dependent or static expansion budget is exhausted"
  let plan := Pipelining.compile actions.toArray (earliestProposal actions.toArray)
  let r := realize actions.toArray plan.cycles g.build.wires
  let a := declarationArtifact r.batches r.widths g.build.memories layout g.build.queues
  let code ← generateBatchModule a r.batches outputs
  return ⟨a,r,code,g.build.wires.size,plan.accepted⟩

structure OptimizedFacts (p : HybridWord.Plan outputs sizes ks) (layout : Array (Nat × Nat))
    (fuel : Nat) (built : WordCircuit) : Prop where
  covered : layoutCovers layout (HybridUnifiedPipeline.lower p) = true
  known : hasSendBounds (HybridUnifiedPipeline.lower p) = true
  communication : checkCommunication (HybridUnifiedPipeline.lower p) = .ok ()
  compiled : ∃ actions after,
    linearize fuel [] (schedule layout (HybridUnifiedPipeline.lower p)).schedule = some (actions,after) ∧
    let g := schedule layout (HybridUnifiedPipeline.lower p)
    let plan := Pipelining.compile actions.toArray (earliestProposal actions.toArray)
    let r := realize actions.toArray plan.cycles g.build.wires
    built.realization = r ∧
    built.artifact = declarationArtifact r.batches r.widths g.build.memories layout g.build.queues ∧
    generateBatchModule built.artifact r.batches outputs = .ok built.module

theorem compileOptimizedScheduled_facts (h : compileOptimizedScheduled p layout fuel = .ok built) :
    OptimizedFacts p layout fuel built := by
  cases hl : checkLayout layout (HybridUnifiedPipeline.lower p) <;>
    simp [compileOptimizedScheduled,hl,bind,Except.bind] at h
  cases hlv : checkSendBudgets (HybridUnifiedPipeline.lower p) <;> simp [hlv] at h
  cases hcom : checkCommunication (HybridUnifiedPipeline.lower p) <;> simp [hcom] at h
  rename_i ul ub uc
  cases ul; cases ub; cases uc
  refine ⟨checkLayout_covered hl,checkSendBudgets_sound hlv,hcom,?_⟩
  cases hs : linearize fuel [] (schedule layout (HybridUnifiedPipeline.lower p)).schedule <;> simp [hs] at h
  rename_i result
  refine ⟨result.1,result.2,rfl,?_⟩
  split at h
  · contradiction
  · cases h
    exact ⟨rfl,rfl,by assumption⟩

theorem optimized_batches_correct {p : HybridWord.Plan outputs sizes ks}
    (success : compileOptimizedScheduled p layout fuel = .ok built)
    (outputsSafe : ∀ a ∈ outputs, a < layoutLimit layout)
    (s : HybridWord.State) (x y : HybridWord.Word)
    (sized : PipelineShapes.Layout sizes s.encode) (ready : p.Ready (HybridWord.encode x) (HybridWord.encode y) s.encode) :
    (runBatches (capacityOf built.artifact.machine.capacities) built.realization.batches (wordPayload s x y)).map
      (fun p => PipelineUse.observe outputs p.data) =
      (HybridWord.source x y ks s).map (fun s => PipelineUse.observe outputs s.encode) := by
  have facts := compileOptimizedScheduled_facts success
  obtain ⟨actions,after,compiled,realization,artifact,_⟩ := facts.compiled
  obtain ⟨result,he,ho⟩ := optimized_schedule_correct p layout facts.covered facts.known facts.communication
    outputsSafe s x y sized ready
  have linear := (linearize_correct fuel _ compiled (by intro k v h; cases h) he).1
  change evalList (Action.eval (lower layout (HybridUnifiedPipeline.lower p)).machine.capacity)
    actions (wordPayload s x y) = result at linear
  have caps : capacityOf built.artifact.machine.capacities =
      (lower layout (HybridUnifiedPipeline.lower p)).machine.capacity := by rw [artifact]; rfl
  have data : (runBatches (capacityOf built.artifact.machine.capacities) built.realization.batches (wordPayload s x y)).map Payload.data =
      result.map Payload.data := by
    rw [realization,realize_correct,compile_correct,sourceEval_eq]
    simp only [caps,linear]
  have observed := congrArg (Option.map (PipelineUse.observe outputs)) data
  simpa only [Option.map_map,Function.comp_def] using observed.trans (by simpa only [Option.map_map,Function.comp_def] using ho)

def PublicObservation (shape : StorageShape) (outputs : List Nat) (r : Circuit.Runtime) (expected : Option State) : Prop :=
  ResultObservation shape.registers
    (fun actual final => ∀ n ∈ outputs, shape.hasMemory n → actual.arrays n = final.arrays n) r expected

theorem public_observation (same : StorageAgreement shape r logical)
    (h : logical.result.map (Option.map (PipelineUse.observe outputs)) = some (expected.map (PipelineUse.observe outputs))) :
    PublicObservation shape outputs r expected := by
  cases hl : logical.result with
  | none => simp [hl] at h
  | some actual =>
    have obs := source_observation same hl
    cases actual with
    | none => cases expected <;> simp_all [PublicObservation,SourceObservation,ResultObservation]
    | some actual =>
      cases expected with
      | none => simp [hl] at h
      | some expected =>
        have eq : PipelineUse.observe outputs actual = PipelineUse.observe outputs expected := by simpa [hl] using h
        have regs : actual.regs = expected.regs := congrArg Prod.fst eq
        have arrays : outputs.map actual.arrays = outputs.map expected.arrays := congrArg Prod.snd eq
        exact ⟨obs.1,obs.2.1,fun n hn => (obs.2.2.1 n hn).trans (congrFun regs n),
          fun n hn live => (obs.2.2.2 n live).trans (List.map_eq_map_iff.mp arrays n hn)⟩

/-- Memory optimization, static generated-control expansion, checked clock
placement, holding-register reuse and the actual printed RTL all compose.
Only public observations are preserved: FIFO-eliminated private arrays need
not remain materialized in the target. -/
theorem compileOptimizedScheduled_correct {p : HybridWord.Plan outputs sizes ks}
    (success : compileOptimizedScheduled p layout fuel = .ok built)
    (outputsSafe : ∀ a ∈ outputs, a < layoutLimit layout)
    (s : HybridWord.State) (x y : HybridWord.Word)
    (sized : PipelineShapes.Layout sizes s.encode) (ready : p.Ready (HybridWord.encode x) (HybridWord.encode y) s.encode)
    (fits : built.artifact.InputFits s.encode)
    (r : RTL.InterfaceState built.artifact.storageShape) (running : r.Running)
    (same : StorageAgreement built.artifact.storageShape r.core.decode ((wordPayload s x y).at 0)) :
    ∃ result, (SystemVerilog.Concrete.parseModule built.module.text).bind (fun parsed =>
      parsed.run built.artifact.storageShape (built.realization.batches.length+1) r) = some result ∧
      PublicObservation built.artifact.storageShape outputs result.core.decode
        ((HybridWord.source x y ks s).map HybridWord.State.encode) := by
  have facts := compileOptimizedScheduled_facts success
  obtain ⟨actions,after,compiled,realization,artifact,generated⟩ := facts.compiled
  rw [← realization] at generated
  have checks := (generateBatchModule_components generated).1
  have initial : BatchBound built.artifact built.realization.batches ((wordPayload s x y).at 0) :=
    ⟨word_initial_bound checks.initial s x y,⟨fits,by intro q; simp [wordPayload,Payload.at,Circuit.Runtime.payload]⟩,by simp [Payload.at]⟩
  obtain ⟨result,executed,agrees,_⟩ := generated_batch_run generated _ initial r running same
    (built.realization.batches.length+1)
  refine ⟨result,executed,public_observation agrees ?_⟩
  rw [shape_frame,batchProgram_correct _ checks.widths _ (word_initial_bound checks.initial s x y)]
  simpa only [Option.map_some,Option.map_map,Function.comp_def] using
    congrArg some (optimized_batches_correct success outputsSafe s x y sized ready)

end IRComparison.Circuit.Pipelining
