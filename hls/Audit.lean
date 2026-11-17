import IRComparison.Tests
#print axioms IRComparison.AutomaticStages.indexExpr_correct
#print axioms IRComparison.AutomaticStages.indexBody_correct
#print axioms IRComparison.AutomaticStages.pieces_correct
#print axioms IRComparison.AutomaticStages.pieces_declared
#print axioms IRComparison.AutomaticStages.entry_closed
#print axioms IRComparison.FixedHLS.Entry.staged_correct
#print axioms IRComparison.FixedHLS.Entry.staged_closed
#print axioms IRComparison.FixedHLS.Entry.artifact_correct
#print axioms IRComparison.HybridSymbolicProducer.BodyShape.word
#print axioms IRComparison.HybridSymbolicProducer.BodyShape.sendBound
#print axioms IRComparison.HybridSymbolicProducer.Compiled.word
#print axioms IRComparison.HybridSymbolicProducer.Compiled.sendBound
#print axioms IRComparison.HybridSymbolicLoop.Selected.word
#print axioms IRComparison.HybridSymbolicGlobal.Plan.word
#print axioms IRComparison.Circuit.word_compactStages
#print axioms IRComparison.Circuit.symbolic_step_sendBound
#print axioms IRComparison.Circuit.symbolic_plan_sendBounds
#print axioms IRComparison.Circuit.compile_sendBudgets
#print axioms IRComparison.Circuit.compileStep_policy
#print axioms IRComparison.Circuit.compilePolicy_policy
#print axioms IRComparison.Circuit.compile_policy
#print axioms IRComparison.Circuit.respects_communication
#print axioms IRComparison.Circuit.compile_communication
#print axioms IRComparison.Circuit.compile_memory_checks
#print axioms IRComparison.Circuit.compilePolicy_empty_total
#print axioms IRComparison.Circuit.symbolic_compile_total
#print axioms IRComparison.HybridIR.WordValue.weaken
#print axioms IRComparison.HybridIR.WordRead.weaken
#print axioms IRComparison.HybridIR.WordChannel.capture
#print axioms IRComparison.ChannelScope.value_word
#print axioms IRComparison.ChannelScope.read_word
#print axioms IRComparison.ChannelCommandBridge.command_word
#print axioms IRComparison.Circuit.ChannelLower.lower_dataWords
#print axioms IRComparison.Circuit.ChannelCounted.command_word
#print axioms IRComparison.Circuit.ChannelCounted.lower_dataWords
#print axioms IRComparison.Circuit.symbolicInstruction_dataWords
#print axioms IRComparison.Circuit.symbolicInstructions_dataWords
#print axioms IRComparison.Circuit.symbolic_schedule_dataWords
#print axioms IRComparison.Circuit.compile_schedule_dataWords
#print axioms IRComparison.HybridIR.WordValue.affineLocal
#print axioms IRComparison.HybridIR.WordRead.affineLocal
#print axioms IRComparison.HybridIR.WordCommand.affineLocal
#print axioms IRComparison.HybridWord.Expr.lower_word
#print axioms IRComparison.HybridWord.Cmd.lower_word
#print axioms IRComparison.Circuit.WordRanges.value_word
#print axioms IRComparison.Circuit.WordRanges.read_word
#print axioms IRComparison.Circuit.WordRanges.lower_affine
#print axioms IRComparison.Circuit.CommandWordRanges.command_dataWords
#print axioms IRComparison.Circuit.CommandWordRanges.source_dataWords
#print axioms IRComparison.Circuit.Frame.refine_within
#print axioms IRComparison.Circuit.Frame.widen_get_below
#print axioms IRComparison.Circuit.Frame.refine_counter_below
#print axioms IRComparison.Circuit.Frame.refine_increment_inside
#print axioms IRComparison.Circuit.transfer_counter_increment
#print axioms IRComparison.Circuit.Action.transfer_preserves_below
#print axioms IRComparison.Circuit.range_nonempty
#print axioms IRComparison.Circuit.range_mono
#print axioms IRComparison.Circuit.Expr.range_agrees
#print axioms IRComparison.Circuit.transfer_wire_inside
#print axioms IRComparison.Circuit.WireAllocation.Extends.get
#print axioms IRComparison.Circuit.WireAllocation.command
#print axioms IRComparison.Circuit.WireAllocation.channelLower
#print axioms IRComparison.Circuit.WireAllocation.scheduled
#print axioms IRComparison.Circuit.WordRanges.lower
#print axioms IRComparison.Circuit.WordRanges.wire_of_within
#print axioms IRComparison.Circuit.WordRanges.transfer_store
#print axioms IRComparison.Circuit.WordRanges.transfer_assign
#print axioms IRComparison.Circuit.Interval.widenBudget_lt
#print axioms IRComparison.Circuit.Frame.widen_merge_inside
#print axioms IRComparison.Circuit.Frame.widenBudget_lt
#print axioms IRComparison.Circuit.InferenceProgress.joinIncoming_progress
#print axioms IRComparison.Circuit.InferenceProgress.enqueue_complete
#print axioms IRComparison.Circuit.InferenceProgress.inferWorklist_complete
#print axioms IRComparison.Circuit.InferenceProgress.standard_budget
#print axioms IRComparison.Circuit.InferenceProgress.initialized_complete
#print axioms IRComparison.Circuit.inferInvariant_complete
#print axioms IRComparison.Circuit.Pipelining.inferClockInvariant_complete
#print axioms IRComparison.Circuit.BuildInvariant.Rules.command
#print axioms IRComparison.Circuit.BuildInvariant.Rules.channelLower
#print axioms IRComparison.Circuit.BuildInvariant.Rules.schedule
#print axioms IRComparison.Circuit.RangeScoped.exprRange_extend
#print axioms IRComparison.Circuit.capture_range
#print axioms IRComparison.Circuit.transfer_capture
#print axioms IRComparison.Circuit.ScheduleRange.layout
#print axioms IRComparison.Circuit.LayoutRanges.closed
#print axioms IRComparison.Circuit.ScheduleRange.inferInvariant
#print axioms IRComparison.Circuit.Action.transfer_preserves_wire
#print axioms IRComparison.Circuit.ScheduleRange.withCounters
#print axioms IRComparison.Circuit.RangeSafe.counterLoop
#print axioms IRComparison.Circuit.RangeSafe.capturedLoop
#print axioms IRComparison.Circuit.ChannelLower.reserve_ranges
#print axioms IRComparison.Circuit.ChannelLower.lower_ranges
#print axioms IRComparison.Circuit.ChannelCounted.lower_ranges
#print axioms IRComparison.Circuit.symbolicInstruction_ranges
#print axioms IRComparison.Circuit.symbolicInstructions_ranges
#print axioms IRComparison.Circuit.symbolic_schedule_ranges
#print axioms IRComparison.Circuit.compile_schedule_ranges
#print axioms IRComparison.Circuit.compile_schedule_inference
#print axioms IRComparison.Circuit.Pipelining.sequential_named_finishes
#print axioms IRComparison.Circuit.Pipelining.InitialWidths.named
#print axioms IRComparison.Circuit.Pipelining.InitialWidths.scheduled
#print axioms IRComparison.Circuit.Pipelining.InitialWidths.scheduled_legacy
#print axioms IRComparison.Circuit.Pipelining.InitialWidths.Ready.check
#print axioms IRComparison.Circuit.Pipelining.InitialWidths.scheduled_check
#print axioms IRComparison.Circuit.Pipelining.InitialWidths.scheduled_legacy_check
#print axioms IRComparison.Circuit.Pipelining.ClockGraph.inventory_closed
#print axioms IRComparison.Circuit.Pipelining.checkGraph_succeeds
#print axioms IRComparison.Circuit.Pipelining.structured_generation
#print axioms IRComparison.Circuit.Pipelining.scheduleStructure_safe
#print axioms IRComparison.Circuit.Pipelining.overlapLoops_safe
#print axioms IRComparison.Circuit.Pipelining.ClockTree.assemble_safe
#print axioms IRComparison.Circuit.Pipelining.ClockTree.assemble_targets
#print axioms IRComparison.Circuit.Pipelining.ClockTree.assemble_distinct
#print axioms IRComparison.Circuit.Pipelining.ClockTree.assemble_entry
#print axioms IRComparison.Circuit.Pipelining.structured_safe
#print axioms IRComparison.Circuit.Pipelining.structured_control_checks
#print axioms IRComparison.Circuit.Allocation.schedule_allocated
#print axioms IRComparison.Circuit.Allocation.find_declared
#print axioms IRComparison.Circuit.Allocation.interface_of_extension
#print axioms IRComparison.Circuit.Allocation.scheduled_metadata
#print axioms IRComparison.Circuit.Allocation.MetadataReady.moduleReady
#print axioms IRComparison.Circuit.Pipelining.structured_metadata
#print axioms IRComparison.Circuit.Pipelining.structured_entry
#print axioms IRComparison.FixedHLS.Entry.layout_unique
#print axioms IRComparison.FixedHLS.Entry.generated_metadata
#print axioms IRComparison.FixedHLS.Entry.generated_outputs
#print axioms IRComparison.Circuit.SystemVerilog.Generation.termText_total
#print axioms IRComparison.Circuit.SystemVerilog.Generation.validityText_total
#print axioms IRComparison.Circuit.SystemVerilog.Generation.expression_total
#print axioms IRComparison.Circuit.SystemVerilog.Generation.statementCode_total
#print axioms IRComparison.Circuit.SystemVerilog.Generation.checkModuleArtifact_total
#print axioms IRComparison.Circuit.SystemVerilog.Generation.checkReadOutputs_total
#print axioms IRComparison.Circuit.SystemVerilog.Generation.generateCode_total
#print axioms IRComparison.Circuit.SystemVerilog.Generation.generateModule_total
#print axioms IRComparison.Circuit.SystemVerilog.Generation.emit_total
#print axioms IRComparison.Circuit.SystemVerilog.Generation.combinational_ready
#print axioms IRComparison.Circuit.SystemVerilog.Generation.lowerNode_ready
#print axioms IRComparison.Circuit.SystemVerilog.Generation.emit_of_nodes
#print axioms IRComparison.Circuit.Pipelining.ClockNode.statement_emitReady
#print axioms IRComparison.Circuit.Pipelining.generateGraph_succeeds
#print axioms IRComparison.Circuit.Pipelining.generateGraphModule_succeeds
#print axioms IRComparison.DependencyClosure.complete
#print axioms IRComparison.WordFrontend.dependencies_complete
#print axioms IRComparison.FixedMemory.affine_read_arrays
#print axioms IRComparison.FixedMemory.affine_command_arrays
#print axioms IRComparison.FixedMemory.expr_lower_declared
#print axioms IRComparison.FixedMemory.lower_declared
#print axioms IRComparison.FixedMemory.lookup_mem
#print axioms IRComparison.FixedHLS.Entry.declaration_in_layout
#print axioms IRComparison.FixedHLS.Entry.anchor_in_layout
#print axioms IRComparison.FixedHLS.Entry.lower_arrays_in_layout
#print axioms IRComparison.FixedHLS.Entry.outputs_safe
#print axioms IRComparison.HybridUnifiedPipeline.compile_total
#print axioms IRComparison.HybridWord.compileProgram_total
#print axioms IRComparison.WordFrontendFacts.letValue
#print axioms IRComparison.WordFrontendFacts.letState
#print axioms IRComparison.WordLoopFacts.letBinding
#print axioms IRComparison.FixedMemoryExamples.sparseHLS.correct
#print axioms IRComparison.FixedMemoryExamples.scalarHLS.correct
#print axioms IRComparison.FixedMemoryExamples.emptyHLS.correct
#print axioms IRComparison.FixedMemoryExamples.capturedHLS.correct
#print axioms IRComparison.FixedMemoryExamples.capturedLoopHLS.correct
#print axioms IRComparison.HybridWord.State.encode_writeNat
#print axioms IRComparison.WordFrontendFacts.copy
#print axioms IRComparison.FixedMemory.declared_copy
#print axioms IRComparison.FixedMemory.write_sizes
#print axioms IRComparison.FixedMemory.writeNat_sizes
#print axioms IRComparison.FixedMemory.fold_sizes
#print axioms IRComparison.FixedMemory.copy_sizes
#print axioms IRComparison.FixedMemory.copy_prefix
#print axioms IRComparison.FixedMemory.copy_complete
#print axioms IRComparison.FixedMemory.eval_sizes
#print axioms IRComparison.FixedHLS.Entry.compile_correct
#print axioms IRComparison.FixedHLS.Entry.preserves_sizes
#print axioms IRComparison.FixedMemoryExamples.independentHLS.correct
#print axioms IRComparison.FixedMemoryExamples.repeatedHLS.correct
#print axioms IRComparison.FixedMemoryExamples.swapHLS.correct
#print axioms IRComparison.FixedMemoryExamples.nestedHLS.correct
#print axioms IRComparison.FixedMemoryExamples.selfHLS.correct
#print axioms IRComparison.FixedMemoryExamples.longHLS.correct
#print axioms IRComparison.FixedMemoryExamples.shortHLS.correct
#print axioms IRComparison.HybridWord.rangeCount_positive
#print axioms IRComparison.HybridWord.rangeCount_negative
#print axioms IRComparison.HybridWord.range_length
#print axioms IRComparison.HybridIR.replaceLocal_get
#print axioms IRComparison.HybridIR.Value.affineLocal_correct
#print axioms IRComparison.HybridIR.ReadCode.affineLocal_correct
#print axioms IRComparison.HybridIR.MemoryCmd.affineLocal_correct
#print axioms IRComparison.WordLoopFacts.forStatic
#print axioms IRComparison.CertifiedHLS.ProgramEntry.compile_correct
#print axioms IRComparison.LeanTyped.numeral_value
#print axioms IRComparison.WholeProgramExamples.filterHLS.correct
#print axioms IRComparison.WholeProgramExamples.nestedHLS.correct
#print axioms IRComparison.WholeProgramExamples.ascendingHLS.correct
#print axioms IRComparison.WholeProgramExamples.descendingHLS.correct
#print axioms IRComparison.WholeProgramExamples.emptyHLS.correct
#print axioms IRComparison.WholeProgramExamples.wrappingHLS.correct
#print axioms IRComparison.WholeProgramExamples.failingHLS.correct
#print axioms IRComparison.WholeProgramExamples.largeHLS.correct
#print axioms IRComparison.WholeProgramExamples.smallHLS.correct
#print axioms IRComparison.Relational.for_with_refill_rule
#print axioms IRComparison.Relational.result_eq
#print axioms IRComparison.HybridSymbolicBody.Compiled.translation
#print axioms IRComparison.HybridSymbolicLoop.Plan.initial_rule
#print axioms IRComparison.HybridSymbolicLoop.Plan.body_rule
#print axioms IRComparison.HybridSymbolicLoop.Plan.refill_rule
#print axioms IRComparison.HybridSymbolicLoop.Plan.loop_rule
#print axioms IRComparison.ChannelCommandBridge.command_correct
#print axioms IRComparison.Circuit.ChannelCounted.piece_correct
#print axioms IRComparison.Circuit.ChannelCounted.round_correct
#print axioms IRComparison.Circuit.ChannelCounted.fold_correct
#print axioms IRComparison.Circuit.ChannelCounted.command_correct
#print axioms IRComparison.Circuit.ChannelCounted.bounded_command
#print axioms IRComparison.Circuit.ChannelCounted.lower_reference
#print axioms IRComparison.Circuit.ChannelLower.bounded_congr
#print axioms IRComparison.Circuit.ChannelLower.resources
#print axioms IRComparison.Circuit.ChannelLower.frame_above
#print axioms IRComparison.Circuit.CountedBackend.named
#print axioms IRComparison.Circuit.prepareSymbolicWith_contract
#print axioms IRComparison.Circuit.symbolicInstructions_correct_with
#print axioms IRComparison.Circuit.symbolic_pipeline_schedule_with
#print axioms IRComparison.Circuit.Pipelining.unified_schedule_correct_with
#print axioms IRComparison.Circuit.Pipelining.optimized_schedule_correct_with
#print axioms IRComparison.ChannelScope.value_correct
#print axioms IRComparison.ChannelScope.read_correct
#print axioms IRComparison.ChannelScope.body_correct
#print axioms IRComparison.ChannelBuffers.capture_correct
#print axioms IRComparison.ChannelBuffers.pop_correct
#print axioms IRComparison.ChannelBuffers.take_correct
#print axioms IRComparison.ChannelWindow.Load.correct
#print axioms IRComparison.ChannelWindow.loads_correct
#print axioms IRComparison.ChannelWindow.put_held
#print axioms IRComparison.ChannelWindow.capture_held
#print axioms IRComparison.Circuit.ChannelCounted.command_budget
#print axioms IRComparison.HybridIR.ChannelCmd.ofMemory_correct
#print axioms IRComparison.Circuit.ChannelLower.lower_correct
#print axioms IRComparison.Circuit.ChannelLower.sendBudget_sound
#print axioms IRComparison.Circuit.Pipelining.ClockTree.assemble_payload_finishes
#print axioms IRComparison.Circuit.Pipelining.rotate_correct
#print axioms IRComparison.Circuit.Pipelining.overlapLoop_correct
#print axioms IRComparison.Circuit.Pipelining.overlapLoops_correct
#print axioms IRComparison.Circuit.Pipelining.scheduleStructure_correct
#print axioms IRComparison.Circuit.Pipelining.ClockTree.layout_correct
#print axioms IRComparison.Circuit.Pipelining.ClockTree.assemble_finishes
#print axioms IRComparison.Circuit.Pipelining.scheduleStructure_finishes
#print axioms IRComparison.Circuit.Pipelining.transferActions_sound
#print axioms IRComparison.Circuit.Pipelining.ClockNode.transfer_sound
#print axioms IRComparison.Circuit.Pipelining.clock_tick_table
#print axioms IRComparison.Circuit.Pipelining.clockGraph_run_bound
#print axioms IRComparison.Circuit.Pipelining.clockGraph_rtl_run
#print axioms IRComparison.Circuit.Pipelining.structured_rtl_finishes
#print axioms IRComparison.Circuit.Pipelining.checkGraph_sound
#print axioms IRComparison.Circuit.Pipelining.graphModule_text
#print axioms IRComparison.Circuit.Pipelining.physical_graph_tick
#print axioms IRComparison.Circuit.Pipelining.physical_graph_run
#print axioms IRComparison.Circuit.Pipelining.generated_graph_run
#print axioms IRComparison.Circuit.Pipelining.compileStructured_correct

#print axioms IRComparison.Circuit.Pipelining.Independent.ordered
#print axioms IRComparison.Circuit.Pipelining.independent_bundle_safe
#print axioms IRComparison.Circuit.Pipelining.ordered_bundle_rhl
#print axioms IRComparison.Circuit.Pipelining.ordered_pair_rhl

#print axioms IRComparison.PipelineWorkloads.histogramCode.wordBody_correct
#print axioms IRComparison.PipelineWorkloads.compactCode.wordBody_correct

#print axioms IRComparison.Circuit.expanded_pipeline_schedule
#print axioms IRComparison.Circuit.compact_pipeline_schedule
#print axioms IRComparison.Circuit.Pipelining.constantExpr_correct
#print axioms IRComparison.Circuit.Pipelining.linearize_correct
#print axioms IRComparison.Circuit.Pipelining.optimized_schedule_correct
#print axioms IRComparison.Circuit.Pipelining.compileOptimizedScheduled_facts
#print axioms IRComparison.Circuit.Pipelining.optimized_batches_correct
#print axioms IRComparison.Circuit.Pipelining.compileOptimizedScheduled_correct

#print axioms IRComparison.Circuit.Pipelining.clock_rename
#print axioms IRComparison.Circuit.Pipelining.reuse_correct
#print axioms IRComparison.Circuit.Pipelining.allocated_word_correct
#print axioms IRComparison.Circuit.Pipelining.batch_width_preserved
#print axioms IRComparison.Circuit.Pipelining.lowerClock_bit_correct
#print axioms IRComparison.Circuit.Pipelining.compiled_rtl_correct
#print axioms IRComparison.Circuit.Pipelining.pipelineWord_rtl_correct
#print axioms IRComparison.Circuit.Pipelining.realize_correct
#print axioms IRComparison.Circuit.Pipelining.batchModule_text
#print axioms IRComparison.Circuit.Pipelining.lowerClock_frame
#print axioms IRComparison.Circuit.Pipelining.generateBatches_total
#print axioms IRComparison.Circuit.Pipelining.physical_batch_tick
#print axioms IRComparison.Circuit.Pipelining.physical_batches_run
#print axioms IRComparison.Circuit.Pipelining.batchRun_bound
#print axioms IRComparison.Circuit.Pipelining.checkBatch_sound
#print axioms IRComparison.Circuit.Pipelining.generated_batch_run
#print axioms IRComparison.Circuit.Pipelining.realized_rtl_correct
#print axioms IRComparison.Circuit.Pipelining.pipelineWord_text_correct
#print axioms IRComparison.Circuit.Pipelining.compileWordCircuit_correct

#print axioms IRComparison.Circuit.Pipelining.rhl_swap
#print axioms IRComparison.Circuit.Pipelining.reorder_sound
#print axioms IRComparison.Circuit.Pipelining.prepare_correct
#print axioms IRComparison.Circuit.Pipelining.independent_sound
#print axioms IRComparison.Circuit.Pipelining.clock_correct
#print axioms IRComparison.Circuit.Pipelining.compile_correct
#print axioms IRComparison.Circuit.Pipelining.compile_rhl
#print axioms IRComparison.Circuit.Pipelining.Loop.pipeline_rhl
#print axioms IRComparison.Circuit.Pipelining.related_tick
#print axioms IRComparison.Circuit.Pipelining.pipeline_finishes
#print axioms IRComparison.Circuit.Pipelining.transform_correct
#print axioms IRComparison.Circuit.Pipelining.materialize_correct
#print axioms IRComparison.Circuit.Pipelining.pipelineCommands_correct
#print axioms IRComparison.Circuit.Pipelining.pipelineWord_correct
#print axioms IRComparison.Circuit.Pipelining.pipelineWord_finishes
#print axioms IRComparison.PipeliningExamples.filterCode.wordBody_correct
#print axioms IRComparison.PipeliningExamples.gatherCode.wordBody_correct

#print axioms IRComparison.ClockedComponent.tick_wellFormed
#print axioms IRComparison.ClockedComponent.tick_conservation
#print axioms IRComparison.ClockedComponent.run_conservation
#print axioms IRComparison.ClockedComponent.results_correct
#print axioms IRComparison.ClockedComponent.drained_trace_correct
#print axioms IRComparison.ClockedComponent.request_finishes
#print axioms IRComparison.ClockedComponent.response_stall
#print axioms IRComparison.ClockedComponent.retire_once
#print axioms IRComparison.ClockedOperation.finishes
#print axioms IRComparison.ClockedOperation.offer_preserves
#print axioms IRComparison.WordComponent.Op.lower_correct
#print axioms IRComparison.WordComponent.finishes_mixed
#print axioms IRComparison.WordComponent.controlled_finishes

#print axioms IRComparison.Imperative.transform_correct
#print axioms IRComparison.Functional.transform_correct
#print axioms IRComparison.lowerBody_correct
#print axioms IRComparison.lowerProgram_correct
#print axioms IRComparison.optimized_agree
#print axioms IRComparison.Examples.forward_example
#print axioms IRComparison.Examples.reverse_example
#print axioms IRComparison.Source.extract_correct
#print axioms IRComparison.Frontend.compileImperative_correct
#print axioms IRComparison.Frontend.compileFunctional_correct
#print axioms IRComparison.Frontend.compilers_agree
#print axioms IRComparison.NativeLoop.run_eq_iterate
#print axioms IRComparison.NativeLoop.imperative_correct
#print axioms IRComparison.NativeLoop.functional_correct
#print axioms IRComparison.NativeBody.compileImperative_correct
#print axioms IRComparison.NativeBody.compileFunctional_correct
#print axioms IRComparison.NativeExamples.imperative_correct
#print axioms IRComparison.NativeExamples.functional_correct
#print axioms IRComparison.LeanScalar.compile_correct
#print axioms IRComparison.LeanScalar.environment_cons
#print axioms IRComparison.LeanScalar.compileFunction_correct
#print axioms IRComparison.LeanScalar.FunctionArtifact.state_independent
#print axioms IRComparison.LeanScalar.FunctionArtifact.imperative_correct
#print axioms IRComparison.LeanScalar.FunctionArtifact.functional_correct

#print axioms IRComparison.LeanDefinition.Artifact.application
#print axioms IRComparison.LeanDefinition.Artifact.declaration_unique
#print axioms IRComparison.LeanTyped.Represents.instantiate
#print axioms IRComparison.LeanTyped.typed_beta
#print axioms IRComparison.LeanTyped.typed_let

#print axioms IRComparison.LeanTyped.DefinitionView.unfold
#print axioms IRComparison.LeanTyped.DefinitionView.apply_three
#print axioms IRComparison.LeanTyped.DefinitionView.source
#print axioms IRComparison.LeanTyped.DefinitionView.type_shape

#print axioms IRComparison.LeanTyped.intLambdas_congr
#print axioms IRComparison.LeanTyped.applications_congr
#print axioms IRComparison.LeanTyped.applications_beta
#print axioms IRComparison.LeanTyped.DefinitionView.apply_and_instantiate
#print axioms IRComparison.LeanTyped.DefinitionView.extend_ordered_from_body
#print axioms IRComparison.LeanTyped.Standard.select

#print axioms IRComparison.HybridRoutingVC.accept_correct
#print axioms IRComparison.HybridSymbolicGlobal.Plan.correct
#print axioms IRComparison.HybridSymbolicGlobal.Program.correct
#print axioms IRComparison.Circuit.symbolicReference_correct
#print axioms IRComparison.Circuit.symbolicReference_execute
#print axioms IRComparison.Circuit.counted_full_reference
#print axioms IRComparison.Circuit.prepareSymbolic_contract
#print axioms IRComparison.Circuit.symbolicInstructions_correct
#print axioms IRComparison.Circuit.symbolic_pipeline_schedule

-- Stop the audit on an unexpected assumption, including a dependency's sorry.
open Lean Elab Command in
run_cmd do
  let audited := [
    ``IRComparison.AutomaticStages.indexExpr_correct,
    ``IRComparison.AutomaticStages.indexBody_correct,
    ``IRComparison.AutomaticStages.pieces_correct,
    ``IRComparison.AutomaticStages.pieces_declared,
    ``IRComparison.AutomaticStages.entry_closed,
    ``IRComparison.FixedHLS.Entry.staged_correct,
    ``IRComparison.FixedHLS.Entry.staged_closed,
    ``IRComparison.FixedHLS.Entry.artifact_correct,
    ``IRComparison.WordFrontend.FunctionSyntax.Syntax.valueCurrentPaired,
    ``IRComparison.WordFrontend.FunctionSyntax.Syntax.yieldPaired,
    ``IRComparison.WordFrontend.FunctionSyntax.Syntax.sequencePaired,
    ``IRComparison.WordFrontend.FunctionSyntax.Syntax.stepSequencePaired,
    ``IRComparison.WordFrontend.FunctionSyntax.Syntax.forStaticPaired,
    ``IRComparison.WordFrontend.FunctionSyntax.Syntax.forRangePaired,
    ``IRComparison.WordFrontend.FixedSequenceCompleteness.InputConditions.forRange,
    ``IRComparison.FrontendGenerationConditions.helperLoopContinuationHLS.wordBody_correct,
    ``IRComparison.FrontendGenerationConditions.naturalForIdentityHLS.wordBody_correct,
    ``IRComparison.FrontendGenerationConditions.naturalFoldIdentityHLS.wordBody_correct,

    ``IRComparison.WordFrontend.FunctionSyntax.sourceCheckedBindTyping,
    ``IRComparison.WordFrontend.FunctionSyntax.sourceCheckedLetTyping,
    ``IRComparison.WordFrontend.FunctionSyntax.sourceReadBindTyping,
    ``IRComparison.WordFrontend.FunctionSyntax.Syntax.functionLetFromLambdaPaired,
    ``IRComparison.WordFrontend.FunctionSyntax.Syntax.valueAssignPaired,
    ``IRComparison.WordFrontend.FunctionSyntax.Syntax.stateLetPaired,
    ``IRComparison.WordFrontend.FunctionSyntax.Syntax.bindValuePaired,
    ``IRComparison.WordFrontend.FunctionSyntax.Syntax.stepBindValuePaired,
    ``IRComparison.WordFrontend.FunctionSyntax.Syntax.booleanBranchPaired,
    ``IRComparison.FrontendGenerationConditions.helperReadContinuationHLS.wordBody_correct,
    ``IRComparison.WordFrontend.FixedFunctionCompleteness.sourceArgumentCases,
    ``IRComparison.WordFrontend.FunctionSyntax.parameterLayout_state,
    ``IRComparison.WordFrontend.FunctionSyntax.parameterLayout_scalar,
    ``IRComparison.WordFrontend.FunctionSyntax.parameterLayout_open,
    ``IRComparison.WordFrontend.FunctionSyntax.parameterLayout_scope,
    ``IRComparison.WordFrontend.FunctionSyntax.argumentTypes_lift,
    ``IRComparison.WordFrontend.StructuralBody.ArgumentBindings.parameterLayout,
    ``IRComparison.WordFrontend.FunctionSyntax.parameterShapes_prefix,
    ``IRComparison.WordFrontend.FunctionSyntax.parameterLayout_scalars,
    ``IRComparison.WordFrontend.FunctionSyntax.argumentTypes_of_representations,
    ``IRComparison.WordFrontend.FixedFunctionCompleteness.retainedArgumentsFromBodyFamily,
    ``IRComparison.FrontendGenerationConditions.retainedMixedReadHLS.wordBody_correct,
    ``IRComparison.WordFrontend.LexicalScalarCode.Evidence.notState,
    ``IRComparison.WordFrontend.FunctionSyntax.openArguments_length,
    ``IRComparison.WordFrontend.FunctionSyntax.closureSubstitution_open_next,
    ``IRComparison.WordFrontend.FunctionSyntax.lambdaSource_opened,
    ``IRComparison.WordFrontend.FunctionSyntax.BindingValue.openedArguments,
    ``IRComparison.WordFrontend.FunctionSyntax.Syntax.retainedCallFromBodyTypes,
    ``IRComparison.WordFrontend.StructuralBody.ArgumentBindings.scalarLayout,
    ``IRComparison.WordFrontend.FixedFunctionCompleteness.retainedScalarArgumentsFromOpenBody,
    ``IRComparison.WordFrontend.FixedReadSourceCompleteness.Conditions.word,
    ``IRComparison.WordFrontend.FixedSequenceCompleteness.InputConditions.readBind,
    ``IRComparison.FrontendGenerationConditions.retainedTwoOpenBindingsHLS.wordBody_correct,
    ``IRComparison.FrontendGenerationConditions.retainedOpenStateHelperHLS.wordBody_correct,
    ``IRComparison.WordFrontend.LexicalScalarSyntax.expand_liftCache,
    ``IRComparison.WordFrontend.LexicalScalarSyntax.Form.liftScalar,
    ``IRComparison.WordFrontend.StructuralBody.ArgumentBindings.fromSyntax,
    ``IRComparison.WordFrontend.StructuralBody.ArgumentBindings.endpointScope,
    ``IRComparison.WordFrontend.FixedFunctionCompleteness.retainedCallFromSourceArguments,
    ``IRComparison.WordFrontend.FixedFunctionCompleteness.retainedCallFromSourceScope,
    ``IRComparison.WordFrontend.FixedFunctionCompleteness.retainedScalarCallFromOpenBody,
    ``IRComparison.WordFrontend.FunctionSyntax.BindingValue.openedScalar,
    ``IRComparison.WordFrontend.FunctionSyntax.closureSubstitution_open_scalar,
    ``IRComparison.WordFrontend.FixedFunctionCompleteness.generatesRetainedSyntaxInstalled,
    ``IRComparison.WordFrontend.FixedFunctionCompleteness.retainedScalarCallFromSyntax,
    ``IRComparison.WordFrontend.FunctionSyntax.Syntax.retainedCallFromLambdaBodies,
    ``IRComparison.WordFrontend.FunctionSyntax.Syntax.retainedCallFromSourceBodies,
    ``IRComparison.WordFrontend.StructuralBody.ArgumentBindings.Syntax.install,
    ``IRComparison.WordFrontend.StructuralBody.ArgumentBindings.syntax,
    ``IRComparison.WordFrontend.StructuralBody.ArgumentBindings.independent,
    ``IRComparison.WordFrontend.FunctionSyntax.application_spine_scoped,
    ``IRComparison.WordFrontend.FunctionSyntax.lambdaSource_apply_scoped,
    ``IRComparison.WordFrontend.FunctionSyntax.BindingValue.retained_call_from_body,
    ``IRComparison.WordFrontend.StructuralBody.retargetRetainedPiece_typed_call,
    ``IRComparison.WordFrontend.FunctionSyntax.step_helper_retained_retarget_complete,
    ``IRComparison.WordFrontend.StructuralSyntax.helper_retained_retarget_complete,
    ``IRComparison.WordFrontend.Arithmetic.AliasSetup.covers_source_ordinary,
    ``IRComparison.WordFrontend.RetainedConversion.Prefix.length_le,
    ``IRComparison.LeanStructuralConversion.ordinary_of_prove,
    ``IRComparison.LeanStructuralConversion.conversion_of_retained,
    ``IRComparison.LeanStructuralConversion.conversion_of_ordinary,
    ``IRComparison.WordFrontend.LexicalScalarCode.expand_open,
    ``IRComparison.WordFrontend.LexicalScalarCode.ValuesTyped.open,
    ``IRComparison.WordFrontend.LexicalScalarCode.Source.bindingEvidenceOfEvidence,
    ``IRComparison.WordFrontend.LexicalScalarCode.Source.bindingEvidenceOpen,
    ``IRComparison.WordFrontend.LexicalScalarCode.Source.letOpen,
    ``IRComparison.WordFrontend.LexicalScalarCode.Source.betaOpen,
    ``IRComparison.WordFrontend.FixedSequenceCompleteness.Source.facts,
    ``IRComparison.WordFrontend.FixedFunctionCompleteness.Source.facts,
    ``IRComparison.FrontendLexicalGeneration.retainedCaptureHLS.wordBody_correct,
    ``IRComparison.WordFrontend.ScalarEnvironment.Unbound.lookup_none,
    ``IRComparison.WordFrontend.ScalarConversion.let_visit_complete_code,
    ``IRComparison.WordFrontend.ScalarConversion.beta_visit_complete_code,
    ``IRComparison.WordFrontend.LexicalScalarCode.Source.computation,
    ``IRComparison.WordFrontend.LexicalScalarCode.Source.complete,
    ``IRComparison.WordFrontend.LexicalScalarCode.Source.evidence,
    ``IRComparison.LeanStructuralConversion.prove_reduction_right_complete_types,
    ``IRComparison.WordFrontend.Arithmetic.AliasSetup.scalar_beta_checked_domain_types,
    ``IRComparison.WordFrontend.LexicalScalarCode.expand_cons,
    ``IRComparison.WordFrontend.LexicalScalarCode.Source.bindingEvidence,
    ``IRComparison.WordFrontend.LexicalScalarCode.Source.letInferred,
    ``IRComparison.WordFrontend.LexicalScalarCode.Source.betaInferred,
    ``IRComparison.WordFrontend.LexicalScalarCode.Evidence.variable,
    ``IRComparison.WordFrontend.LexicalScalarCode.Evidence.lift,
    ``IRComparison.WordFrontend.LexicalScalarCode.ScopeTyped.lift,
    ``IRComparison.WordFrontend.LexicalScalarCode.ScopeTyped.nextWord,
    ``IRComparison.WordFrontend.LexicalScalarCode.ScopeTyped.initial,
    ``IRComparison.WordFrontend.LexicalScalarCode.ScopeTyped.nextState,
    ``IRComparison.WordFrontend.LexicalScalarCode.ScopeTyped.forStatic,
    ``IRComparison.WordFrontend.LexicalScalarCode.Evidence.naturalIndex,
    ``IRComparison.WordFrontend.LexicalScalarCode.ScopeTyped.withLocal,
    ``IRComparison.WordFrontend.LexicalScalarCode.ScopeTyped.naturalLoop,
    ``IRComparison.WordFrontend.LexicalScalarCode.Source.binaryInferred,
    ``IRComparison.WordFrontend.LexicalScalarCode.Source.negInferred,
    ``IRComparison.WordFrontend.LexicalScalarCode.Source.selectInferred,
    ``IRComparison.WordFrontend.FixedScalarCompleteness.Source.lexical,
    ``IRComparison.WordFrontend.FixedScalarCompleteness.Scoped.asLexical,
    ``IRComparison.WordFrontend.FixedScalarCompleteness.Scoped.evidence,
    ``IRComparison.WordFrontend.FixedFunctionCompleteness.Source.branchInferred,
    ``IRComparison.WordFrontend.FixedFunctionCompleteness.Source.stepBranchInferred,
    ``IRComparison.WordFrontend.StandardLibrary.closed,
    ``IRComparison.WordFrontend.LexicalScalarCode.Source.install,
    ``IRComparison.WordFrontend.LexicalScalarCode.Source.parse_complete,
    ``IRComparison.WordFrontend.FixedScalarCompleteness.Scoped.declared,
    ``IRComparison.WordFrontend.FixedScalarCompleteness.Scoped.computation,
    ``IRComparison.WordFrontend.FixedScalarCompleteness.Scoped.complete,
    ``IRComparison.WordFrontend.FixedScalarCompleteness.Scoped.install,
    ``IRComparison.WordFrontend.FixedReadSourceCompleteness.Source.install,
    ``IRComparison.WordFrontend.FixedSequenceCompleteness.Source.install,
    ``IRComparison.WordFrontend.Certificate.For.Bound.binary,
    ``IRComparison.WordFrontend.Certificate.For.BoundSignatures.binary_header_typed,
    ``IRComparison.WordFrontend.AnnotatedLiteral.visit_complete,
    ``IRComparison.WordFrontend.AnnotatedLiteral.fact_typed,
    ``IRComparison.WordFrontend.AnnotatedLiteral.typed,
    ``IRComparison.LeanStructuralConversion.prove_application_or_same_complete,
    ``IRComparison.WordFrontend.Arithmetic.AliasSetup.basic_values_none_of_types,
    ``IRComparison.WordFrontend.Arithmetic.AliasSetup.heterogeneous_proved,
    ``IRComparison.WordFrontend.AnnotatedBinary.dictionary_typed,
    ``IRComparison.WordFrontend.AnnotatedBinary.header_typed,
    ``IRComparison.WordFrontend.AnnotatedBinary.value_typed,
    ``IRComparison.WordFrontend.AnnotatedBinary.dictionary_proved,
    ``IRComparison.WordFrontend.AnnotatedLiteral.annotation_typed,
    ``IRComparison.WordFrontend.AnnotatedCondition.dictionary_proved,
    ``IRComparison.WordFrontend.AnnotatedCondition.header_proved,
    ``IRComparison.WordFrontend.AnnotatedCondition.literal_proved,
    ``IRComparison.WordFrontend.AnnotatedCondition.test_proved,
    ``IRComparison.WordFrontend.AnnotatedCondition.condition_proved,
    ``IRComparison.WordFrontend.AnnotatedCondition.decidable_proved,
    ``IRComparison.WordFrontend.AnnotatedCondition.Casts.covered,
    ``IRComparison.WordFrontend.AnnotatedCondition.choice_proved,
    ``IRComparison.WordFrontend.Certificate.Branch.ite_checked_typed,
    ``IRComparison.WordFrontend.AnnotatedCondition.choice_with_prefix_proved,
    ``IRComparison.WordFrontend.AnnotatedCondition.scalar_choice_proved,
    ``IRComparison.WordFrontend.AnnotatedCondition.scalar_choice_typed,
    ``IRComparison.WordFrontend.AnnotatedCondition.scalarSource_typed,
    ``IRComparison.WordFrontend.ScalarConversion.select_expected_proved,
    ``IRComparison.WordFrontend.AnnotatedSelect.finish_complete,
    ``IRComparison.WordFrontend.AnnotatedSelect.visit_complete_code,
    ``IRComparison.WordFrontend.AnnotatedCondition.choice_equality_proved,
    ``IRComparison.WordFrontend.AnnotatedCondition.ChoiceConditions.conversion,
    ``IRComparison.WordFrontend.AnnotatedBranch.finish_complete,
    ``IRComparison.WordFrontend.AnnotatedBranch.visit_complete_code,
    ``IRComparison.WordFrontend.AnnotatedBranch.Loop.finish_complete,
    ``IRComparison.WordFrontend.AnnotatedBranch.Loop.visit_complete_code,
    ``IRComparison.WordFrontend.AnnotatedNeg.header_typed,
    ``IRComparison.WordFrontend.AnnotatedNeg.header_proved,
    ``IRComparison.WordFrontend.AnnotatedNeg.value_proved,
    ``IRComparison.WordFrontend.ScalarConversion.expected_value_proved,
    ``IRComparison.WordFrontend.ScalarConversion.neg_expected_proved,
    ``IRComparison.WordFrontend.ScalarConversion.annotated_neg_finish,
    ``IRComparison.WordFrontend.AnnotatedNeg.visit_complete_code,
    ``IRComparison.WordFrontend.AnnotatedBinary.header_proved,
    ``IRComparison.WordFrontend.AnnotatedBinary.value_proved,
    ``IRComparison.WordFrontend.ScalarConversion.binary_expected_proved,
    ``IRComparison.WordFrontend.ScalarConversion.annotated_binary_finish,
    ``IRComparison.WordFrontend.AnnotatedBinary.visit_complete_code,
    ``IRComparison.WordFrontend.FixedFunctionCompleteness.closure_single,
    ``IRComparison.WordFrontend.FunctionSyntax.closureReference_append,
    ``IRComparison.WordFrontend.FunctionSyntax.closureSubstitution_append,
    ``IRComparison.WordFrontend.FunctionSyntax.closureSubstitution_append_represents,
    ``IRComparison.WordFrontend.FunctionSyntax.lambdaSource_apply_represents,
    ``IRComparison.WordFrontend.FunctionSyntax.closureCall_representations,
    ``IRComparison.WordFrontend.FunctionSyntax.BindingValue.application_parts,
    ``IRComparison.LeanTypeReduction.step_apply_checked_complete,
    ``IRComparison.LeanTypeReduction.applyReduced_typed,
    ``IRComparison.LeanTypeReduction.checked_spine_typed,
    ``IRComparison.LeanTypeReduction.exact_spine_prefix_typed,
    ``IRComparison.LeanTypeReduction.step_checked_spine_complete,
    ``IRComparison.LeanTypeReduction.ArgumentsCasts.application_typed,
    ``IRComparison.WordFrontend.Arithmetic.ValueForm.checkedArguments,
    ``IRComparison.WordFrontend.Arithmetic.AliasSetup.helper_checked_proved,
    ``IRComparison.WordFrontend.Certificate.For.helper_checked_equality_conversion,
    ``IRComparison.WordFrontend.LexicalScalarCode.expand_state_scoped,
    ``IRComparison.WordFrontend.ScalarSyntax.Form.lexical,
    ``IRComparison.WordFrontend.LexicalScalarCode.ExternalAt.lift,
    ``IRComparison.WordFrontend.LexicalScalarCode.expand_scoped,
    ``IRComparison.WordFrontend.LexicalScalarCode.Source.independent,
    ``IRComparison.WordFrontend.FixedScalarCompleteness.Scoped.independent,
    ``IRComparison.WordFrontend.FixedReadSourceCompleteness.Source.independent,
    ``IRComparison.WordFrontend.FixedReadSourceCompleteness.constructSource,
    ``IRComparison.WordFrontend.FixedSequenceCompleteness.represented_scoped,
    ``IRComparison.WordFrontend.FixedSequenceCompleteness.reduced_scoped,
    ``IRComparison.WordFrontend.FixedSequenceCompleteness.Source.independent,
    ``IRComparison.WordFrontend.FixedSequenceCompleteness.constructAtomSource,
    ``IRComparison.WordFrontend.FixedSequenceCompleteness.constructSource,
    ``IRComparison.WordFrontend.FixedFunctionCompleteness.Source.independent,
    ``IRComparison.WordFrontend.FixedFunctionCompleteness.constructFunctionSource,
    ``IRComparison.WordFrontend.LexicalScalarCode.expand_scoped_compared,
    ``IRComparison.WordFrontend.LexicalScalarCode.Source.compareLocals,
    ``IRComparison.WordFrontend.FixedSequenceCompleteness.InputConditions.valueAssign,
    ``IRComparison.WordFrontend.FixedSequenceCompleteness.InputConditions.yield,
    ``IRComparison.WordFrontend.FixedSequenceCompleteness.InputConditions.forStatic,
    ``IRComparison.WordFrontend.FunctionSyntax.lambda_prefix_retag,
    ``IRComparison.WordFrontend.FunctionSyntax.lambdaTelescope_typed,
    ``IRComparison.WordFrontend.FunctionSyntax.lambdaPrefixesFromBody,
    ``IRComparison.WordFrontend.FixedFunctionCompleteness.argumentsWithTypesFromSyntax,
    ``IRComparison.WordFrontend.FixedFunctionCompleteness.argumentsWithShapesFromSyntax,
    ``IRComparison.WordFrontend.FixedFunctionCompleteness.argumentsTypedWithShapesFromSyntax,
    ``IRComparison.WordFrontend.ScalarSyntax.Decision.mono,
    ``IRComparison.WordFrontend.ScalarSyntax.Decision.instantiate,
    ``IRComparison.WordFrontend.LexicalScalarCode.Evidence.instantiateExact,
    ``IRComparison.WordFrontend.LexicalScalarSyntax.ValueShape.instantiateExact,
    ``IRComparison.WordFrontend.LexicalScalarSyntax.ValueShape.instantiateSome,
    ``IRComparison.WordFrontend.LexicalScalarSyntax.Form.renameCache,
    ``IRComparison.WordFrontend.LexicalScalarSyntax.Form.closeExact,
    ``IRComparison.WordFrontend.LexicalScalarSyntax.Form.closeOpenExact,
    ``IRComparison.WordFrontend.LexicalScalarSyntax.StaticRegisters.rename,
    ``IRComparison.WordFrontend.LexicalScalarSyntax.Form.bindingFromOpen,
    ``IRComparison.WordFrontend.LexicalScalarSyntax.Form.letFromOpen,
    ``IRComparison.WordFrontend.LexicalScalarSyntax.Form.betaFromOpen,
    ``IRComparison.WordFrontend.ScalarSyntax.ReferenceScope.separated,
    ``IRComparison.WordFrontend.ScalarSyntax.ReferenceScope.initial,
    ``IRComparison.WordFrontend.ScalarSyntax.ReferenceScope.lift,
    ``IRComparison.WordFrontend.ScalarSyntax.ReferenceScope.scalar,
    ``IRComparison.WordFrontend.ScalarSyntax.ReferenceScope.state,
    ``IRComparison.WordFrontend.ScalarSyntax.ReferenceScope.forStatic,
    ``IRComparison.WordFrontend.ScalarSyntax.ReferenceScope.forIn,
    ``IRComparison.WordFrontend.ScalarSyntax.ReferenceScope.fold,
    ``IRComparison.WordFrontend.FunctionSyntax.Syntax.sourceTyping,
    ``IRComparison.WordFrontend.FunctionSyntax.Syntax.helperPrefixes,
    ``IRComparison.WordFrontend.FixedFunctionCompleteness.argumentsFromSyntax,
    ``IRComparison.WordFrontend.FixedFunctionCompleteness.argumentsTypedFromSyntax,
    ``IRComparison.WordFrontend.LexicalScalarCode.Source.stateOnly,
    ``IRComparison.WordFrontend.LexicalScalarSyntax.Form.constructSource,
    ``IRComparison.WordFrontend.LexicalScalarSyntax.expand_cons,
    ``IRComparison.WordFrontend.LexicalScalarSyntax.Form.evidence,
    ``IRComparison.WordFrontend.LexicalScalarSyntax.Form.binaryInferred,
    ``IRComparison.WordFrontend.LexicalScalarSyntax.Form.negInferred,
    ``IRComparison.WordFrontend.LexicalScalarSyntax.Form.selectInferred,
    ``IRComparison.WordFrontend.LexicalScalarSyntax.Form.bindingEvidence,
    ``IRComparison.WordFrontend.LexicalScalarSyntax.Form.letFromTyping,
    ``IRComparison.WordFrontend.LexicalScalarSyntax.Form.betaFromTyping,
    ``IRComparison.WordFrontend.ScalarSyntax.sameTerm_application_variable,
    ``IRComparison.WordFrontend.ScalarSyntax.Separated.initialApplication,
    ``IRComparison.WordFrontend.FixedScalarCompleteness.Scoped.fromSyntax,
    ``IRComparison.WordFrontend.FunctionSyntax.closureSubstitution_at_capture,
    ``IRComparison.WordFrontend.FunctionSyntax.closureSubstitution_shift_empty,
    ``IRComparison.WordFrontend.FunctionSyntax.Scope.coherent_empty,
    ``IRComparison.WordFrontend.FunctionSyntax.Closure.SourceAt.shift,
    ``IRComparison.WordFrontend.FunctionSyntax.BindingValue.sourceAt,
    ``IRComparison.WordFrontend.FunctionSyntax.Scope.Coherent.functionLet,
    ``IRComparison.WordFrontend.FunctionSyntax.Scope.Coherent.under,
    ``IRComparison.WordFrontend.FunctionSyntax.Scope.lookup_parameters,
    ``IRComparison.WordFrontend.FunctionSyntax.Scope.Coherent.applyArguments,
    ``IRComparison.WordFrontend.FunctionSyntax.substitution_applications,
    ``IRComparison.WordFrontend.FunctionSyntax.application_spine,
    ``IRComparison.WordFrontend.FunctionSyntax.BindingValue.call_representations,
    ``IRComparison.WordFrontend.FunctionSyntax.functionType_suffix_closed,
    ``IRComparison.LeanTypeInference.CheckedTyping.install,
    ``IRComparison.WordFrontend.FunctionSyntax.letSubstitution_apply,
    ``IRComparison.WordFrontend.FunctionSyntax.let_representations,
    ``IRComparison.WordFrontend.FunctionSyntax.lambdaSource_typed,
    ``IRComparison.WordFrontend.FunctionSyntax.functionType_typed,
    ``IRComparison.WordFrontend.FunctionSyntax.functionArguments_typed,
    ``IRComparison.WordFrontend.FixedFunctionCompleteness.Source.bodyTyping,
    ``IRComparison.WordFrontend.FixedFunctionCompleteness.Source.stepBodyTyping,
    ``IRComparison.WordFrontend.FixedFunctionCompleteness.Source.functionLetInferred,
    ``IRComparison.WordFrontend.FixedFunctionCompleteness.Source.stepFunctionLetInferred,
    ``IRComparison.WordFrontend.FixedFunctionCompleteness.Source.bodyNotLambda,
    ``IRComparison.WordFrontend.FixedFunctionCompleteness.Source.lambdaTyping,
    ``IRComparison.WordFrontend.FixedFunctionCompleteness.Source.functionLetFromLambda,
    ``IRComparison.WordFrontend.FixedFunctionCompleteness.Source.stepFunctionLetFromLambda,
    ``IRComparison.WordFrontend.FixedFunctionCompleteness.Source.stateFunctionLetFromSource,
    ``IRComparison.FrontendGenerationConditions.twoArgumentHelperHLS.wordBody_correct,
    ``IRComparison.WordFrontend.FixedFunctionCompleteness.Source.complete,
    ``IRComparison.WordFrontend.FixedFunctionCompleteness.Source.install,
    ``IRComparison.WordFrontend.FixedFunctionCompleteness.Source.computation,
    ``IRComparison.WordFrontend.FixedFunctionCompleteness.Source.declared,
    ``IRComparison.WordFrontend.FunctionSyntax.sequence_complete_code,
    ``IRComparison.WordFrontend.StructuralLoop.yield_certificate,
    ``IRComparison.WordFrontend.StructuralLoop.mapped_forStatic_complete_code,
    ``IRComparison.WordFrontend.FunctionSyntax.stepSequence_complete_code,
    ``IRComparison.WordFrontend.FunctionSyntax.yield_complete_code,
    ``IRComparison.WordFrontend.FunctionSyntax.stepBranch_complete_code,
    ``IRComparison.WordFrontend.WordBinder.step_let_certificate,
    ``IRComparison.WordFrontend.FunctionSyntax.stepLetValue_complete_code,
    ``IRComparison.WordFrontend.FunctionSyntax.step_helper_retarget_complete,
    ``IRComparison.WordFrontend.FunctionSyntax.step_functionLet_complete,
    ``IRComparison.WordFrontend.WordBinder.mapped_bind_bits_complete_code,
    ``IRComparison.WordFrontend.WordBinder.mapped_step_bind_bits_complete_code,
    ``IRComparison.WordFrontend.FunctionSyntax.readWord_complete_code,
    ``IRComparison.WordFrontend.FunctionSyntax.stepReadWord_complete_code,
    ``IRComparison.WordFrontend.WordBinder.let_certificate,
    ``IRComparison.WordFrontend.FunctionSyntax.letValue_complete_code,
    ``IRComparison.WordFrontend.FunctionSyntax.branch_typed_complete_code,
    ``IRComparison.WordFrontend.FunctionSyntax.branch_complete_code,
    ``IRComparison.WordFrontend.ScalarEnvironment.reference_complete_code,
    ``IRComparison.WordFrontend.ScalarEnvironment.lookup_selected_complete,
    ``IRComparison.WordFrontend.ScalarSyntax.select_visit_complete_code,
    ``IRComparison.WordFrontend.StructuralStep.Conditional.split_complete_code,
    ``IRComparison.WordFrontend.Certificate.Branch.branch_step_split_complete_code,
    ``IRComparison.WordFrontend.Certificate.Branch.BooleanLibrary.condition_typed,
    ``IRComparison.WordFrontend.Certificate.Branch.BooleanLibrary.header_typed,
    ``IRComparison.WordFrontend.Certificate.Branch.booleanDecision_represents,
    ``IRComparison.WordFrontend.NativeEnvironment.checkDecEqShape_complete,
    ``IRComparison.WordFrontend.NativeEnvironment.decEqShape,
    ``IRComparison.WordFrontend.Arithmetic.AliasSetup.decision_function,
    ``IRComparison.WordFrontend.Arithmetic.AliasSetup.decision_step,
    ``IRComparison.WordFrontend.Arithmetic.AliasSetup.base_universe,
    ``IRComparison.WordFrontend.Arithmetic.decEqTail_typed,
    ``IRComparison.LeanTypeReduction.unfoldConstant_kind,
    ``IRComparison.WordFrontend.Certificate.StateAlias.alias_certificate,
    ``IRComparison.WordFrontend.StructuralStep.Alias.mapped_alias_complete_code,
    ``IRComparison.WordFrontend.FunctionSyntax.stateAlias_complete_code,
    ``IRComparison.WordFrontend.FunctionSyntax.stepAlias_complete_code,
    ``IRComparison.WordFrontend.NaturalLoop.mapped_forRange_complete_code,
    ``IRComparison.WordFrontend.FunctionSyntax.valueAssign_congr,
    ``IRComparison.WordFrontend.StructuralStateLet.mapped_complete_code,
    ``IRComparison.WordFrontend.StructuralStateLet.Loop.mapped_complete_code,
    ``IRComparison.WordFrontend.StructuralUnit.mapped_complete_code,
    ``IRComparison.WordFrontend.NaturalLoop.body_forRange_complete_code,
    ``IRComparison.WordFrontend.FixedSequenceCompleteness.StaticBound.typed,
    ``IRComparison.WordFrontend.StructuralUnit.complete_code,
    ``IRComparison.WordFrontend.WordBinder.step_bind_bits_complete_code,
    ``IRComparison.WordFrontend.WordBinder.step_let_complete_code,
    ``IRComparison.WordFrontend.StructuralReadBind.complete_code,
    ``IRComparison.WordFrontend.StructuralStep.sequence_complete_code,
    ``IRComparison.WordFrontend.StructuralStateLet.Loop.complete_code,
    ``IRComparison.WordFrontend.StructuralStateLet.complete_code,
    ``IRComparison.WordFrontend.StructuralLoop.body_forStatic_complete_code,
    ``IRComparison.WordFrontend.StructuralLoop.yield_complete_code,
    ``IRComparison.WordFrontend.StructuralLoop.value_assign_split_complete_code,
    ``IRComparison.WordFrontend.StructuralLoop.value_skip_complete_code,
    ``IRComparison.WordFrontend.Read.nat_step_invariant_complete_code,
    ``IRComparison.WordFrontend.Read.word_step_split_complete_code,
    ``IRComparison.WordFrontend.Read.bits_word_complete_code,
    ``IRComparison.WordFrontend.Certificate.bindValue_step_complete_code,
    ``IRComparison.WordFrontend.ScopedSyntax.represented_head,
    ``IRComparison.WordFrontend.FixedReadSourceCompleteness.Source.declared,
    ``IRComparison.WordFrontend.FixedReadSourceCompleteness.Source.computation,
    ``IRComparison.WordFrontend.FixedReadSourceCompleteness.Source.valueForm,
    ``IRComparison.WordFrontend.FixedReadSourceCompleteness.Source.complete,

    ``IRComparison.WordFrontend.FixedReadCompleteness.source_syntax_at,
    ``IRComparison.WordFrontend.FixedReadCompleteness.body_complete_at,
    ``IRComparison.WordFrontend.ScopedSyntax.head_form,
    ``IRComparison.WordFrontend.Certificate.sequence_step_complete_code,
    ``IRComparison.WordFrontend.Certificate.store_step_invariant_complete_code,
    ``IRComparison.WordFrontend.Certificate.Return.body_skip_invariant_complete_code,
    ``IRComparison.WordFrontend.WordBinder.let_complete_code,
    ``IRComparison.WordFrontend.ScalarSyntax.literal_visit_complete_code,
    ``IRComparison.WordFrontend.ScalarSyntax.index_visit_complete_code,
    ``IRComparison.WordFrontend.ScalarSyntax.binary_visit_complete_code,
    ``IRComparison.WordFrontend.ScalarSyntax.parameter_visit_complete_code,
    ``IRComparison.WordFrontend.ScalarSyntax.register_visit_complete_code,
    ``IRComparison.WordFrontend.ScalarSyntax.neg_visit_complete_code,
    ``IRComparison.WordFrontend.FixedSequenceCompleteness.Source.declared,
    ``IRComparison.WordFrontend.FixedSequenceCompleteness.Source.computation,
    ``IRComparison.WordFrontend.FixedSequenceCompleteness.Source.complete,
    ``IRComparison.WordFrontend.FixedScalarCompleteness.Source.declared,
    ``IRComparison.WordFrontend.FixedScalarCompleteness.Source.computation,
    ``IRComparison.WordFrontend.FixedScalarCompleteness.Source.complete,

    ``IRComparison.Imperative.transform_correct,
    ``IRComparison.Functional.transform_correct,
    ``IRComparison.lowerBody_correct,
    ``IRComparison.lowerProgram_correct,
    ``IRComparison.optimized_agree,
    ``IRComparison.Examples.forward_example,
    ``IRComparison.Examples.reverse_example,
    ``IRComparison.Source.extract_correct,
    ``IRComparison.Frontend.compileImperative_correct,
    ``IRComparison.Frontend.compileFunctional_correct,
    ``IRComparison.Frontend.compilers_agree,
    ``IRComparison.NativeLoop.run_eq_iterate,
    ``IRComparison.NativeLoop.imperative_correct,
    ``IRComparison.NativeLoop.functional_correct,
    ``IRComparison.NativeBody.compileImperative_correct,
    ``IRComparison.NativeBody.compileFunctional_correct,
    ``IRComparison.NativeExamples.imperative_correct,
    ``IRComparison.NativeExamples.functional_correct,
    ``IRComparison.LeanScalar.compile_correct,
    ``IRComparison.LeanScalar.environment_cons,
    ``IRComparison.LeanScalar.compileFunction_correct,
    ``IRComparison.LeanScalar.FunctionArtifact.state_independent,
    ``IRComparison.LeanScalar.FunctionArtifact.imperative_correct,
    ``IRComparison.LeanScalar.FunctionArtifact.functional_correct,
    ``IRComparison.LeanDefinition.Artifact.application,
    ``IRComparison.LeanDefinition.Artifact.declaration_unique,
    ``IRComparison.LeanTyped.Represents.instantiate,
    ``IRComparison.LeanTyped.typed_beta,
    ``IRComparison.LeanTyped.typed_let,
    ``IRComparison.LeanTyped.DefinitionView.unfold,
    ``IRComparison.LeanTyped.DefinitionView.apply_three,
    ``IRComparison.LeanTyped.DefinitionView.source,
    ``IRComparison.LeanTyped.DefinitionView.type_shape,
    ``IRComparison.DependencyClosure.walk_contains,
    ``IRComparison.LeanLibrary.installTypes_present,
    ``IRComparison.LeanLibrary.Declaration.signature_unique,
    ``IRComparison.WordFrontend.loaded_library_signature,
    ``IRComparison.WordFrontend.ScalarSyntax.register_complete,
    ``IRComparison.WordFrontend.ScalarSyntax.select_complete,
    ``IRComparison.WordFrontend.StructuralLoop.body_forStatic_complete,
    ``IRComparison.WordFrontend.StructuralLoop.yield_complete,
    ``IRComparison.WordFrontend.StructuralStep.sequence_complete,
    ``IRComparison.WordFrontend.StructuralStep.Conditional.complete,
    ``IRComparison.WordFrontend.StructuralStep.Alias.alias_step_complete,
    ``IRComparison.WordFrontend.StructuralReadBind.complete,
    ``IRComparison.WordFrontend.StructuralReadBind.letValue_step_complete,
    ``IRComparison.WordFrontend.StructuralStateLet.complete,
    ``IRComparison.WordFrontend.StructuralStateLet.Loop.complete,
    ``IRComparison.WordFrontend.StructuralUnit.complete,
    ``IRComparison.WordFrontend.ScopedSyntax.syntax_complete,
    ``IRComparison.WordFrontend.ScopedSyntax.complete,
    ``IRComparison.WordFrontend.Certificate.Step.direct_beta_conversion_domain,
    ``IRComparison.WordFrontend.Certificate.For.unit_beta_conversion,
    ``IRComparison.DependencyClosure.walk_closed,
    ``IRComparison.WordFrontend.Certificate.finish_checked_complete,
    ``IRComparison.WordFrontend.Read.Signatures.annotationDictionary,
    ``IRComparison.WordFrontend.Read.Signatures.bits_header_typed,
    ``IRComparison.WordFrontend.Read.Signatures.bits_source_typed,
    ``IRComparison.WordFrontend.Read.element_equality_conversion,
    ``IRComparison.WordFrontend.Read.bits_finish_complete,
    ``IRComparison.WordFrontend.Read.bits_nat_complete,
    ``IRComparison.WordFrontend.Read.bits_word_complete,
    ``IRComparison.WordFrontend.WordBinder.bind_equality_conversion,
    ``IRComparison.WordFrontend.WordBinder.bind_bits_complete,
    ``IRComparison.WordFrontend.WordBinder.bind_bits_complete_code,
    ``IRComparison.WordFrontend.WordBinder.checked_option_bitvec,
    ``IRComparison.WordFrontend.WordBinder.step_bind_bits_complete,
    ``IRComparison.WordFrontend.StructuralBody.finishBody_code,
    ``IRComparison.WordFrontend.StructuralBody.retargetPiece_code,
    ``IRComparison.WordFrontend.Certificate.Return.assign_step_split_complete_code,
    ``IRComparison.WordFrontend.Read.bits_nat_complete_code,
    ``IRComparison.WordFrontend.ScalarSyntax.local_visit_complete_code,
    ``IRComparison.WordFrontend.FixedReadCompleteness.source_syntax,
    ``IRComparison.WordFrontend.FixedReadCompleteness.body_complete,
    ``IRComparison.WordFrontend.StructuralSyntax.mapped_bindValue,
    ``IRComparison.WordFrontend.StructuralSyntax.mapped_letValue,
    ``IRComparison.WordFrontend.StructuralBody.closureReference_scoped,
    ``IRComparison.WordFrontend.StructuralBody.closureBody_scoped,
    ``IRComparison.WordFrontend.StructuralBody.lambdaChain_scoped,
    ``IRComparison.WordFrontend.StructuralBody.LambdaSource.parts,
    ``IRComparison.WordFrontend.StructuralBody.LambdaSource.capture,
    ``IRComparison.WordFrontend.StructuralBody.LambdaSource.call_scoped,
    ``IRComparison.WordFrontend.StructuralSyntax.HeadForm.parser_congr,
    ``IRComparison.WordFrontend.Arithmetic.AliasSetup.helper_proved,
    ``IRComparison.WordFrontend.Certificate.For.helper_equality_conversion,
    ``IRComparison.WordFrontend.StructuralBody.applicationHead_app,
    ``IRComparison.WordFrontend.StructuralSyntax.helper_retarget_complete,
    ``IRComparison.WordFrontend.Arithmetic.AliasSetup.function_state_none,
    ``IRComparison.WordFrontend.Arithmetic.AliasSetup.function_word_none,
    ``IRComparison.WordFrontend.StructuralSyntax.function_let_step_complete,
    ``IRComparison.WordFrontend.FunctionSyntax.BindingValue.construct,
    ``IRComparison.WordFrontend.FunctionSyntax.branch_complete,
    ``IRComparison.WordFrontend.FunctionSyntax.sequence_complete,
    ``IRComparison.WordFrontend.FunctionSyntax.complete,
    ``IRComparison.WordFrontend.FixedSequenceCompleteness.InputConditions.assign,
    ``IRComparison.WordFrontend.FixedFunctionCompleteness.Source.toEntry,
    ``IRComparison.WordFrontend.FixedFunctionCompleteness.boundCallTypingFromSyntax,
    ``IRComparison.WordFrontend.LexicalScalarSyntax.expand_substituteCache,
    ``IRComparison.WordFrontend.LexicalScalarSyntax.under_substituteCache,
    ``IRComparison.WordFrontend.LexicalScalarSyntax.sourceReference_cons,
    ``IRComparison.WordFrontend.LexicalScalarSyntax.expand_rename_cons,
    ``IRComparison.WordFrontend.LexicalScalarSyntax.substituteCache_cons,
    ``IRComparison.WordFrontend.LexicalScalarSyntax.Form.substituteCache,
    ``IRComparison.WordFrontend.LexicalScalarSyntax.Form.materialize,
    ``IRComparison.WordFrontend.LexicalScalarSyntax.Form.instantiateFromSyntax,
    ``IRComparison.WordFrontend.LexicalScalarSyntax.ValueShape.instantiateAt,
    ``IRComparison.WordFrontend.LexicalScalarCode.Evidence.instantiateAt,
    ``IRComparison.WordFrontend.FunctionSyntax.parameterScope,
    ``IRComparison.WordFrontend.FunctionSyntax.parameterInputs_retag,
    ``IRComparison.WordFrontend.FunctionSyntax.parameterInputs_prefix,
    ``IRComparison.WordFrontend.FunctionSyntax.parameterTypes_prefix,
    ``IRComparison.WordFrontend.FunctionSyntax.Syntax.functionLetFromLambda,
    ``IRComparison.WordFrontend.FunctionSyntax.Syntax.functionLetFromLambdaMode,
    ``IRComparison.WordFrontend.FunctionSyntax.sourceBindTyping,
    ``IRComparison.WordFrontend.FunctionSyntax.sourceBooleanTyping,
    ``IRComparison.WordFrontend.FunctionSyntax.sourceForStaticTyping,
    ``IRComparison.WordFrontend.FunctionSyntax.sourceForRangeTyping,
    ``IRComparison.WordFrontend.FunctionSyntax.sourceBinderTyping,
    ``IRComparison.WordFrontend.FixedSequenceCompleteness.InputConditions.choice,
    ``IRComparison.WordFrontend.FixedSequenceCompleteness.InputConditions.returnVariable,
    ``IRComparison.WordFrontend.FunctionSyntax.Syntax.lambdaTyping,
    ``IRComparison.WordFrontend.FunctionSyntax.lambdaTypingFromBody,
    ``IRComparison.WordFrontend.FunctionSyntax.Syntax.bodyTyping,
    ``IRComparison.WordFrontend.FunctionSyntax.syntax_complete,
    ``IRComparison.WordFrontend.FunctionSyntax.Syntax.install,
    ``IRComparison.WordFrontend.StandardLibrary.library,
    ``IRComparison.WordFrontend.StandardLibrary.checkEntries_complete,
    ``IRComparison.WordFrontend.StandardLibrary.check_complete,
    ``IRComparison.WordFrontend.SignatureClosure.selected_subset,
    ``IRComparison.WordFrontend.loaded_types_closed_in_scope,
    ``IRComparison.WordFrontend.NativeEnvironment.scope_complete,
    ``IRComparison.WordFrontend.NativeEnvironment.checkClosed_complete,
    ``IRComparison.WordFrontend.NativeEnvironment.wordShape,
    ``IRComparison.WordFrontend.NativeEnvironment.checkWordShape_complete,
    ``IRComparison.WordFrontend.NativeEnvironment.fresh_of_not_library,
    ``IRComparison.WordFrontend.NativeEnvironment.prepare_complete,
    ``IRComparison.WordFrontend.compileWith_code_of_body,
    ``IRComparison.WordFrontend.NatNotation.view_complete,
    ``IRComparison.WordFrontend.Arithmetic.Signatures.natural_notation_typed,
    ``IRComparison.WordFrontend.FixedCopyCompleteness.source_syntax,

    ``IRComparison.DependencyClosure.walk_reachable,
    ``IRComparison.WordFrontend.loaded_reachable_signature,
    ``IRComparison.WordFrontend.ScalarEnvironment.retarget_same_complete,
    ``IRComparison.WordFrontend.ScalarEnvironment.retarget_cast_complete,
    ``IRComparison.WordFrontend.ScalarEnvironment.reference_complete,
    ``IRComparison.WordFrontend.ScalarSyntax.binary_visit_complete,
    ``IRComparison.WordFrontend.Arithmetic.AliasSetup.scalar_beta_proved,
    ``IRComparison.WordFrontend.ScalarConversion.Casts.covered,
    ``IRComparison.WordFrontend.ScalarConversion.let_visit_complete,
    ``IRComparison.WordFrontend.Arithmetic.neg_finish,
    ``IRComparison.WordFrontend.ScalarSyntax.parameter_visit_complete,
    ``IRComparison.WordFrontend.ScalarSyntax.index_visit_complete,
    ``IRComparison.WordFrontend.ScalarSyntax.local_visit_complete,
    ``IRComparison.WordFrontend.ScalarSyntax.literal_visit_complete,
    ``IRComparison.WordFrontend.ScalarSyntax.neg_visit_complete,
    ``IRComparison.WordFrontend.ScalarSyntax.select_visit_complete,
    ``IRComparison.WordFrontend.ScalarSyntax.register_visit_complete,
    ``IRComparison.WordFrontend.ScalarConversion.beta_visit_complete,
    ``IRComparison.LeanStructuralConversion.prove_application_cast_complete,
    ``IRComparison.WordFrontend.Arithmetic.AliasSetup.scalar_beta_checked_domain_proved,
    ``IRComparison.WordFrontend.WordBinder.Annotation.result,
    ``IRComparison.WordFrontend.WordBinder.Annotation.substitute_native,
    ``IRComparison.WordFrontend.WordBinder.Annotation.view_complete,
    ``IRComparison.WordFrontend.NativeEnvironment.header_complete,
    ``IRComparison.WordFrontend.NativeEnvironment.input_complete,
    ``IRComparison.WordFrontend.LexicalScalarSyntax.complete,
    ``IRComparison.WordFrontend.LexicalScalarSyntax.parse_complete,
    ``IRComparison.WordFrontend.ScopedSyntax.scalar_complete,
    ``IRComparison.WordFrontend.Certificate.continuation_beta_conversion_with_domain,
    ``IRComparison.WordFrontend.WordBinder.Annotation.domain_proved,
    ``IRComparison.WordFrontend.WordBinder.Annotation.function_conversion,
    ``IRComparison.WordFrontend.WordBinder.Annotation.continuation_conversion,
    ``IRComparison.WordFrontend.WordBinder.let_complete,
    ``IRComparison.WordFrontend.WordBinder.step_let_complete,
    ``IRComparison.WordFrontend.NaturalLoop.body_forRange_complete,
    ``IRComparison.WordFrontend.loaded_source_signature,
    ``IRComparison.WordFrontend.NativeCompleteness.SourceTable.installed,
    ``IRComparison.WordFrontend.ScopedSyntax.Syntax.install,
    ``IRComparison.WordFrontend.ScopedSyntax.Library.install,
    ``IRComparison.WordLoopFacts.letValue,
    ``IRComparison.WordLoopFacts.letStateAlias,
    ``IRComparison.WordLoopFacts.letState,
    ``IRComparison.WordLoopFacts.bindValue,
    ``IRComparison.WordLoopFacts.sequence,
    ``IRComparison.WordLoopFacts.branchCmd,
    ``IRComparison.WordLoopFacts.unitSequence,
    ``IRComparison.WordFrontendFacts.unitSequence,
    ``IRComparison.WordFrontend.ScalarEnvironment.materialize_eq_substitute,
    ``IRComparison.WordFrontend.StructuralBody.Substitution.apply_eq,
    ``IRComparison.WordFrontend.StructuralBody.under_reference,
    ``IRComparison.WordFrontend.StructuralBody.bindArgument_complete,
    ``IRComparison.WordFrontend.StructuralBody.retainArguments_bind_complete,
    ``IRComparison.WordFrontend.StructuralBody.compileRetained_correct,
    ``IRComparison.WordFrontend.ScopedSyntax.compile_of_parser_rule_with_code,
    ``IRComparison.WordFrontend.NativeEnvironment.Input.compilesInstalledCodeWith,
    ``IRComparison.WordFrontend.FunctionSyntax.BindingValue.retained_call_complete,
    ``IRComparison.WordFrontend.FixedFunctionCompleteness.generatesRetainedSyntax,
    ``IRComparison.WordFrontend.FixedFunctionCompleteness.Source.completeArguments,
    ``IRComparison.WordFrontend.StructuralBody.unitArgument_of_type,
    ``IRComparison.WordFrontend.StructuralBody.ArgumentBindings.complete,
    ``IRComparison.WordFrontend.StructuralBody.ArgumentBindings.facts,
    ``IRComparison.WordFrontend.StructuralBody.ArgumentBindings.install,
    ``IRComparison.WordFrontend.StructuralBody.ArgumentBindings.scalarFromSyntax,
    ``IRComparison.WordFrontend.RetainedConversion.conversion_complete,
    ``IRComparison.WordFrontend.RetainedConversion.prefix_endpoint,
    ``IRComparison.WordFrontend.RetainedConversion.reducePrefix_checkedBeta,
    ``IRComparison.WordFrontend.RetainedConversion.reducePrefix_beta,
    ``IRComparison.WordFrontend.RetainedConversion.reducePrefix_mono,
    ``IRComparison.WordFrontend.StructuralBody.retargetRetainedPiece_of_retarget,
    ``IRComparison.WordFrontend.StructuralBody.ArgumentBindings.context_growth,
    ``IRComparison.WordFrontend.StructuralBody.ArgumentBindings.argument_count,
    ``IRComparison.WordFrontend.FunctionSyntax.closureSubstitution_instantiate,
    ``IRComparison.WordFrontend.FunctionSyntax.closureSubstitution_retain_actual,
    ``IRComparison.LeanBindings.substitute_instantiate,
    ``IRComparison.WordFrontend.RetainedConversion.contractLets_substitute,
    ``IRComparison.WordFrontend.RetainedConversion.contractLets_represents,
    ``IRComparison.WordFrontend.RetainedConversion.Prefix.typed,
    ``IRComparison.WordFrontend.RetainedConversion.Prefix.instN,
    ``IRComparison.WordFrontend.RetainedConversion.Prefix.complete,
    ``IRComparison.WordFrontend.RetainedConversion.conversion_of_prefix,
    ``IRComparison.WordFrontend.StructuralBody.argumentAnnotation_of_type,
    ``IRComparison.WordFrontend.StructuralBody.ArgumentBindings.endpointInputs,
    ``IRComparison.WordFrontend.StructuralBody.ArgumentBindings.contract,
    ``IRComparison.WordFrontend.StructuralBody.ArgumentBindings.contract_represents,
    ``IRComparison.WordFrontend.StructuralBody.ArgumentBindings.prefix,
    ``IRComparison.WordFrontend.StructuralBody.ArgumentBindings.prefix_complete,
    ``IRComparison.WordFrontend.StructuralBody.retargetRetainedPiece_of_prefix,
    ``IRComparison.WordFrontend.FunctionSyntax.BindingValue.retained_call_representations,
    ``IRComparison.WordFrontend.FunctionSyntax.BindingValue.retained_call_complete_with_transport,
    ``IRComparison.WordFrontend.FixedFunctionCompleteness.Source.retainedPrefix,
    ``IRComparison.WordFrontend.RetainedConversion.conversion_checked_call,
    ``IRComparison.WordFrontend.StructuralBody.retargetRetainedPiece_of_conversion,
    ``IRComparison.WordFrontend.StructuralBody.retargetRetainedPiece_checked_call,
    ``IRComparison.WordFrontend.StructuralBody.RetainedCasts.equalityPrefix,
    ``IRComparison.WordFrontend.FixedFunctionCompleteness.Source.completeRetainedCall,
    ``IRComparison.RetainedArgumentExamples.updateArgument_snapshot,
    ``IRComparison.RetainedArgumentExamples.severalArguments_snapshot,
    ``IRComparison.WordFrontend.ScalarSyntax.complete,
    ``IRComparison.WordFrontend.ScalarSyntax.complete_loaded,
    ``IRComparison.WordFrontend.Certificate.store_step_complete,
    ``IRComparison.WordFrontend.StructuralSyntax.complete,
    ``IRComparison.Circuit.Shared.command_simulates,
    ``IRComparison.Circuit.Shared.channel_simulates,
    ``IRComparison.Circuit.Shared.pipeline_related,
    ``IRComparison.Circuit.Shared.prepare_references,
    ``IRComparison.Circuit.Shared.prepared_storage,
    ``IRComparison.Circuit.Shared.graph_cases_references,
    ``IRComparison.Circuit.Shared.graph_cases_ready,
    ``IRComparison.Circuit.Shared.graph_cases_frame,
    ``IRComparison.Circuit.Shared.generated_tick,
    ``IRComparison.Circuit.Shared.generated_run,
    ``IRComparison.Circuit.Shared.generated_text_run,
    ``IRComparison.Circuit.Shared.compileStructured_correct,
    ``IRComparison.Circuit.SystemVerilog.combinational_codeSound,
    ``IRComparison.Circuit.SystemVerilog.testCode_correctWith,
    ``IRComparison.Circuit.SystemVerilog.scalarCode_correctWith,
    ``IRComparison.Circuit.SystemVerilog.statementCode_assign_correctWith,
    ``IRComparison.Circuit.SystemVerilog.statementCode_store_correctWith,
    ``IRComparison.Circuit.SystemVerilog.statementCode_send_correctWith,
    ``IRComparison.Circuit.SystemVerilog.statementCode_refines_controlWith,
    ``IRComparison.Circuit.SystemVerilog.keeps_statementCode,
    ``IRComparison.Circuit.Shared.NetEmission.shared_codeSound,
    ``IRComparison.Circuit.Shared.NetEmission.sum_codeSound,
    ``IRComparison.Circuit.Shared.NetEmission.shared_keeps_trace,
    ``IRComparison.Circuit.Shared.NetEmission.shared_cases_total,
    ``IRComparison.Circuit.Shared.NetEmission.shared_statement_refines_control,
    ``IRComparison.Circuit.Shared.NetEmission.shared_cases_refine,
    ``IRComparison.Circuit.Shared.NetEmission.shared_module_tick,
    ``IRComparison.Circuit.Shared.NetEmission.shared_module_text_tick,

    ``IRComparison.Circuit.Emission.WellFormed.extendDeclarations,
    ``IRComparison.Circuit.preserves_statementCodeWith,
    ``IRComparison.Circuit.Shared.NetEmission.append_generate,
    ``IRComparison.Circuit.Shared.NetEmission.append_builds,
    ``IRComparison.Circuit.Shared.NetEmission.append_correct,
    ``IRComparison.Circuit.Shared.NetEmission.intoPair_builds,
    ``IRComparison.Circuit.Shared.NetEmission.intoPair_correct,
    ``IRComparison.Circuit.Shared.NetEmission.intoPair_cacheMeaning,
    ``IRComparison.Circuit.Shared.NetEmission.into_signal_correct,
    ``IRComparison.Circuit.Shared.NetEmission.intoPair_trace,
    ``IRComparison.Circuit.Shared.prepare_bounds,
    ``IRComparison.Circuit.Shared.prepare_correct,
    ``IRComparison.Circuit.Shared.prepare_range_correct,
    ``IRComparison.Circuit.Shared.prepare_statement_correct,
    ``IRComparison.Circuit.Shared.NetEmission.shared_statement_preserves,
    ``IRComparison.Circuit.Shared.NetEmission.mixed_statement_preserves,
    ``IRComparison.Circuit.Shared.NetEmission.module_declarations_ordered,
    ``IRComparison.Circuit.Shared.NetEmission.generateModule_text,
    ``IRComparison.Circuit.Shared.LocalRTL.fullValues_model,
    ``IRComparison.Circuit.Shared.LocalRTL.compile_fullEval_correct,
    ``IRComparison.Circuit.Shared.NetEmission.generate_ordered,
    ``IRComparison.Circuit.Shared.NetEmission.term_correct,
    ``IRComparison.Circuit.Shared.NetEmission.validity_correct,
    ``IRComparison.Circuit.Shared.NetEmission.expression_correct,
    ``IRComparison.Circuit.Shared.NetEmission.graph_correct,
    ``IRComparison.Circuit.Shared.NetEmission.generate_correct,
    ``IRComparison.Circuit.Shared.NetEmission.physical_from_refs,
    ``IRComparison.Circuit.Shared.NetEmission.NetTrace.total,
    ``IRComparison.Circuit.Shared.NetEmission.graph_trace,
    ``IRComparison.Circuit.Shared.NetEmission.generate_total,
    ``IRComparison.Circuit.Shared.NetEmission.read_text,
    ``IRComparison.Circuit.Shared.NetEmission.evaluate_text,
    ``IRComparison.Circuit.Shared.NetEmission.emitted_read_correct,
    ``IRComparison.Circuit.Shared.NetEmission.emitted_total_correct,
    ``IRComparison.Circuit.Shared.NetEmission.emitted_read_total_correct,
    ``IRComparison.Circuit.SystemVerilog.Concrete.readWiresTail_eq,
    ``IRComparison.Circuit.Shared.lowerValue_projection,
    ``IRComparison.Circuit.Shared.lowerRead_projection,
    ``IRComparison.Circuit.Shared.build_projection,
    ``IRComparison.Circuit.Shared.Node.bitEval_correct,
    ``IRComparison.Circuit.Shared.bitValues_correct,
    ``IRComparison.Circuit.Shared.Program.bitEval_correct,
    ``IRComparison.Circuit.Shared.compile_bitEval_correct,
    ``IRComparison.Circuit.Shared.LocalRTL.lower_correct,
    ``IRComparison.Circuit.Shared.LocalRTL.lowerGraph_correct,
    ``IRComparison.Circuit.Shared.LocalRTL.lowerGraph_size,
    ``IRComparison.Circuit.Shared.LocalRTL.compile_correct,
    ``IRComparison.Circuit.Shared.LocalRTL.compile_read_correct,
    ``IRComparison.Circuit.Shared.compile_ordered,
    ``IRComparison.Circuit.Shared.compile_result_bound,
    ``IRComparison.Circuit.Shared.compile_correct,
    ``IRComparison.Circuit.Shared.compile_read_correct,
    ``IRComparison.Circuit.Shared.Program.range_correct,
    ``IRComparison.Circuit.Shared.Program.agrees,
    ``IRComparison.HybridSymbolicGlobal.improve_selected,
    ``IRComparison.HybridSymbolicGlobal.compile_selected,
    ``IRComparison.Circuit.SystemVerilog.ExternalPorts.request_exact,
    ``IRComparison.Circuit.SystemVerilog.ExternalPorts.request_rejects,
    ``IRComparison.Circuit.SystemVerilog.ExternalPorts.array_request,
    ``IRComparison.Circuit.SystemVerilog.ExternalPorts.register_request,
    ``IRComparison.Circuit.SystemVerilog.ExternalPorts.configuration_exact,
    ``IRComparison.Circuit.SystemVerilog.ExternalPorts.output_request,
    ``IRComparison.Circuit.SystemVerilog.ExternalPorts.emitted_output_request,
    ``IRComparison.Circuit.SystemVerilog.ExternalPorts.oversized_id_rejected,
    ``IRComparison.Circuit.SystemVerilog.ExternalPorts.oversized_length_rejected,

    ``IRComparison.HybridSymbolicProducer.BodyShape.word,
    ``IRComparison.HybridSymbolicProducer.BodyShape.sendBound,
    ``IRComparison.HybridSymbolicProducer.Compiled.word,
    ``IRComparison.HybridSymbolicProducer.Compiled.sendBound,
    ``IRComparison.HybridSymbolicLoop.Selected.word,
    ``IRComparison.HybridSymbolicGlobal.Plan.word,
    ``IRComparison.Circuit.word_compactStages,
    ``IRComparison.Circuit.symbolic_step_sendBound,
    ``IRComparison.Circuit.symbolic_plan_sendBounds,
    ``IRComparison.Circuit.compile_sendBudgets,
    ``IRComparison.Circuit.compileStep_policy,
    ``IRComparison.Circuit.compilePolicy_policy,
    ``IRComparison.Circuit.compile_policy,
    ``IRComparison.Circuit.respects_communication,
    ``IRComparison.Circuit.compile_communication,
    ``IRComparison.Circuit.compile_memory_checks,
    ``IRComparison.Circuit.compilePolicy_empty_total,
    ``IRComparison.Circuit.symbolic_compile_total,
    ``IRComparison.HybridIR.WordValue.weaken,
    ``IRComparison.HybridIR.WordRead.weaken,
    ``IRComparison.HybridIR.WordChannel.capture,
    ``IRComparison.ChannelScope.value_word,
    ``IRComparison.ChannelScope.read_word,
    ``IRComparison.ChannelCommandBridge.command_word,
    ``IRComparison.Circuit.ChannelLower.lower_dataWords,
    ``IRComparison.Circuit.ChannelCounted.command_word,
    ``IRComparison.Circuit.ChannelCounted.lower_dataWords,
    ``IRComparison.Circuit.symbolicInstruction_dataWords,
    ``IRComparison.Circuit.symbolicInstructions_dataWords,
    ``IRComparison.Circuit.symbolic_schedule_dataWords,
    ``IRComparison.Circuit.compile_schedule_dataWords,

    ``IRComparison.HybridIR.WordValue.affineLocal,
    ``IRComparison.HybridIR.WordRead.affineLocal,
    ``IRComparison.HybridIR.WordCommand.affineLocal,
    ``IRComparison.HybridWord.Expr.lower_word,
    ``IRComparison.HybridWord.Cmd.lower_word,
    ``IRComparison.Circuit.WordRanges.value_word,
    ``IRComparison.Circuit.WordRanges.read_word,
    ``IRComparison.Circuit.WordRanges.lower_affine,
    ``IRComparison.Circuit.CommandWordRanges.command_dataWords,
    ``IRComparison.Circuit.CommandWordRanges.source_dataWords,
    ``IRComparison.Circuit.Frame.refine_within,
    ``IRComparison.Circuit.Frame.widen_get_below,
    ``IRComparison.Circuit.Frame.refine_counter_below,
    ``IRComparison.Circuit.Frame.refine_increment_inside,
    ``IRComparison.Circuit.transfer_counter_increment,
    ``IRComparison.Circuit.Action.transfer_preserves_below,
    ``IRComparison.Circuit.range_nonempty,
    ``IRComparison.Circuit.range_mono,
    ``IRComparison.Circuit.Expr.range_agrees,
    ``IRComparison.Circuit.transfer_wire_inside,
    ``IRComparison.Circuit.WireAllocation.Extends.get,
    ``IRComparison.Circuit.WireAllocation.command,
    ``IRComparison.Circuit.WireAllocation.channelLower,
    ``IRComparison.Circuit.WireAllocation.scheduled,
    ``IRComparison.Circuit.WordRanges.lower,
    ``IRComparison.Circuit.WordRanges.wire_of_within,
    ``IRComparison.Circuit.WordRanges.transfer_store,
    ``IRComparison.Circuit.WordRanges.transfer_assign,
    ``IRComparison.Circuit.Interval.widenBudget_lt,
    ``IRComparison.Circuit.Frame.widen_merge_inside,
    ``IRComparison.Circuit.Frame.widenBudget_lt,
    ``IRComparison.Circuit.InferenceProgress.joinIncoming_progress,
    ``IRComparison.Circuit.InferenceProgress.enqueue_complete,
    ``IRComparison.Circuit.InferenceProgress.inferWorklist_complete,
    ``IRComparison.Circuit.InferenceProgress.standard_budget,
    ``IRComparison.Circuit.InferenceProgress.initialized_complete,
    ``IRComparison.Circuit.inferInvariant_complete,
    ``IRComparison.Circuit.Pipelining.inferClockInvariant_complete,
    ``IRComparison.Circuit.BuildInvariant.Rules.command,
    ``IRComparison.Circuit.BuildInvariant.Rules.channelLower,
    ``IRComparison.Circuit.BuildInvariant.Rules.schedule,
    ``IRComparison.Circuit.RangeScoped.exprRange_extend,
    ``IRComparison.Circuit.capture_range,
    ``IRComparison.Circuit.transfer_capture,
    ``IRComparison.Circuit.ScheduleRange.layout,
    ``IRComparison.Circuit.LayoutRanges.closed,
    ``IRComparison.Circuit.ScheduleRange.inferInvariant,
    ``IRComparison.Circuit.Action.transfer_preserves_wire,
    ``IRComparison.Circuit.ScheduleRange.withCounters,
    ``IRComparison.Circuit.RangeSafe.counterLoop,
    ``IRComparison.Circuit.RangeSafe.capturedLoop,
    ``IRComparison.Circuit.ChannelLower.reserve_ranges,
    ``IRComparison.Circuit.ChannelLower.lower_ranges,
    ``IRComparison.Circuit.ChannelCounted.lower_ranges,
    ``IRComparison.Circuit.symbolicInstruction_ranges,
    ``IRComparison.Circuit.symbolicInstructions_ranges,
    ``IRComparison.Circuit.symbolic_schedule_ranges,
    ``IRComparison.Circuit.compile_schedule_ranges,
    ``IRComparison.Circuit.compile_schedule_inference,
    ``IRComparison.Circuit.Pipelining.sequential_named_finishes,
    ``IRComparison.Circuit.Pipelining.InitialWidths.named,
    ``IRComparison.Circuit.Pipelining.InitialWidths.scheduled,
    ``IRComparison.Circuit.Pipelining.InitialWidths.scheduled_legacy,
    ``IRComparison.Circuit.Pipelining.InitialWidths.Ready.check,
    ``IRComparison.Circuit.Pipelining.InitialWidths.scheduled_check,
    ``IRComparison.Circuit.Pipelining.InitialWidths.scheduled_legacy_check,
    ``IRComparison.Circuit.Pipelining.ClockGraph.inventory_closed,
    ``IRComparison.Circuit.Pipelining.checkGraph_succeeds,
    ``IRComparison.Circuit.Pipelining.structured_generation,
    ``IRComparison.Circuit.Pipelining.scheduleStructure_safe,
    ``IRComparison.Circuit.Pipelining.overlapLoops_safe,
    ``IRComparison.Circuit.Pipelining.ClockTree.assemble_safe,
    ``IRComparison.Circuit.Pipelining.ClockTree.assemble_targets,
    ``IRComparison.Circuit.Pipelining.ClockTree.assemble_distinct,
    ``IRComparison.Circuit.Pipelining.ClockTree.assemble_entry,
    ``IRComparison.Circuit.Pipelining.structured_safe,
    ``IRComparison.Circuit.Pipelining.structured_control_checks,
    ``IRComparison.Circuit.Allocation.schedule_allocated,
    ``IRComparison.Circuit.Allocation.find_declared,
    ``IRComparison.Circuit.Allocation.interface_of_extension,
    ``IRComparison.Circuit.Allocation.scheduled_metadata,
    ``IRComparison.Circuit.Allocation.MetadataReady.moduleReady,
    ``IRComparison.Circuit.Pipelining.structured_metadata,
    ``IRComparison.Circuit.Pipelining.structured_entry,
    ``IRComparison.FixedHLS.Entry.layout_unique,
    ``IRComparison.FixedHLS.Entry.generated_metadata,
    ``IRComparison.FixedHLS.Entry.generated_outputs,
    ``IRComparison.Circuit.SystemVerilog.Generation.termText_total,
    ``IRComparison.Circuit.SystemVerilog.Generation.validityText_total,
    ``IRComparison.Circuit.SystemVerilog.Generation.expression_total,
    ``IRComparison.Circuit.SystemVerilog.Generation.statementCode_total,
    ``IRComparison.Circuit.SystemVerilog.Generation.checkModuleArtifact_total,
    ``IRComparison.Circuit.SystemVerilog.Generation.checkReadOutputs_total,
    ``IRComparison.Circuit.SystemVerilog.Generation.generateCode_total,
    ``IRComparison.Circuit.SystemVerilog.Generation.generateModule_total,
    ``IRComparison.Circuit.SystemVerilog.Generation.emit_total,
    ``IRComparison.Circuit.SystemVerilog.Generation.combinational_ready,
    ``IRComparison.Circuit.SystemVerilog.Generation.lowerNode_ready,
    ``IRComparison.Circuit.SystemVerilog.Generation.emit_of_nodes,
    ``IRComparison.Circuit.Pipelining.ClockNode.statement_emitReady,
    ``IRComparison.Circuit.Pipelining.generateGraph_succeeds,
    ``IRComparison.Circuit.Pipelining.generateGraphModule_succeeds,
    ``IRComparison.DependencyClosure.complete,
    ``IRComparison.WordFrontend.dependencies_complete,
    ``IRComparison.FixedMemory.affine_read_arrays,
    ``IRComparison.FixedMemory.affine_command_arrays,
    ``IRComparison.FixedMemory.expr_lower_declared,
    ``IRComparison.FixedMemory.lower_declared,
    ``IRComparison.FixedMemory.lookup_mem,
    ``IRComparison.FixedHLS.Entry.declaration_in_layout,
    ``IRComparison.FixedHLS.Entry.anchor_in_layout,
    ``IRComparison.FixedHLS.Entry.lower_arrays_in_layout,
    ``IRComparison.FixedHLS.Entry.outputs_safe,
    ``IRComparison.HybridUnifiedPipeline.compile_total,
    ``IRComparison.HybridWord.compileProgram_total,
    ``IRComparison.WordFrontendFacts.letValue,
    ``IRComparison.WordFrontendFacts.letState,
    ``IRComparison.WordLoopFacts.letBinding,
    ``IRComparison.FixedMemoryExamples.sparseHLS.correct,
    ``IRComparison.FixedMemoryExamples.scalarHLS.correct,
    ``IRComparison.FixedMemoryExamples.emptyHLS.correct,
    ``IRComparison.FixedMemoryExamples.capturedHLS.correct,
    ``IRComparison.FixedMemoryExamples.capturedLoopHLS.correct,
    ``IRComparison.HybridWord.State.encode_writeNat,
    ``IRComparison.WordFrontendFacts.copy,
    ``IRComparison.FixedMemory.declared_copy,
    ``IRComparison.FixedMemory.write_sizes,
    ``IRComparison.FixedMemory.writeNat_sizes,
    ``IRComparison.FixedMemory.fold_sizes,
    ``IRComparison.FixedMemory.copy_sizes,
    ``IRComparison.FixedMemory.copy_prefix,
    ``IRComparison.FixedMemory.copy_complete,
    ``IRComparison.FixedMemory.eval_sizes,
    ``IRComparison.FixedHLS.Entry.compile_correct,
    ``IRComparison.FixedHLS.Entry.preserves_sizes,
    ``IRComparison.FixedMemoryExamples.independentHLS.correct,
    ``IRComparison.FixedMemoryExamples.repeatedHLS.correct,
    ``IRComparison.FixedMemoryExamples.swapHLS.correct,
    ``IRComparison.FixedMemoryExamples.nestedHLS.correct,
    ``IRComparison.FixedMemoryExamples.selfHLS.correct,
    ``IRComparison.FixedMemoryExamples.longHLS.correct,
    ``IRComparison.FixedMemoryExamples.shortHLS.correct,
    ``IRComparison.HybridWord.rangeCount_positive,
    ``IRComparison.HybridWord.rangeCount_negative,
    ``IRComparison.HybridWord.range_length,
    ``IRComparison.HybridIR.replaceLocal_get,
    ``IRComparison.HybridIR.Value.affineLocal_correct,
    ``IRComparison.HybridIR.ReadCode.affineLocal_correct,
    ``IRComparison.HybridIR.MemoryCmd.affineLocal_correct,
    ``IRComparison.WordLoopFacts.forStatic,
    ``IRComparison.CertifiedHLS.ProgramEntry.compile_correct,
    ``IRComparison.LeanTyped.numeral_value,
    ``IRComparison.WholeProgramExamples.filterHLS.correct,
    ``IRComparison.WholeProgramExamples.nestedHLS.correct,
    ``IRComparison.WholeProgramExamples.ascendingHLS.correct,
    ``IRComparison.WholeProgramExamples.descendingHLS.correct,
    ``IRComparison.WholeProgramExamples.emptyHLS.correct,
    ``IRComparison.WholeProgramExamples.wrappingHLS.correct,
    ``IRComparison.WholeProgramExamples.failingHLS.correct,
    ``IRComparison.WholeProgramExamples.largeHLS.correct,
    ``IRComparison.WholeProgramExamples.smallHLS.correct,

    ``IRComparison.ChannelCommandBridge.command_correct,
    ``IRComparison.Circuit.ChannelCounted.piece_correct,
    ``IRComparison.Circuit.ChannelCounted.round_correct,
    ``IRComparison.Circuit.ChannelCounted.fold_correct,
    ``IRComparison.Circuit.ChannelCounted.command_correct,
    ``IRComparison.Circuit.ChannelCounted.bounded_command,
    ``IRComparison.Circuit.ChannelCounted.lower_reference,
    ``IRComparison.Circuit.ChannelLower.bounded_congr,
    ``IRComparison.Circuit.ChannelLower.resources,
    ``IRComparison.Circuit.ChannelLower.frame_above,
    ``IRComparison.Circuit.CountedBackend.named,
    ``IRComparison.Circuit.prepareSymbolicWith_contract,
    ``IRComparison.Circuit.symbolicInstructions_correct_with,
    ``IRComparison.Circuit.symbolic_pipeline_schedule_with,
    ``IRComparison.Circuit.Pipelining.unified_schedule_correct_with,
    ``IRComparison.Circuit.Pipelining.optimized_schedule_correct_with,

    ``IRComparison.ChannelScope.value_correct,
    ``IRComparison.ChannelScope.read_correct,
    ``IRComparison.ChannelScope.body_correct,
    ``IRComparison.ChannelBuffers.capture_correct,
    ``IRComparison.ChannelBuffers.pop_correct,
    ``IRComparison.ChannelBuffers.take_correct,
    ``IRComparison.ChannelWindow.Load.correct,
    ``IRComparison.ChannelWindow.loads_correct,
    ``IRComparison.ChannelWindow.put_held,
    ``IRComparison.ChannelWindow.capture_held,
    ``IRComparison.Circuit.ChannelCounted.command_budget,
    ``IRComparison.HybridIR.ChannelCmd.ofMemory_correct,
    ``IRComparison.Circuit.ChannelLower.lower_correct,
    ``IRComparison.Circuit.ChannelLower.sendBudget_sound,
    ``IRComparison.Circuit.Pipelining.ClockTree.assemble_payload_finishes,
    ``IRComparison.HybridRoutingVC.accept_correct,
    ``IRComparison.HybridSymbolicGlobal.Plan.correct,
    ``IRComparison.HybridSymbolicGlobal.Program.correct,
    ``IRComparison.Circuit.symbolicReference_correct,
    ``IRComparison.Circuit.symbolicReference_execute,
    ``IRComparison.Circuit.counted_full_reference,
    ``IRComparison.Circuit.prepareSymbolic_contract,
    ``IRComparison.Circuit.symbolicInstructions_correct,
    ``IRComparison.Circuit.symbolic_pipeline_schedule,

    ``IRComparison.HybridRegions.ofStages_correct,
    ``IRComparison.HybridRegions.producer_loop,
    ``IRComparison.HybridRegions.producer_eval,
    ``IRComparison.Circuit.region_code_trim,
    ``IRComparison.Circuit.region_trim,
    ``IRComparison.Circuit.regions_trim,
    ``IRComparison.Circuit.trim_snapshot_above,
    ``IRComparison.Circuit.regionCode_extension,
    ``IRComparison.Circuit.regionCode_arrays,
    ``IRComparison.Circuit.regionCode_frame,
    ``IRComparison.Circuit.regionCode_correct,
    ``IRComparison.Circuit.regionsCode_correct,
    ``IRComparison.Circuit.regions_pipeline_schedule,

    ``IRComparison.Circuit.Pipelining.rotate_correct,
    ``IRComparison.Circuit.Pipelining.overlapLoop_correct,
    ``IRComparison.Circuit.Pipelining.overlapLoops_correct,
    ``IRComparison.Execution.Reaches.trans,
    ``IRComparison.Execution.Reaches.finite,
    ``IRComparison.Execution.Reaches.map,
    ``IRComparison.Circuit.ResultObservation.of_agreement,
    ``IRComparison.NativeLoop.forIn_lift,
    ``IRComparison.Circuit.Pipelining.sequential_text_correct,
    ``IRComparison.Circuit.Pipelining.Integrated.correct,
    ``IRComparison.CertifiedHLS.Entry.source_eq,
    ``IRComparison.CertifiedHLS.observation_of_public,
    ``IRComparison.CertifiedHLS.Compiled.correct,
    ``IRComparison.CertifiedHLS.compile_correct,
    ``IRComparison.CertifiedHLS.BodyEntry.compile_correct,
    ``IRComparison.CertifiedHLSExamples.filterHLS.correct,
    ``IRComparison.CertifiedHLSExamples.conditionalHLS.correct,
    ``IRComparison.CertifiedHLSExamples.producerHLS.correct,
    ``IRComparison.CertifiedHLSExamples.consumerHLS.correct,
    ``IRComparison.CertifiedHLSExamples.filter_to_rtl,
    ``IRComparison.Relational.consequence,
    ``IRComparison.Relational.seq,
    ``IRComparison.Relational.insertLeft,
    ``IRComparison.Relational.insertRight,
    ``IRComparison.Relational.insertion_succeeds,
    ``IRComparison.Relational.branch_rule,
    ``IRComparison.Relational.for_rule,
    ``IRComparison.Relational.for_with_refill_rule,
    ``IRComparison.Relational.result_eq,
    ``IRComparison.HybridSymbolicBody.Compiled.translation,
    ``IRComparison.HybridSymbolicLoop.Plan.initial_rule,
    ``IRComparison.HybridSymbolicLoop.Plan.body_rule,
    ``IRComparison.HybridSymbolicLoop.Plan.refill_rule,
    ``IRComparison.HybridSymbolicLoop.Plan.loop_rule,
    ``IRComparison.Relational.fold_rule,
    ``IRComparison.BufferRules.insertRead_rule,
    ``IRComparison.BufferRules.insertMemory_rule,
    ``IRComparison.WindowCoverage.emit_exists,
    ``IRComparison.BufferRules.insertMove_rule,
    ``IRComparison.BufferRules.readMem_rule,
    ``IRComparison.BufferRules.take_rule,
    ``IRComparison.BufferRules.take_eval,
    ``IRComparison.StreamState.writeMem_rule,
    ``IRComparison.StreamState.insertWrite_rule,
    ``IRComparison.StreamState.directSend_rule,
    ``IRComparison.HybridWindowRead.readMem_rule,
    ``IRComparison.HybridRules.seq,
    ``IRComparison.HybridRules.letValue,
    ``IRComparison.HybridRules.repeat_rule,
    ``IRComparison.HybridRules.forRange,
    ``IRComparison.HybridAlternatives.Compiled.translation,
    ``IRComparison.HybridAlternatives.sequence,
    ``IRComparison.HybridAlternatives.branch,
    ``IRComparison.Circuit.Pipelining.bundle_rule,
    ``IRComparison.Circuit.Pipelining.ControlTranslation.consequence,
    ``IRComparison.Circuit.Pipelining.ControlTranslation.seq,
    ``IRComparison.Circuit.Pipelining.ControlTranslation.branch,
    ``IRComparison.Circuit.Pipelining.ControlTranslation.loop,
    ``IRComparison.Circuit.Pipelining.scheduleStructure_rule,

    ``IRComparison.Circuit.Pipelining.scheduleStructure_correct,
    ``IRComparison.Circuit.Pipelining.ClockTree.layout_correct,
    ``IRComparison.Circuit.Pipelining.ClockTree.assemble_finishes,
    ``IRComparison.Circuit.Pipelining.scheduleStructure_finishes,
    ``IRComparison.Circuit.Pipelining.transferActions_sound,
    ``IRComparison.Circuit.Pipelining.ClockNode.transfer_sound,
    ``IRComparison.Circuit.Pipelining.clock_tick_table,
    ``IRComparison.Circuit.Pipelining.clockGraph_run_bound,
    ``IRComparison.Circuit.Pipelining.clockGraph_rtl_run,
    ``IRComparison.Circuit.Pipelining.structured_rtl_finishes,
    ``IRComparison.Circuit.Pipelining.checkGraph_sound,
    ``IRComparison.Circuit.Pipelining.graphModule_text,
    ``IRComparison.Circuit.Pipelining.physical_graph_tick,
    ``IRComparison.Circuit.Pipelining.physical_graph_run,
    ``IRComparison.Circuit.Pipelining.generated_graph_run,
    ``IRComparison.Circuit.Pipelining.compileStructured_correct,

    ``IRComparison.Circuit.Pipelining.rhl_swap,
    ``IRComparison.Circuit.Pipelining.reorder_sound,
    ``IRComparison.Circuit.Pipelining.prepare_correct,
    ``IRComparison.Circuit.expanded_pipeline_schedule,
    ``IRComparison.Circuit.compact_pipeline_schedule,
    ``IRComparison.Circuit.Pipelining.constantExpr_correct,
    ``IRComparison.Circuit.Pipelining.linearize_correct,
    ``IRComparison.Circuit.Pipelining.optimized_schedule_correct,
    ``IRComparison.Circuit.Pipelining.compileOptimizedScheduled_facts,
    ``IRComparison.Circuit.Pipelining.optimized_batches_correct,
    ``IRComparison.Circuit.Pipelining.compileOptimizedScheduled_correct,
    ``IRComparison.Circuit.Pipelining.Independent.ordered,
    ``IRComparison.Circuit.Pipelining.independent_bundle_safe,
    ``IRComparison.Circuit.Pipelining.ordered_bundle_rhl,
    ``IRComparison.Circuit.Pipelining.ordered_pair_rhl,
    ``IRComparison.Circuit.Pipelining.clock_rename,
    ``IRComparison.Circuit.Pipelining.reuse_correct,
    ``IRComparison.Circuit.Pipelining.allocated_word_correct,
    ``IRComparison.Circuit.Pipelining.batch_width_preserved,
    ``IRComparison.Circuit.Pipelining.lowerClock_bit_correct,
    ``IRComparison.Circuit.Pipelining.compiled_rtl_correct,
    ``IRComparison.Circuit.Pipelining.pipelineWord_rtl_correct,
    ``IRComparison.Circuit.Pipelining.realize_correct,
    ``IRComparison.Circuit.Pipelining.batchModule_text,
    ``IRComparison.Circuit.Pipelining.lowerClock_frame,
    ``IRComparison.Circuit.Pipelining.generateBatches_total,
    ``IRComparison.Circuit.Pipelining.physical_batch_tick,
    ``IRComparison.Circuit.Pipelining.physical_batches_run,
    ``IRComparison.Circuit.Pipelining.batchRun_bound,
    ``IRComparison.Circuit.Pipelining.checkBatch_sound,
    ``IRComparison.Circuit.Pipelining.generated_batch_run,
    ``IRComparison.Circuit.Pipelining.realized_rtl_correct,
    ``IRComparison.Circuit.Pipelining.pipelineWord_text_correct,
    ``IRComparison.Circuit.Pipelining.compileWordCircuit_correct,
    ``IRComparison.Circuit.Pipelining.independent_sound,
    ``IRComparison.Circuit.Pipelining.clock_correct,
    ``IRComparison.Circuit.Pipelining.compile_correct,
    ``IRComparison.Circuit.Pipelining.compile_rhl,
    ``IRComparison.Circuit.Pipelining.Loop.pipeline_rhl,
    ``IRComparison.Circuit.Pipelining.related_tick,
    ``IRComparison.Circuit.Pipelining.pipeline_finishes,
    ``IRComparison.Circuit.Pipelining.transform_correct,
    ``IRComparison.Circuit.Pipelining.materialize_correct,
    ``IRComparison.Circuit.Pipelining.pipelineCommands_correct,
    ``IRComparison.Circuit.Pipelining.pipelineWord_correct,
    ``IRComparison.Circuit.Pipelining.pipelineWord_finishes,
    ``IRComparison.PipeliningExamples.filterCode.wordBody_correct,
    ``IRComparison.PipeliningExamples.gatherCode.wordBody_correct,
    ``IRComparison.Circuit.initialized_queue_bound,
    ``IRComparison.Circuit.blocks_correct,
    ``IRComparison.Circuit.boundedBlocks_eq,
    ``IRComparison.Circuit.take_correct,
    ``IRComparison.Circuit.expandedLoads_correct,
    ``IRComparison.Circuit.layoutCovers_sound,
    ``IRComparison.Circuit.value_correct,
    ``IRComparison.Circuit.read_correct,
    ``IRComparison.Circuit.Schedule.layout_correct,
    ``IRComparison.Circuit.Schedule.assemble_finishes,
    ``IRComparison.Circuit.tailCode_finishes,
    ``IRComparison.Circuit.rootCode_correct,
    ``IRComparison.Circuit.compact_pipeline_finishes,
    ``IRComparison.Circuit.unified_compact_finishes,
    ``IRComparison.Circuit.QueueWellFormed.covers,
    ``IRComparison.Circuit.command_trim,
    ``IRComparison.Circuit.compactLoads_correct,
    ``IRComparison.Circuit.copies_correct,
    ``IRComparison.Circuit.prepareCounted_parts,
    ``IRComparison.Circuit.counted_correct,
    ``IRComparison.Circuit.countedFold_eq,
    ``IRComparison.Circuit.duplex_static_correct,
    ``IRComparison.Circuit.producer_static_correct,
    ``IRComparison.Circuit.receiver_correct,
    ``IRComparison.Circuit.sendBound_sound,
    ``IRComparison.Circuit.sendBound_memory,
    ``IRComparison.Circuit.blocksBudget_sound,
    ``IRComparison.Circuit.counted_resources,
    ``IRComparison.Circuit.counted_frame,
    ``IRComparison.Circuit.checkSendBudgets_sound,
    ``IRComparison.Circuit.command_frame,
    ``IRComparison.Circuit.command_correct,
    ``IRComparison.Circuit.bounded_eq,
    ``IRComparison.Circuit.command_finishes,
    ``IRComparison.Circuit.Expr.bitEval_correct,
    ``IRComparison.Circuit.verilogDivision_correct,
    ``IRComparison.Circuit.reachable_widths,
    ``IRComparison.Circuit.Checked.execution,
    ``IRComparison.Circuit.FIFO.push_correct,
    ``IRComparison.Circuit.FIFO.pop_correct,

    ``IRComparison.ClockedComponent.tick_wellFormed,
    ``IRComparison.ClockedComponent.tick_conservation,
    ``IRComparison.ClockedComponent.run_conservation,
    ``IRComparison.ClockedComponent.results_correct,
    ``IRComparison.ClockedComponent.drained_trace_correct,
    ``IRComparison.ClockedComponent.request_finishes,
    ``IRComparison.ClockedComponent.response_stall,
    ``IRComparison.ClockedComponent.retire_once,
    ``IRComparison.ClockedOperation.finishes,
    ``IRComparison.ClockedOperation.offer_preserves,
    ``IRComparison.WordComponent.Op.lower_correct,
    ``IRComparison.WordComponent.finishes_mixed,
    ``IRComparison.WordComponent.controlled_finishes,
    ``IRComparison.HybridWord.Expr.lower_correct_int,
    ``IRComparison.HybridWord.Cmd.lower_correct_int,
    ``IRComparison.HybridWord.iterate_correct,
    ``IRComparison.HybridWord.compile_correct,
    ``IRComparison.HybridWord.optimized_control_finishes,
    ``IRComparison.HybridWord.source_correct,
    ``IRComparison.HybridWord.program_correct,
    ``IRComparison.HybridWord.program_finishes,
    ``IRComparison.WordFrontend.Result.correct,
    ``IRComparison.WordFrontendExamples.producer.wordBody_correct,
    ``IRComparison.WordFrontendExamples.consumer.wordBody_correct,
    ``IRComparison.WordFrontendExamples.loopCode.wordBody_correct,
    ``IRComparison.WordFrontendExamples.capturedCode.wordBody_correct,
    ``IRComparison.VersionedHybrid.ofFunctional_correct,
    ``IRComparison.VersionedAllocation.lower_correct,
    ``IRComparison.VersionedStorage.lower_correct,
    ``IRComparison.VersionedPlacement.compile,
    ``IRComparison.VersionedWindowBody.compile,
    ``IRComparison.VersionedLoop.Plan.correct,
    ``IRComparison.VersionedLoop.Selected.correct,
    ``IRComparison.VersionedFIFO.Plan.correct,
    ``IRComparison.VersionedMemoryMachine.correct,
    ``IRComparison.VersionedFIFOMachine.correct,
    ``IRComparison.VersionedOrder.early,
    ``IRComparison.VersionedOrder.late,
    ``IRComparison.VersionedOrder.materialize_correct,
    ``IRComparison.VersionedOrder.orders_agree,
    ``IRComparison.VersionedOrderControl.artifact_finishes,
    ``IRComparison.VersionedOrderExamples.filter.versionedBody_correct,
    ``IRComparison.VersionedOrderExamples.filter.early_correct,
    ``IRComparison.VersionedOrderExamples.filter.late_correct,
    ``IRComparison.VersionedOrderExamples.previous.versionedBody_correct,
    ``IRComparison.VersionedOrderExamples.threeVersions.late_correct,
    ``IRComparison.VersionedOrderExamples.returnOld.late_correct,
    ``IRComparison.VersionedOrderExamples.selected.late_correct,
    ``IRComparison.VersionedOrderExamples.oldOther.late_correct,
    ``IRComparison.HybridAffine.value_correct,
    ``IRComparison.HybridAffine.read_correct,
    ``IRComparison.HybridSymbolicRead.compile,
    ``IRComparison.HybridSymbolicBody.compile,
    ``IRComparison.HybridSymbolicLoop.Plan.correct,
    ``IRComparison.HybridSymbolicLoop.Selected.correct,
    ``IRComparison.HybridSymbolicProducer.compile,
    ``IRComparison.HybridSymbolicProducerLoop.Plan.correct,
    ``IRComparison.HybridCompactFIFO.Plan.correct,
    ``IRComparison.HybridCompactTransport.SolverSelection.correct,
    ``IRComparison.HybridCompactStage.Clear.correct,
    ``IRComparison.HybridCompactChainEmit.Plan.correct,
    ``IRComparison.HybridCompactChain.Plan.correct,
    ``IRComparison.HybridSymbolicWindowControl.correct,
    ``IRComparison.HybridSymbolicProducerControl.correct,
    ``IRComparison.HybridCompactFIFOControl.correct,
    ``IRComparison.HybridCompactDuplexControl.correct,
    ``IRComparison.HybridCompactChainControl.plan_finishes,
    ``IRComparison.HybridUnifiedPipeline.Plan.correct,
    ``IRComparison.HybridUnifiedPipeline.plan_finishes,
    ``IRComparison.HybridCompactExamples.native_correct,
    ``IRComparison.HybridCompactExamples.taps.hybridCompactWindow_correct,
    ``IRComparison.HybridIR.extract_correct,
    ``IRComparison.HybridIR.MemoryCmd.fromImperative_correct,
    ``IRComparison.HybridIR.MemoryCmd.target_correct,
    ``IRComparison.HybridAddress.value_correct,
    ``IRComparison.HybridAddress.read_correct,
    ``IRComparison.HybridWindowRead.compile,
    ``IRComparison.HybridWindowBody.compile,
    ``IRComparison.HybridWindowPlan.Plan.blocks_correct,
    ``IRComparison.HybridWindowTransport.Selected.correct,
    ``IRComparison.HybridStage.eval_correct,
    ``IRComparison.HybridSafety.read_correct,
    ``IRComparison.HybridShapes.stage_same,
    ``IRComparison.HybridEffects.stage_preserves,
    ``IRComparison.HybridSender.compile,
    ``IRComparison.HybridAlternatives.compile,
    ``IRComparison.HybridRouting.Blocks.eval_correct,
    ``IRComparison.HybridProducerBlocks.compile,
    ``IRComparison.HybridGlobal.Plan.correct,
    ``IRComparison.HybridGlobal.Program.correct,
    ``IRComparison.HybridInputs.WindowWorkloads.filterCode.hybridBody_correct,
    ``IRComparison.HybridIR.memoryBlocks_correct,
    ``IRComparison.HybridIR.lower_correct,
    ``IRComparison.HybridIR.Program.correct,
    ``IRComparison.HybridIR.kernels_correct,
    ``IRComparison.HybridCommandControl.correct,
    ``IRComparison.HybridBlocksControl.correct,
    ``IRComparison.HybridControl.correct,
    ``IRComparison.HybridControl.program_finishes,``IRComparison.GlobalEffects.body_preserves,
    ``IRComparison.GlobalEffects.stage_preserves,
    ``IRComparison.GlobalPipeline.Plan.correct,
    ``IRComparison.GlobalPipeline.Program.correct,
    ``IRComparison.GlobalPipelineControl.correct,
    ``IRComparison.GlobalPipelineControl.program_finishes,
    ``IRComparison.CompactDuplex.compile,
    ``IRComparison.CompactDuplex.Plan.routing_correct,
    ``IRComparison.CompactChainEmit.Plan.correct,
    ``IRComparison.CompactChain.compile,
    ``IRComparison.CompactChain.Plan.correct,
    ``IRComparison.CompactChainControl.plan_finishes,
    ``IRComparison.UnifiedPipeline.compile,
    ``IRComparison.UnifiedPipeline.compileWithSMT,
    ``IRComparison.UnifiedPipeline.Plan.correct,
    ``IRComparison.UnifiedPipeline.plan_finishes,
    ``IRComparison.UnifiedPipelineExamples.both_correct,
    ``IRComparison.AlternativeProducerBlocks.compile,
    ``IRComparison.AlternativeStageFusion.compile,
    ``IRComparison.AlternativeStageFusion.Plan.correct,
    ``IRComparison.AlternativePipelineExamples.native_correct,
    ``IRComparison.SymbolicProducer.compile,
    ``IRComparison.SymbolicProducerLoop.compile,
    ``IRComparison.SymbolicProducerLoop.Plan.correct,
    ``IRComparison.CompactFusion.compile,
    ``IRComparison.CompactFusion.candidateReceiver,
    ``IRComparison.CompactFusion.Selected.correct,
    ``IRComparison.CompactFusionControl.plan_finishes,
    ``IRComparison.CompactFusionExamples.native_correct,
    ``IRComparison.StreamChainEmit.compile,
    ``IRComparison.StreamChainEmit.Plan.correct,
    ``IRComparison.StreamChain.compile,
    ``IRComparison.StreamChain.Plan.correct,
    ``IRComparison.PipelineCompiler.compile_correct,
    ``IRComparison.PipelineCompilerControl.compile_finishes,
    ``IRComparison.StreamChainExamples.both_correct,
    ``IRComparison.CompactRouting.compile,
    ``IRComparison.CompactFIFO.compile,
    ``IRComparison.CompactFIFO.Plan.correct,
    ``IRComparison.CompactTransport.select,
    ``IRComparison.CompactTransport.SolverSelection.correct,
    ``IRComparison.CompactFIFOControl.plan_finishes,
    ``IRComparison.CompactFIFOExamples.native_correct,
    ``IRComparison.StreamAlternatives.compile,
    ``IRComparison.AlternativeRouting.compile,
    ``IRComparison.AlternativeRouting.Blocks.eval_correct,
    ``IRComparison.AlternativeFusion.compile,
    ``IRComparison.AlternativeFusion.Plan.correct,
    ``IRComparison.AlternativeExamples.native_correct,
    ``IRComparison.CompactSequence.response_sound,
    ``IRComparison.CompactSequence.accept,
    ``IRComparison.AffineAddress.parse,
    ``IRComparison.AffineAddress.checkGuards_sound,
    ``IRComparison.SymbolicWindowBody.compile,
    ``IRComparison.SymbolicWindowLoop.compile,
    ``IRComparison.SymbolicWindowLoop.Plan.correct,
    ``IRComparison.SymbolicWindowLoop.Selected.correct,
    ``IRComparison.FunctionalSymbolicLoop.compile,
    ``IRComparison.FunctionalSymbolicLoop.Artifact.correct,
    ``IRComparison.FunctionalSymbolicLoop.select,
    ``IRComparison.SymbolicWindowControl.correct,
    ``IRComparison.SymbolicWindowControl.plan_finishes,
    ``IRComparison.SymbolicWindowExamples.native_correct,
    ``IRComparison.SymbolicWindowExamples.routes_agree,
    ``IRComparison.PipelineShapes.body_same,
    ``IRComparison.PipelineShapes.blocks_same,
    ``IRComparison.PipelineShapes.stage_same,
    ``IRComparison.PipelineUse.checkBodies,
    ``IRComparison.PipelineUse.checkStage,
    ``IRComparison.PipelineUse.checkTail,
    ``IRComparison.PipelineUse.StageClear.source,
    ``IRComparison.PipelineUse.Clear.ready,
    ``IRComparison.PipelineUse.Clear.source,
    ``IRComparison.PipelineUse.observe_erase,
    ``IRComparison.AutoPipeline.compile,
    ``IRComparison.AutoPipeline.Plan.correct,
    ``IRComparison.AutoPipeline.compile_correct,
    ``IRComparison.AutoPipelineControl.lower_correct,
    ``IRComparison.AutoPipelineControl.correct,
    ``IRComparison.AutoPipelineControl.compile_finishes,
    ``IRComparison.AutoPipelineExamples.pipeline_correct,
    ``IRComparison.AutoPipelineExamples.two_routes_agree,

    ``IRComparison.StreamFusion.Plan.observe_correct,
    ``IRComparison.StreamFusionExamples.public_output_correct,
    ``IRComparison.WindowPipeline.Stage.rebase,
    ``IRComparison.StreamState.expr_correct,
    ``IRComparison.StreamState.write_output,
    ``IRComparison.StreamState.Related.send,
    ``IRComparison.StreamState.Related.write_other,
    ``IRComparison.StreamProducer.sequence,
    ``IRComparison.StreamProducer.compile,
    ``IRComparison.StreamConsumer.check,
    ``IRComparison.StreamConsumer.checkBlocks,
    ``IRComparison.StreamConsumer.Closed.correct,
    ``IRComparison.StreamProducerBlocks.compile,
    ``IRComparison.StreamFusion.compile,
    ``IRComparison.StreamFusion.select,
    ``IRComparison.StreamFusion.Plan.correct,
    ``IRComparison.StreamFusion.Selected.correct,
    ``IRComparison.FIFOReadControl.correct,
    ``IRComparison.StreamProducerControl.correct,
    ``IRComparison.StreamProducerControl.finishes,
    ``IRComparison.StreamBlocksControl.correct,
    ``IRComparison.StreamBlocksControl.finishes,
    ``IRComparison.StreamFusionControl.correct,
    ``IRComparison.StreamFusionControl.plan_finishes,
    ``IRComparison.StreamFusionExamples.whole_region,

    ``IRComparison.NativeWindowExamples.taps.windows_agree,
    ``IRComparison.NativeWindowExpr.compile,
    ``IRComparison.NativeWindowBody.compile,
    ``IRComparison.NativeWindowPlan.prepareWith,
    ``IRComparison.NativeWindowPlan.compile,
    ``IRComparison.WindowFIFO.route,
    ``IRComparison.WindowTransport.route,
    ``IRComparison.WindowTransport.compile,
    ``IRComparison.FunctionalWindowBody.compile,
    ``IRComparison.FunctionalWindowPlan.prepare,
    ``IRComparison.FunctionalWindowPlan.compile,
    ``IRComparison.WindowPipeline.Stage.queue_ready,
    ``IRComparison.WindowPipeline.Stage.eval_correct,
    ``IRComparison.WindowPipeline.Stage.finishes,
    ``IRComparison.WindowPipeline.imperative,
    ``IRComparison.WindowPipeline.functional,
    ``IRComparison.WindowPipeline.eval_correct,
    ``IRComparison.NativeWindowExamples.taps.imperativeWindow_correct,
    ``IRComparison.NativeWindowExamples.taps.functionalWindow_correct,
    ``IRComparison.NativeWindowExamples.taps.imperativeWindow_finishes,
    ``IRComparison.NativeWindowExamples.taps.functionalWindow_finishes,

    ``IRComparison.WindowSchedule.loads_correct,
    ``IRComparison.WindowSchedule.emit_matches,
    ``IRComparison.WindowCoverage.array_covered,
    ``IRComparison.WindowCoverage.emit_exists,
    ``IRComparison.NativeWindowExpr.address_correct,
    ``IRComparison.NativeWindowBody.write_other,
    ``IRComparison.NativeWindowPlan.Plan.imperative_correct,
    ``IRComparison.NativeWindowPlan.Plan.functional_correct,
    ``IRComparison.WindowFIFO.Routes.correct,
    ``IRComparison.WindowTransport.Routes.correct,
    ``IRComparison.WindowTransport.Selected.correct,
    ``IRComparison.WindowTransport.Selected.code_correct,
    ``IRComparison.WindowControl.lower_finishes,
    ``IRComparison.WindowControl.selected_finishes,
    ``IRComparison.FunctionalWindowPlan.Plan.functional_correct,
    ``IRComparison.FunctionalWindowPlan.Plan.allocated_correct,
    ``IRComparison.FunctionalWindowPlan.Artifact.correct,
    ``IRComparison.FunctionalWindowPlan.Artifact.finishes,

    ``IRComparison.CommunicationIR.plan,
    ``IRComparison.CommunicationIR.step_correct,
    ``IRComparison.CommunicationIR.run_correct,
    ``IRComparison.CommunicationIR.selected_correct,
    ``IRComparison.CommunicationIR.Transport.execute_correct,
    ``IRComparison.CommunicationIR.compileOptimized_finishes,
    ``IRComparison.CommunicationIR.emit_correct,
    ``IRComparison.CommunicationIR.compileImperative_finishes,
    ``IRComparison.CommunicationIR.FunctionalArtifact.finishes,
    ``IRComparison.CommunicationExamples.native_filter_finishes,
    ``IRComparison.CommunicationExamples.snapshot_body_finishes,

    ``IRComparison.VersionFacts.capturedLoop,
    ``IRComparison.LeanVersionBody.loop,
    ``IRComparison.SnapshotLoopExamples.captured.functional_correct,
    ``IRComparison.SnapshotLoopExamples.captured.imperativeControl_correct,
    ``IRComparison.SnapshotLoopExamples.captured.functionalControl_correct,
    ``IRComparison.SnapshotLoopExamples.captured.imperativeOptimizedControl_correct,
    ``IRComparison.SnapshotLoopExamples.captured.functionalOptimizedControl_correct,
    ``IRComparison.SnapshotLoopExamples.nested.functional_correct,
    ``IRComparison.SnapshotLoopExamples.nested.imperativeControl_correct,
    ``IRComparison.SnapshotLoopExamples.nested.functionalControl_correct,
    ``IRComparison.SnapshotLoopExamples.nested.imperativeOptimizedControl_correct,
    ``IRComparison.SnapshotLoopExamples.nested.functionalOptimizedControl_correct,
    ``IRComparison.SnapshotLoopExamples.dynamic.functional_correct,
    ``IRComparison.SnapshotLoopExamples.dynamic.imperativeControl_correct,
    ``IRComparison.SnapshotLoopExamples.dynamic.functionalControl_correct,
    ``IRComparison.SnapshotLoopExamples.dynamic.imperativeOptimizedControl_correct,
    ``IRComparison.SnapshotLoopExamples.dynamic.functionalOptimizedControl_correct,

    ``IRComparison.SnapshotIR.lower_correct,
    ``IRComparison.SnapshotControlIR.lower_correct,
    ``IRComparison.SnapshotControlIR.lower_finishes,
    ``IRComparison.SnapshotControlIR.functional_finishes,
    ``IRComparison.ControlIR.snapshots_correct,
    ``IRComparison.ControlIR.lowerVersions_finishes,
    ``IRComparison.ProgramControlIR.readRepeat_generic,
    ``IRComparison.ProgramControlIR.bufferedRepeat_generic,
    ``IRComparison.ProgramControlIR.body_from_finishes,
    ``IRComparison.ProgramControlIR.optimizedBody_finishes,
    ``IRComparison.LeanVersionBody.compile,
    ``IRComparison.LeanVersionEntry.compile,
    ``IRComparison.LeanArrayNormalization.compile,
    ``IRComparison.ArrayNormalizationFacts.identity,
    ``IRComparison.ArrayNormalizationFacts.fuse,
    ``IRComparison.ArrayNormalizationFacts.result,
    ``IRComparison.VersionFacts.lookupZero,
    ``IRComparison.VersionFacts.lookupSucc,
    ``IRComparison.VersionFacts.yieldSome,
    ``IRComparison.VersionFacts.yieldPure,
    ``IRComparison.VersionFacts.store,
    ``IRComparison.VersionFacts.storeLiteral,
    ``IRComparison.VersionFacts.bind,
    ``IRComparison.VersionFacts.capture,
    ``IRComparison.VersionFacts.branch,

    ``IRComparison.ProgramLowering.lower_correct,
    ``IRComparison.ProgramControlIR.lift_steps, ``IRComparison.ProgramControlIR.body_correct,
    ``IRComparison.ProgramControlIR.readRepeat_correct, ``IRComparison.ProgramControlIR.bufferedRepeat_correct,
    ``IRComparison.ProgramControlIR.lower_correct, ``IRComparison.ProgramControlIR.lower_finishes,
    ``IRComparison.ProgramControlIR.lowerFunctional_finishes, 
    ``IRComparison.ProgramControlIR.result_unique, ``IRComparison.ProgramControlIR.optimized_finishes,
    ``IRComparison.ProgramControlIR.optimized_result_correct,
    ``IRComparison.ProgramControlIR.optimizedFunctional_finishes,
    ``IRComparison.ProgramControlIR.optimizedFunctional_result_correct,
    ``IRComparison.ProgramControlIR.lower_optimizedLoop,
    ``IRComparison.ProgramControlIR.lowerFunctional_optimizedLoop,
    ``IRComparison.OptimizedControlExamples.filtered.imperativeOptimizedControl_correct,
    ``IRComparison.OptimizedControlExamples.filtered.functionalOptimizedControl_correct,
    ``IRComparison.OptimizedControlExamples.filtered.imperativeOptimizedControl_result_correct,
    ``IRComparison.OptimizedControlExamples.filtered.functionalOptimizedControl_result_correct,
    ``IRComparison.OptimizedControlExamples.filter_controls_agree,
    ``IRComparison.OptimizedControlExamples.accumulate_controls_agree,
    ``IRComparison.OptimizedControlExamples.branch_controls_agree,

    ``IRComparison.LeanSourceToIR.beta, ``IRComparison.LeanSourceToIR.knownValue,
    ``IRComparison.LeanStructuralConversion.prove, ``IRComparison.LeanStructuralConversion.conversion,
    ``IRComparison.ArrayIR.fold_map, ``IRComparison.ArrayIR.map_total,
    ``IRComparison.ArrayIR.imperative_correct, ``IRComparison.ArrayIR.functional_correct,
    ``IRComparison.LeanArrayEntry.compile,
    ``IRComparison.BoundedReadIR.imperative_correct, ``IRComparison.BoundedReadIR.functional_correct,
    ``IRComparison.LeanBoundedReadEntry.compile,
    ``IRComparison.LoopFacts.forIn_lift, ``IRComparison.LoopFacts.imperative, ``IRComparison.LoopFacts.functional,
    ``IRComparison.LeanLoopNormalization.compile, ``IRComparison.LeanLoopNormalization.beta,
    ``IRComparison.LeanSourceBody.loop, ``IRComparison.ControlIR.range_correct,
    ``IRComparison.ReadFacts.natural, ``IRComparison.ReadFacts.naturalA,
    ``IRComparison.ReadHoistingFacts.commute, ``IRComparison.ReadHoistingFacts.transport,
    ``IRComparison.LeanReadHoisting.compile, ``IRComparison.LeanSourceBody.hoisted,
    ``IRComparison.ArrayControlIR.mapping_correct, ``IRComparison.ArrayControlIR.imperative_correct,
    ``IRComparison.ArrayControlIR.functional_correct, ``IRComparison.ArrayControlIR.load_correct,
    ``IRComparison.ArrayControlIR.imperative_get_correct, ``IRComparison.ArrayControlIR.functional_get_correct,
    ``IRComparison.OldReadEntryExamples.saved.imperativeControl_correct,
    ``IRComparison.OldReadEntryExamples.saved.functionalControl_correct,

    ``IRComparison.ControlWorkloads.helper_eq_expanded,
    ``IRComparison.ControlWorkloads.squaredDistance_symmetric,
    ``IRComparison.ControlWorkloads.distance_controller_symmetric,

    ``IRComparison.StateLowering.lower_correct,
    ``IRComparison.ControlIR.lower_correct,
    ``IRComparison.ControlIR.lower_finishes,
    ``IRComparison.ControlIR.lowerFunctional_finishes,
    
    ``IRComparison.ControlIR.result_unique,
    ``IRComparison.ControlIR.lower_result_correct,

    ``IRComparison.LeanTypeReduction.conversion,
    ``IRComparison.ScopedFacts.literal, ``IRComparison.ScopedFacts.index,
    ``IRComparison.ScopedFacts.left, ``IRComparison.ScopedFacts.right,
    ``IRComparison.ScopedFacts.localZero, ``IRComparison.ScopedFacts.localSucc,
    ``IRComparison.ScopedFacts.natIndex,
    ``IRComparison.ScopedFacts.add, ``IRComparison.ScopedFacts.sub,
    ``IRComparison.ScopedFacts.mul, ``IRComparison.ScopedFacts.div, ``IRComparison.ScopedFacts.select,
    ``IRComparison.ReadFacts.literal, ``IRComparison.ReadFacts.literalA,
    ``IRComparison.ReadFacts.literalN, ``IRComparison.ReadFacts.literalAN,
    ``IRComparison.ReadFacts.dynamic, ``IRComparison.ReadFacts.dynamicA,
    ``IRComparison.BodyFacts.letImperative, ``IRComparison.BodyFacts.letFunctional,
    ``IRComparison.LeanSourceBody.readInputs, ``IRComparison.LeanSourceBody.read,
    ``IRComparison.LeanSourceBody.readBinding,

    ``IRComparison.BodyFacts.seqImperative,
    ``IRComparison.BodyFacts.seqFunctional,
    ``IRComparison.BodyFacts.skipImperative,
    ``IRComparison.BodyFacts.skipFunctional,
    ``IRComparison.BodyFacts.returnImperative,
    ``IRComparison.BodyFacts.returnFunctional,
    ``IRComparison.LeanSourceBody.nextInputs,
    ``IRComparison.LeanSourceBody.sequence,
    ``IRComparison.LeanSourceBody.returnState,
    ``IRComparison.LeanSourceToIR.boundVariable,
    ``IRComparison.LeanBodyQuotation.imperative_represents,
    ``IRComparison.LeanBodyQuotation.functional_represents,
    ``IRComparison.LeanBodyQuotation.result_congr,
    ``IRComparison.BodyFacts.storeImperative,
    ``IRComparison.BodyFacts.storeFunctional,
    ``IRComparison.BodyFacts.storeImperativeLiteral,
    ``IRComparison.BodyFacts.storeFunctionalLiteral,
    ``IRComparison.BodyFacts.branchImperative,
    ``IRComparison.BodyFacts.branchFunctional,
    ``IRComparison.LeanSourceBody.store,
    ``IRComparison.LeanSourceBody.branch,
    ``IRComparison.LeanSourceBody.letValue,
    ``IRComparison.LeanSourceBody.compile,
    ``IRComparison.LeanNamedBody.parameters,
    ``IRComparison.LeanNamedBody.compile,
    ``IRComparison.LeanNamedBody.close_correct,
    ``IRComparison.BodyBackends.imperative_correct,
    ``IRComparison.BodyBackends.functional_correct,
    ``IRComparison.LeanBodyPipeline.compile,
    ``IRComparison.LeanBodyPipeline.Result.correct,
    ``IRComparison.LeanLibrary.Declaration.install_faithful,
    ``IRComparison.LeanLibrary.installTypes_faithful,
    ``IRComparison.LeanLibrary.installTypes_no_equations,
    ``IRComparison.LeanEnvironmentProvenance.alias_equation,
    ``IRComparison.LeanEnvironmentProvenance.install_definition,
    ``IRComparison.LeanEnvironmentProvenance.install_alias,
    ``IRComparison.LeanEnvironmentProvenance.install_types,
    ``IRComparison.LeanEntryEnvironment.load,
    ``IRComparison.LeanEntryEnvironment.compile,
    ``IRComparison.LeanNamedScalar.result_congr,
    ``IRComparison.LeanNamedScalar.compile,
    ``IRComparison.LeanNamedScalar.Result.closed_correct,
    ``IRComparison.LeanProofApplication.constant,
    ``IRComparison.LeanProofApplication.apply,
    ``IRComparison.ScalarBackends.imperative_correct,
    ``IRComparison.ScalarBackends.functional_correct,
    ``IRComparison.LeanScalarPipeline.compile,
    ``IRComparison.LeanScalarPipeline.Result.correct,
    ``IRComparison.LeanCertificate.level_roundtrip,
    ``IRComparison.LeanCertificate.expression_represents,
    ``IRComparison.LeanCertificate.declaration,
    ``IRComparison.LeanLiteralNormalization.elaboratedFact,
    ``IRComparison.LeanLiteralNormalization.apply_literal,
    ``IRComparison.LeanLiteralNormalization.apply_elaborated,
    ``IRComparison.LeanNegNormalization.coreFact,
    ``IRComparison.LeanNegNormalization.surfaceFact,
    ``IRComparison.LeanNegNormalization.apply_neg,
    ``IRComparison.LeanSourceEntry.load,
    ``IRComparison.LeanSourceEntry.represents_original,
    ``IRComparison.LeanSourceEntry.Header.represents_function,
    ``IRComparison.LeanSourceEntry.Header.represents_type,
    ``IRComparison.LeanIRQuotation.code_represents,
    ``IRComparison.LeanIRQuotation.Facts.literal,
    ``IRComparison.LeanIRQuotation.Facts.index,
    ``IRComparison.LeanIRQuotation.Facts.left,
    ``IRComparison.LeanIRQuotation.Facts.right,
    ``IRComparison.LeanIRQuotation.Facts.add,
    ``IRComparison.LeanIRQuotation.Facts.sub,
    ``IRComparison.LeanIRQuotation.Facts.mul,
    ``IRComparison.LeanIRQuotation.Facts.div,
    ``IRComparison.LeanIRQuotation.Facts.select,
    ``IRComparison.LeanIREvaluation.apply_literal,
    ``IRComparison.LeanIREvaluation.apply_slot,
    ``IRComparison.LeanIREvaluation.apply_binary,
    ``IRComparison.LeanIRSelect.apply_select,
    ``IRComparison.LeanIREvaluationCompiler.literal,
    ``IRComparison.LeanIREvaluationCompiler.slot,
    ``IRComparison.LeanIREvaluationCompiler.binary,
    ``IRComparison.LeanIREvaluationCompiler.select,
    ``IRComparison.LeanIREvaluationCompiler.compile,
    ``IRComparison.LeanIREvaluationCompiler.compile_correct,
    ``IRComparison.LeanSelectBridge.fact,
    ``IRComparison.LeanSelectBridge.apply_fact,
    ``IRComparison.LeanSelectBridge.represents,
    ``IRComparison.LeanSourceToIR.normalized,
    ``IRComparison.LeanSourceToIR.branch,
    ``IRComparison.LeanSourceToIR.letValue,
    ``IRComparison.LeanSourceToIR.binary,
    ``IRComparison.LeanSourceToIR.negative,
    ``IRComparison.LeanSourceToIR.compile,
    ``IRComparison.LeanIRTransport.transport,
    ``IRComparison.LeanIRTransport.apply_transport,
    ``IRComparison.LeanIRTransport.connect,
    ``IRComparison.LeanCertifiedScalar.parameters,
    ``IRComparison.LeanCertifiedScalar.compile,
    ``IRComparison.LeanCertifiedScalar.Result.correct,
    ``IRComparison.LeanLetNormalization.equality_congr,
    ``IRComparison.LeanLetNormalization.let_proof,
    ``IRComparison.LeanLetNormalization.normalize,
    ``IRComparison.LeanLetNormalization.unchangedOrArithmetic,
    ``IRComparison.LeanLetNormalization.Result.compose,
    ``IRComparison.LeanLetNormalization.leading,
    ``IRComparison.LeanLetNormalization.Result.compilers_agree,
    ``IRComparison.LeanFunctionNormalization.instantiate_typed,
    ``IRComparison.LeanFunctionNormalization.instantiate_equality,
    ``IRComparison.LeanFunctionNormalization.apply_normalization,
    ``IRComparison.LeanFunctionNormalization.named_application,
    ``IRComparison.LeanUniverseConversion.closed_eval,
    ``IRComparison.LeanUniverseConversion.conversion,
    ``IRComparison.LeanTypeReduction.load,
    ``IRComparison.LeanTypeReduction.Definition.source,
    ``IRComparison.LeanTypeReduction.Definition.install_ordered,
    ``IRComparison.LeanTypeReduction.Definition.unfold,
    ``IRComparison.LeanTypeReduction.unfoldConstant,
    ``IRComparison.LeanTypeReduction.step,
    ``IRComparison.LeanTypeReduction.reduce,
    ``IRComparison.LeanTypeReduction.expose,
    ``IRComparison.LeanTypeInference.inferWith,
    ``IRComparison.LeanTypeInference.checkWith,
    ``IRComparison.LeanTypeAliases.load,
    ``IRComparison.LeanTypeAliases.Alias.source,
    ``IRComparison.LeanTypeAliases.Alias.install_ordered,
    ``IRComparison.LeanTypeAliases.Alias.reduce,
    ``IRComparison.LeanTypeAliases.Alias.expand,
    ``IRComparison.LeanTypeAliases.Alias.conversion,
    ``IRComparison.LeanTypeInference.infer,
    ``IRComparison.LeanTypeInference.checkReady,
    ``IRComparison.LeanTypeInference.normalize,
    ``IRComparison.LeanTypeInference.infer_sound,
    ``IRComparison.LeanTypeInference.check_sound,
    ``IRComparison.LeanTypeInference.Result.correct,
    ``IRComparison.LeanTypeInference.normalize_correct,
    ``IRComparison.LeanLibrary.translate,
    ``IRComparison.LeanLibrary.load,
    ``IRComparison.LeanLibrary.Declaration.installed,
    ``IRComparison.LeanArithmeticNormalization.Plan.represents_source,
    ``IRComparison.LeanArithmeticNormalization.Plan.represents_normalized,
    ``IRComparison.LeanArithmeticNormalization.Plan.preserves_denotes,
    ``IRComparison.LeanArithmeticNormalization.Plan.compilers_agree,
    ``IRComparison.LeanArithmeticNormalization.Plan.correct,
    ``IRComparison.LeanArithmeticNormalization.plan_correct,
    ``IRComparison.LeanTyped.apply_refl,
    ``IRComparison.LeanTyped.apply_trans,
    ``IRComparison.LeanTyped.apply_congr,
    ``IRComparison.LeanTyped.composeBinary_correct,
    ``IRComparison.LeanTyped.FixedFact.installed,
    ``IRComparison.LeanTyped.Standard.intRefl,
    ``IRComparison.LeanTyped.Standard.intTrans,
    ``IRComparison.LeanTyped.Standard.intCongr,
    ``IRComparison.LeanArithmetic.BinaryArtifact.children_correct,
    ``IRComparison.LeanScalar.compile_surfaceBinary,
    ``IRComparison.LeanArithmetic.OperatorFact.apply,
    ``IRComparison.LeanArithmetic.BinaryArtifact.same_compiler,
    ``IRComparison.LeanArithmetic.BinaryArtifact.represents_source,
    ``IRComparison.LeanArithmetic.BinaryArtifact.normalization_correct,
    ``IRComparison.LeanArithmetic.BinaryArtifact.code_value,
    ``IRComparison.LeanArithmetic.compileBinary_correct,
    ``IRComparison.LeanTyped.intLambdas_congr,
    ``IRComparison.LeanTyped.applications_congr,
    ``IRComparison.LeanTyped.applications_beta,
    ``IRComparison.LeanTyped.appliedBody_represents,
    ``IRComparison.LeanTyped.DefinitionView.apply_body_equivalence,
    ``IRComparison.LeanTyped.DefinitionView.apply_and_instantiate,
    ``IRComparison.LeanTyped.DefinitionView.extend_ordered_from_body,
    ``IRComparison.LeanTyped.apply_binary_fact,
    ``IRComparison.LeanTyped.BinaryFactView.apply,
    ``IRComparison.LeanTyped.BinaryFactView.signature_represents,
    ``IRComparison.LeanTyped.BinaryFactView.install_ordered,
    ``IRComparison.LeanTyped.Standard.add, ``IRComparison.LeanTyped.Standard.sub,
    ``IRComparison.LeanTyped.Standard.mul, ``IRComparison.LeanTyped.Standard.div,
    ``IRComparison.LeanTyped.Standard.neg, ``IRComparison.LeanTyped.Standard.literal,
    ``IRComparison.LeanTyped.Standard.select,
    ``IRComparison.Circuit.instructions_correct,
    ``IRComparison.Circuit.allocateChannels_correct,
    ``IRComparison.Circuit.expanded_pipeline_finishes,
    ``IRComparison.Circuit.unified_pipeline_finishes,
    ``IRComparison.Circuit.compile_facts,
    ``IRComparison.Circuit.word_pipeline_finishes,
    ``IRComparison.Circuit.WordBuffer.pack_correct,
    ``IRComparison.Circuit.WordBuffer.withUnused_contents,
    ``IRComparison.Circuit.FiniteRuntime.pack_correct,
    ``IRComparison.Circuit.FiniteRuntime.withUnused_decode,
    ``IRComparison.Circuit.finiteTick_from_agreement,
    ``IRComparison.Circuit.finiteRun_from_agreement,
    ``IRComparison.Circuit.observation_from_agreement,
    ``IRComparison.Circuit.finite_observation_from_initial,
    ``IRComparison.Circuit.storage_reachable,
    ``IRComparison.Circuit.finite_execution,
    ``IRComparison.Circuit.finite_observation,
    ``IRComparison.Circuit.finite_pipeline_finishes,
    ``IRComparison.Circuit.RTL.lowerNode_correct,
    ``IRComparison.Circuit.RTL.lower_tick,
    ``IRComparison.Circuit.RTL.lower_run,
    ``IRComparison.Circuit.Expr.seq_eq_select,
    ``IRComparison.Circuit.RTL.Validity.both_eval,
    ``IRComparison.Circuit.RTL.Validity.choose_eval,
    ``IRComparison.Circuit.SystemVerilog.validityReferences_both,
    ``IRComparison.Circuit.SystemVerilog.validityReferences_choose,
    ``IRComparison.Circuit.RTL.combinational_correct,
    ``IRComparison.Circuit.RTL.map_statement_correct,
    ``IRComparison.Circuit.RTL.lowerCombinational_tick,
    ``IRComparison.Circuit.RTL.writeRange_correct,
    ``IRComparison.Circuit.RTL.Bank.copy_correct,
    ``IRComparison.Circuit.RTL.Bank.push_correct,
    ``IRComparison.Circuit.RTL.Bank.store_correct,
    ``IRComparison.Circuit.RTL.Bank.head_correct,
    ``IRComparison.Circuit.RTL.Bank.shift_correct,
    ``IRComparison.Circuit.RTL.Bank.length_fits,
    ``IRComparison.Circuit.RTL.artifact_tick_correct,
    ``IRComparison.Circuit.RTL.artifact_run_correct,
    ``IRComparison.Circuit.RTL.rtl_pipeline_from_initial,
    ``IRComparison.Circuit.RTL.rtl_pipeline_finishes,
    ``IRComparison.Circuit.RTL.Controller.render_prints,
    ``IRComparison.Circuit.RTL.controller_reset,
    ``IRComparison.Circuit.RTL.controller_execute,
    ``IRComparison.Circuit.RTL.controller_start,
    ``IRComparison.Circuit.RTL.controller_configure,
    ``IRComparison.Circuit.FiniteRuntime.inputSource_encode,
    ``IRComparison.Circuit.RTL.start_edge,
    ``IRComparison.Circuit.RTL.reset_edge,
    ``IRComparison.Circuit.RTL.configure_lengths,
    ``IRComparison.Circuit.RTL.configure_cell,
    ``IRComparison.Circuit.RTL.beginInvocation_agrees,
    ``IRComparison.Circuit.RTL.startup_pipeline_finishes,
    ``IRComparison.Circuit.RTL.quiet_tick_running,
    ``IRComparison.Circuit.RTL.quiet_tick_agrees,
    ``IRComparison.Circuit.RTL.quiet_run_agrees,
    ``IRComparison.Circuit.RTL.interface_pipeline_finishes,
    ``IRComparison.Circuit.SystemVerilog.Expr.text_correct,
    ``IRComparison.Circuit.SystemVerilog.Wire.text_correct,
    ``IRComparison.Circuit.SystemVerilog.Destination.text_correct,
    ``IRComparison.Circuit.SystemVerilog.Statement.text_correct,
    ``IRComparison.Circuit.SystemVerilog.signed_magnitude,
    ``IRComparison.Circuit.SystemVerilog.ofInt_signed_preserves,
    ``IRComparison.Circuit.SystemVerilog.arithmetic_working_width,
    ``IRComparison.Circuit.SystemVerilog.signed_widen,
    ``IRComparison.Circuit.SystemVerilog.signed_reference_eval,
    ``IRComparison.Circuit.SystemVerilog.signed_reference_self,
    ``IRComparison.Circuit.SystemVerilog.cast_reference_eval,
    ``IRComparison.Circuit.SystemVerilog.literal_eval,
    ``IRComparison.Circuit.SystemVerilog.binary_eval,
    ``IRComparison.Circuit.SystemVerilog.widened_binary_eval,
    ``IRComparison.Circuit.SystemVerilog.widened_binary_correct,
    ``IRComparison.Circuit.SystemVerilog.loop_counter_fits,
    ``IRComparison.Circuit.SystemVerilog.loop_reference_eval,
    ``IRComparison.Circuit.SystemVerilog.scalar_nonblocking,
    ``IRComparison.Circuit.SystemVerilog.evaluateNode_correct,
    ``IRComparison.Circuit.SystemVerilog.literal_printed_bits,
    ``IRComparison.Circuit.SystemVerilog.loop_cell_assignment,
    ``IRComparison.Circuit.SystemVerilog.loop_copy_cell,
    ``IRComparison.Circuit.SystemVerilog.Store.fold_cells,
    ``IRComparison.Circuit.SystemVerilog.forRange_cells,
    ``IRComparison.Circuit.SystemVerilog.snapshot_copy_correct,
    ``IRComparison.Circuit.SystemVerilog.Expr.type_agrees,
    ``IRComparison.Circuit.SystemVerilog.Expr.eval_agrees,
    ``IRComparison.Circuit.SystemVerilog.Expr.assignment_agrees,
    ``IRComparison.Circuit.SystemVerilog.appendWires_satisfies,
    ``IRComparison.Circuit.SystemVerilog.evaluateWires_satisfies,
    ``IRComparison.Circuit.termText_builds,
    ``IRComparison.Circuit.termText_declared,
    ``IRComparison.Circuit.preserves_statementCode,
    ``IRComparison.Circuit.generateCode_ordered,
    ``IRComparison.Circuit.generateCode_satisfies,
    ``IRComparison.Circuit.SystemVerilog.SignedMeaning.assignment,
    ``IRComparison.Circuit.SystemVerilog.SignedMeaning.cast,
    ``IRComparison.Circuit.SystemVerilog.SignedMeaning.binary_join,
    ``IRComparison.Circuit.SystemVerilog.SignedMeaning.comparison,
    ``IRComparison.Circuit.SystemVerilog.SignedMeaning.select_bool,
    ``IRComparison.Circuit.SystemVerilog.unsigned_reference_meaning,
    ``IRComparison.Circuit.SystemVerilog.unsigned_index_meaning,
    ``IRComparison.Circuit.SystemVerilog.division_corrections_fit,
    ``IRComparison.Circuit.SystemVerilog.division_meaning,
    ``IRComparison.Circuit.SystemVerilog.termTemplate_binary,
    ``IRComparison.Circuit.SystemVerilog.termTemplate_cell,
    ``IRComparison.Circuit.SystemVerilog.termTemplate_correct,
    ``IRComparison.Circuit.SystemVerilog.recordTerm_correct,
    ``IRComparison.Circuit.SystemVerilog.termText_correct,
    ``IRComparison.Circuit.SystemVerilog.evaluateWires_realizes,
    ``IRComparison.Circuit.SystemVerilog.generateCode_cache_correct,
    ``IRComparison.Circuit.SystemVerilog.generateCode_values_correct,
    ``IRComparison.Circuit.SystemVerilog.physicalNode_finite,
    ``IRComparison.Circuit.SystemVerilog.physicalTree_finite,
    ``IRComparison.Circuit.SystemVerilog.generateCode_finite_values,
    ``IRComparison.Circuit.SystemVerilog.cache_termText,
    ``IRComparison.Circuit.SystemVerilog.combinational_references,
    ``IRComparison.Circuit.SystemVerilog.lowerNode_references,
    ``IRComparison.Circuit.SystemVerilog.generateCode_references,
    ``IRComparison.Circuit.SystemVerilog.generateCode_checked_values,
    ``IRComparison.Circuit.SystemVerilog.EmissionTrace.total,
    ``IRComparison.Circuit.SystemVerilog.generateCode_trace,
    ``IRComparison.Circuit.SystemVerilog.generateCode_total,
    ``IRComparison.Circuit.SystemVerilog.BooleanMeaning.select,
    ``IRComparison.Circuit.SystemVerilog.unsigned_comparison,
    ``IRComparison.Circuit.SystemVerilog.validityText_correct,
    ``IRComparison.Circuit.SystemVerilog.expression_correct,
    ``IRComparison.Circuit.SystemVerilog.testCode_correct,
    ``IRComparison.Circuit.SystemVerilog.lowerNode_tests_ready,
    ``IRComparison.Circuit.SystemVerilog.artifact_tests_ready,
    ``IRComparison.Circuit.SystemVerilog.statementCode_branch_decision,
    ``IRComparison.Circuit.SystemVerilog.Statement.assign_signed,
    ``IRComparison.Circuit.SystemVerilog.Statement.assign_index_signed,
    ``IRComparison.Circuit.SystemVerilog.Statement.assign_boolean,
    ``IRComparison.Circuit.SystemVerilog.finite_head_meaning,
    ``IRComparison.Circuit.SystemVerilog.scalarCode_correct,
    ``IRComparison.Circuit.SystemVerilog.statementCode_assign_correct,
    ``IRComparison.Circuit.SystemVerilog.unsigned_reference_assignment,
    ``IRComparison.Circuit.SystemVerilog.counter_assignment,
    ``IRComparison.Circuit.SystemVerilog.fifo_shift_correct,
    ``IRComparison.Circuit.SystemVerilog.statementCode_store_correct,
    ``IRComparison.Circuit.SystemVerilog.statementCode_erase_correct,
    ``IRComparison.Circuit.SystemVerilog.statementCode_clear_correct,
    ``IRComparison.Circuit.SystemVerilog.statementCode_send_correct,
    ``IRComparison.Circuit.SystemVerilog.statementCode_tail_correct,
    ``IRComparison.Circuit.SystemVerilog.statementCode_copy_correct,
    ``IRComparison.Circuit.SystemVerilog.lowerNode_ready,
    ``IRComparison.Circuit.SystemVerilog.artifact_ready,
    ``IRComparison.Circuit.SystemVerilog.statementCode_total,
    ``IRComparison.Circuit.SystemVerilog.generateCode_execution_total,
    ``IRComparison.Circuit.SystemVerilog.finite_store_matches,
    ``IRComparison.Circuit.SystemVerilog.Store.Matches.writeRegister,
    ``IRComparison.Circuit.SystemVerilog.Store.Matches.setArray,
    ``IRComparison.Circuit.SystemVerilog.Store.Matches.setQueue,
    ``IRComparison.Circuit.SystemVerilog.Store.Matches.store,
    ``IRComparison.Circuit.SystemVerilog.Store.Matches.push,
    ``IRComparison.Circuit.SystemVerilog.Store.Matches.copy,
    ``IRComparison.Circuit.SystemVerilog.Store.Matches.shift,
    ``IRComparison.Circuit.SystemVerilog.lowerNode_frame,
    ``IRComparison.Circuit.SystemVerilog.statementCode_refines,
    ``IRComparison.Circuit.SystemVerilog.generateCode_refines,
    ``IRComparison.Circuit.SystemVerilog.generateCode_tick_refines,
    ``IRComparison.Circuit.SystemVerilog.statementCode_refines_control,
    ``IRComparison.Circuit.SystemVerilog.Store.Matches.commit_packed,
    ``IRComparison.Circuit.SystemVerilog.Store.Matches.commit_agrees,
    ``IRComparison.Circuit.SystemVerilog.commit_environment,
    ``IRComparison.Circuit.SystemVerilog.generated_cases_control,
    ``IRComparison.Circuit.SystemVerilog.physicalTick_quiet_refines,
    ``IRComparison.Circuit.SystemVerilog.physicalRun_agrees,
    ``IRComparison.Circuit.SystemVerilog.physical_pipeline_from_started,
    ``IRComparison.Circuit.SystemVerilog.readCode_correct,
    ``IRComparison.Circuit.SystemVerilog.readCode_observed,
    ``IRComparison.Circuit.SystemVerilog.physical_pipeline_readout,
    ``IRComparison.Circuit.SystemVerilog.storageDeclarations_type,
    ``IRComparison.Circuit.SystemVerilog.storageDeclarations_memory_capacity,
    ``IRComparison.Circuit.SystemVerilog.storageDeclarations_queue_capacity,
    ``IRComparison.Circuit.SystemVerilog.storageDeclarations_positive,
    ``IRComparison.Circuit.SystemVerilog.moduleCode_tick,
    ``IRComparison.Circuit.SystemVerilog.moduleCode_run,
    ``IRComparison.Circuit.SystemVerilog.generateModule_components,
    ``IRComparison.Circuit.SystemVerilog.emit_module,
    ``IRComparison.Circuit.SystemVerilog.moduleCode_storage,
    ``IRComparison.Circuit.SystemVerilog.emitted_pipeline_readout,
    ``IRComparison.Circuit.SystemVerilog.decimal_toString,
    ``IRComparison.Circuit.SystemVerilog.decimal_text_injective,
    ``IRComparison.Circuit.SystemVerilog.Name.decode_text,
    ``IRComparison.Circuit.SystemVerilog.Name.text_injective,
    ``IRComparison.Circuit.SystemVerilog.Name.parse_text,
    ``IRComparison.Circuit.SystemVerilog.Name.parse_sound,
    ``IRComparison.Circuit.SystemVerilog.Operator.decode_text,
    ``IRComparison.Circuit.SystemVerilog.Operator.text_injective,
    ``IRComparison.Circuit.SystemVerilog.signedDecimal_print,
    ``IRComparison.Circuit.SystemVerilog.literal_text_eval,
    ``IRComparison.Circuit.SystemVerilog.integer_text_eval,
    ``IRComparison.Circuit.SystemVerilog.Expr.literalReadback_type,
    ``IRComparison.Circuit.SystemVerilog.Expr.literalReadback_eval,
    ``IRComparison.Circuit.SystemVerilog.Concrete.parse_print,
    ``IRComparison.Circuit.SystemVerilog.Concrete.Tree.tokens_injective,
    ``IRComparison.Circuit.SystemVerilog.Concrete.expression_readback,
    ``IRComparison.Circuit.SystemVerilog.Concrete.parse_printExpression,
    ``IRComparison.Circuit.SystemVerilog.Concrete.printExpression_eval,
    ``IRComparison.Circuit.SystemVerilog.Concrete.statement_readback,
    ``IRComparison.Circuit.SystemVerilog.Concrete.parse_printStatement,
    ``IRComparison.Circuit.SystemVerilog.Concrete.printStatement_eval,
    ``IRComparison.Circuit.SystemVerilog.Concrete.declarations_readback,
    ``IRComparison.Circuit.SystemVerilog.Concrete.wires_readback,
    ``IRComparison.Circuit.SystemVerilog.Concrete.readPort_readback,
    ``IRComparison.Circuit.SystemVerilog.Concrete.clock_readback,
    ``IRComparison.Circuit.SystemVerilog.Concrete.module_readback,
    ``IRComparison.Circuit.SystemVerilog.Concrete.parse_printModule,
    ``IRComparison.Circuit.SystemVerilog.Statement.literalReadback_eval,
    ``IRComparison.Circuit.SystemVerilog.environmentFor_readback,
    ``IRComparison.Circuit.SystemVerilog.appendWires_readback,
    ``IRComparison.Circuit.SystemVerilog.moduleReadback_tick,
    ``IRComparison.Circuit.SystemVerilog.moduleReadback_run,
    ``IRComparison.Circuit.SystemVerilog.moduleReadback_read,
    ``IRComparison.Circuit.SystemVerilog.declaredType_readback,
    ``IRComparison.Circuit.SystemVerilog.declaredCapacity_readback,
    ``IRComparison.Circuit.SystemVerilog.printModule_run,
    ``IRComparison.Circuit.SystemVerilog.emit_text_correct,
    ``IRComparison.Circuit.SystemVerilog.emitted_text_pipeline_readout,
    ``IRComparison.Circuit.SystemVerilog.startCode_eval,
    ``IRComparison.Circuit.SystemVerilog.start_commit,
    ``IRComparison.Circuit.SystemVerilog.emitted_interface_layout,
    ``IRComparison.Circuit.SystemVerilog.emitted_text_start,
    ``IRComparison.Circuit.SystemVerilog.emitted_text_invocation_readout,
    ``IRComparison.Circuit.SystemVerilog.zero_bank_eval,
    ``IRComparison.HybridIR.Cmd.ArraysWithin.mono,
    ``IRComparison.Circuit.compile_layout,
    ``IRComparison.Circuit.ChannelCounted.lower_references,
    ``IRComparison.Circuit.symbolic_schedule_references,
    ``IRComparison.Circuit.ReferenceScope.Control.assemble_ready,
    ``IRComparison.Circuit.compile_generation,
    ``IRComparison.Circuit.Pipelining.integrate_total,
    ``IRComparison.Circuit.Pipelining.Integrated.outputs_declared,
    ``IRComparison.LeanTyped.Represents.translate_complete,
    ``IRComparison.LeanTypeInference.DirectTyping.infer_complete,
    ``IRComparison.LeanTypeInference.DirectTyping.check_complete,
    ``IRComparison.LeanLibrary.Represents.translate_complete,
    ``IRComparison.LeanLibrary.Declaration.load_complete,
    ``IRComparison.LeanLibrary.installTypes_complete,
    ``IRComparison.LeanTypeAliases.Alias.load_complete,
    ``IRComparison.LeanTypeReduction.Definition.load_complete,
    ``IRComparison.LeanTypeReduction.step_beta_complete,
    ``IRComparison.DependencyClosure.walk_inventory,
    ``IRComparison.WordFrontend.SignatureClosure.install_complete,
    ``IRComparison.WordFrontend.load_complete,
    ``IRComparison.WordFrontend.closeArtifact_complete,
    ``IRComparison.WordFrontend.finish_complete,
    ``IRComparison.WordFrontend.Artifact.check_known,
    ``IRComparison.WordFrontend.ClosedTerm.const,
    ``IRComparison.WordFrontend.ClosedTerm.app,
    ``IRComparison.LeanTypeReduction.reduce_alias_complete,
    ``IRComparison.LeanTypeReduction.expose_alias_complete,
    ``IRComparison.LeanTypeReduction.conversion_alias_right_complete,
    ``IRComparison.WordFrontend.compatible_same,
    ``IRComparison.WordFrontend.compatible_alias_right,
    ``IRComparison.LeanTyped.RepresentableSyntax.translate_complete,
    ``IRComparison.LeanTyped.RepresentableSyntax.rename,
    ``IRComparison.LeanTyped.RepresentableSyntax.substitute,
    ``IRComparison.LeanLibrary.Represents.monomorphic,
    ``IRComparison.LeanSourceEntry.represents_stripped,
    ``IRComparison.WordFrontend.app_represents,
    ``IRComparison.WordFrontend.sourceApplication,
    ``IRComparison.WordFrontend.targetEvaluation,
    ``IRComparison.WordFrontend.namedEquality,
    ``IRComparison.WordFrontend.closedTerm_complete,
    ``IRComparison.WordFrontend.Piece.target_translate,
    ``IRComparison.WordFrontend.localFact_complete,
    ``IRComparison.LeanUniverseConversion.conversion_complete,
    ``IRComparison.LeanTypeAliases.Alias.expand_complete,
    ``IRComparison.LeanTypeAliases.Alias.conversion_left_complete,
    ``IRComparison.LeanTypeAliases.Alias.conversion_right_complete,
    ``IRComparison.WordFrontend.ClosedTerm.bindingIndex_value,
    ``IRComparison.WordFrontend.ClosedTerm.bindingIndex_size,
    ``IRComparison.FrontendDepthExamples.earlierScalarHLS.correct,
    ``IRComparison.WordFrontend.source_body_represents,
    ``IRComparison.LeanTypeInference.NatSignatures.numeral_typed,
    ``IRComparison.WordFrontend.ClosedTerm.bindingIndex_typed,
    ``IRComparison.LeanTypeInference.DirectTyping.weakN,
    ``IRComparison.LeanTypeInference.DirectTyping.instN,
    ``IRComparison.LeanTypeInference.DirectTyping.in_context,
    ``IRComparison.LeanTypeInference.DirectTyping.infer_known_complete,
    ``IRComparison.LeanTypeInference.DirectTyping.check_known_complete,
    ``IRComparison.LeanLibrary.Represents.closed,
    ``IRComparison.WordFrontend.Certificate.initialInputs,
    ``IRComparison.WordFrontend.Certificate.InputsTyped.lift,
    ``IRComparison.WordFrontend.Certificate.InputsTyped.nextState,
    ``IRComparison.WordFrontend.Certificate.InputsTyped.nextWord,
    ``IRComparison.WordFrontend.Certificate.finish_known_complete,
    ``IRComparison.WordFrontend.Certificate.body_copy_complete,
    ``IRComparison.LeanTypeInference.CastTyping.infer_complete,
    ``IRComparison.LeanTypeInference.CastTyping.check_complete,
    ``IRComparison.LeanTypeInference.CastTyping.withoutCasts,
    ``IRComparison.LeanStructuralConversion.prove_application_complete,
    ``IRComparison.LeanTypeReduction.conversion_alias_right_exact,
    ``IRComparison.WordFrontend.Certificate.finish_cast_complete,
    ``IRComparison.WordFrontend.Arithmetic.Signatures.width_typed,
    ``IRComparison.WordFrontend.Arithmetic.Signatures.header_typed,
    ``IRComparison.WordFrontend.Arithmetic.AliasSetup.covers,
    ``IRComparison.WordFrontend.Arithmetic.loaded_conversion_covers,
    ``IRComparison.WordFrontend.Arithmetic.binary_typed,
    ``IRComparison.WordFrontend.Arithmetic.binary_finish,
    ``IRComparison.WordFrontend.Arithmetic.binary_value_checked,
    ``IRComparison.LeanTypeInference.CastTyping.weakN,
    ``IRComparison.LeanTypeInference.CastTyping.instN,
    ``IRComparison.LeanTypeReduction.step_apply_cast_complete,
    ``IRComparison.LeanTypeReduction.ArgumentsCasts.step_complete,
    ``IRComparison.LeanTypeReduction.named_application_cast_complete,
    ``IRComparison.WordFrontend.Arithmetic.casts_closed,
    ``IRComparison.WordFrontend.source_function_cast_typed,
    ``IRComparison.WordFrontend.named_source_step_cast_complete,
    ``IRComparison.WordFrontend.compile_of_cast_body,
    ``IRComparison.Circuit.range_wrap32,
    ``IRComparison.Circuit.Expr.wrap32_preserves_modular,
    ``IRComparison.Circuit.SystemVerilog.termTemplate_wrap32,
    ``IRComparison.Circuit.SystemVerilog.Generation.ready_wrap32,
    ``IRComparison.WordFrontend.ScalarEnvironment.materialize_nil,
    ``IRComparison.WordFrontend.ScalarEnvironment.reference_cons_succ,
    ``IRComparison.WordFrontend.ScalarEnvironment.materialize_cons,
    ``IRComparison.WordFrontend.ScalarEnvironment.materialize_app,
    ``IRComparison.WordFrontend.ScalarEnvironment.visit,
    ``IRComparison.ScalarEnvironmentExamples.generatedShared.wordBody_correct,
    ``IRComparison.ScalarEnvironmentExamples.generatedShadow.wordBody_correct,
    ``IRComparison.ScalarEnvironmentExamples.generatedSelected.wordBody_correct,
    ``IRComparison.WordFrontend.Certificate.target_check_cast_complete,
    ``IRComparison.WordFrontend.Arithmetic.Signatures.literal_typed,
    ``IRComparison.WordFrontend.Arithmetic.literal_finish,
    ``IRComparison.LeanTypeInference.CastTyping.replace_context_suffix,
    ``IRComparison.LeanTypeInference.CastTyping.closed_context,
    ``IRComparison.WordFrontend.Read.nat_typed,
    ``IRComparison.WordFrontend.Read.word_typed,
    ``IRComparison.WordFrontend.Certificate.sequence_typed,
    ``IRComparison.WordFrontend.Certificate.sequence_next_typed,
    ``IRComparison.WordFrontend.Certificate.sequence_finish,
    ``IRComparison.WordFrontend.Certificate.BindSignatures.state_header_typed,
    ``IRComparison.LeanTypeInference.CastTyping.mono,
    ``IRComparison.LeanStructuralConversion.prove_beta_argument_complete,
    ``IRComparison.LeanTypeReduction.step_beta_cast_complete,
    ``IRComparison.LeanStructuralConversion.prove_reflexive_cast_complete,
    ``IRComparison.LeanStructuralConversion.prove_beta_right_cast_complete,
    ``IRComparison.LeanStructuralConversion.prove_forall_complete,
    ``IRComparison.WordFrontend.Arithmetic.AliasSetup.proves,
    ``IRComparison.WordFrontend.Arithmetic.AliasSetup.covers_recursive,
    ``IRComparison.LeanTypeInference.CastTyping.inferred_kind,
    ``IRComparison.LeanTypeReduction.reduce_first_complete,
    ``IRComparison.LeanTypeReduction.expose_beta_not_sort,
    ``IRComparison.LeanTypeAliases.Alias.expand_other_head,
    ``IRComparison.WordFrontend.Arithmetic.AliasSetup.basic_beta_none,
    ``IRComparison.WordFrontend.Arithmetic.loaded_alias_setup,
    ``IRComparison.WordFrontend.Certificate.sequence_beta_conversion,
    ``IRComparison.WordFrontend.Certificate.ProofCasts.covered,
    ``IRComparison.WordFrontend.Certificate.BindSignatures.header_typed,
    ``IRComparison.WordFrontend.Certificate.continuation_beta_conversion,
    ``IRComparison.WordFrontend.Certificate.value_beta_conversion,
    ``IRComparison.WordFrontend.Certificate.bindValue_typed,
    ``IRComparison.WordFrontend.Certificate.bindValue_next_typed,
    ``IRComparison.WordFrontend.Certificate.bindValue_finish,
    ``IRComparison.WordFrontend.Certificate.letValue_typed,
    ``IRComparison.WordFrontend.Certificate.letValue_finish,
    ``IRComparison.WordFrontend.Certificate.Return.Signatures.header_typed,
    ``IRComparison.WordFrontend.Certificate.Return.skip_typed,
    ``IRComparison.WordFrontend.Certificate.Return.body_skip_invariant_complete,
    ``IRComparison.WordFrontend.Certificate.body_copy_invariant_complete,
    ``IRComparison.WordFrontend.Certificate.body_copy_invariant_complete_code,
    ``IRComparison.WordFrontend.Certificate.assign_fact_typed,
    ``IRComparison.WordFrontend.Certificate.Return.Signatures.headerFor_typed,
    ``IRComparison.WordFrontend.Certificate.Branch.ite_typed,
    ``IRComparison.WordFrontend.Certificate.Branch.Select.fact_typed,
    ``IRComparison.WordFrontend.Certificate.Branch.Select.finish_complete,
    ``IRComparison.WordFrontend.Certificate.Step.yield_typed,
    ``IRComparison.WordFrontend.Certificate.Step.yield_fact_typed,
    ``IRComparison.WordFrontend.Certificate.Step.branch_fact_typed,
    ``IRComparison.WordFrontend.Certificate.Step.bind_fact_typed,
    ``IRComparison.WordFrontend.Arithmetic.continuationValue_ne,
    ``IRComparison.WordFrontend.Arithmetic.AliasSetup.value_beta_proved,
    ``IRComparison.WordFrontend.Certificate.Step.lift_beta_proved,
    ``IRComparison.WordFrontend.Certificate.Step.equality_betas_proved,
    ``IRComparison.WordFrontend.Certificate.Step.bind_beta_conversion,
    ``IRComparison.WordFrontend.Certificate.Step.NormalizationCasts.covered,
    ``IRComparison.WordFrontend.Certificate.Step.let_fact_typed,
    ``IRComparison.WordFrontend.Arithmetic.AliasSetup.word_state_none,
    ``IRComparison.WordFrontend.Certificate.Branch.fact_typed,
    ``IRComparison.WordFrontend.Certificate.Branch.choice_typed,
    ``IRComparison.WordFrontend.Certificate.Branch.finish_complete,
    ``IRComparison.WordFrontend.Certificate.Return.assign_typed,
    ``IRComparison.WordFrontend.Certificate.Return.assign_finish,
    ``IRComparison.LeanTypeReduction.step_application_kind,
    ``IRComparison.LeanTypeReduction.step_beta2_kind,
    ``IRComparison.LeanTypeReduction.expose_not_sort,
    ``IRComparison.LeanTypeReduction.expose_beta2_not_sort,
    ``IRComparison.LeanTypeReduction.step_beta2_cast_complete,
    ``IRComparison.LeanStructuralConversion.prove_reduction_right_complete,
    ``IRComparison.WordFrontend.Arithmetic.AliasSetup.basic_beta2_none,
    ``IRComparison.WordFrontend.Arithmetic.continuation2Value_inst,
    ``IRComparison.WordFrontend.Arithmetic.continuation2Value_ne,
    ``IRComparison.WordFrontend.Arithmetic.AliasSetup.value_beta2_proved,
    ``IRComparison.WordFrontend.Certificate.evalCmd_represents,
    ``IRComparison.WordFrontend.Certificate.For.header_represents,
    ``IRComparison.WordFrontend.Certificate.For.source_arguments,
    ``IRComparison.WordFrontend.Certificate.For.source_represents,
    ``IRComparison.WordFrontend.Certificate.For.compose_typed,
    ``IRComparison.WordFrontend.Certificate.For.fact_typed,
    ``IRComparison.WordFrontend.Certificate.For.next_typed,
    ``IRComparison.WordFrontend.Certificate.For.finish_complete,
    ``IRComparison.WordFrontend.Certificate.For.Bound.closedTerm_complete,
    ``IRComparison.WordFrontend.Certificate.For.source_typed,
    ``IRComparison.WordFrontend.Certificate.Step.equalityPrefix_typed,
    ``IRComparison.WordFrontend.Certificate.For.equality_beta2_proved,
    ``IRComparison.WordFrontend.Certificate.For.continuation_beta_conversion,
    ``IRComparison.WordFrontend.Certificate.For.Casts.covered,
    ``IRComparison.WordFrontend.Certificate.For.BoundSignatures.natural_typed,
    ``IRComparison.WordFrontend.Certificate.For.BoundSignatures.negative_typed,
    ``IRComparison.WordFrontend.Certificate.For.Header.Signatures.word_typed,
    ``IRComparison.WordFrontend.Certificate.For.Header.Signatures.option_typed,
    ``IRComparison.WordFrontend.Certificate.For.Header.Signatures.words_typed,
    ``IRComparison.WordFrontend.Certificate.For.Header.Signatures.membership_type,
    ``IRComparison.WordFrontend.Certificate.For.Header.Signatures.membership_value,
    ``IRComparison.WordFrontend.Certificate.For.Header.Signatures.list_value,
    ``IRComparison.WordFrontend.Certificate.For.Header.Signatures.forIn_value,
    ``IRComparison.WordFrontend.Certificate.For.Header.Signatures.header_typed,
    ``IRComparison.WordFrontend.Certificate.StateAlias.fact_typed,
    ``IRComparison.WordFrontend.Certificate.StateLet.fact_typed,
    ``IRComparison.WordFrontend.Certificate.StateLet.finish_complete,
    ``IRComparison.WordFrontend.Certificate.UnitStep.Signatures.type_typed,
    ``IRComparison.WordFrontend.Certificate.UnitStep.Signatures.value_typed,
    ``IRComparison.WordFrontend.Certificate.UnitStep.beta_at_proved,
    ``IRComparison.WordFrontend.Certificate.UnitStep.premise_conversion,
    ``IRComparison.WordFrontend.Certificate.UnitStep.pure_represents,
    ``IRComparison.WordFrontend.Certificate.UnitStep.pure_typed,
    ``IRComparison.WordFrontend.Certificate.UnitStep.fact_typed,
    ``IRComparison.LeanTypeReduction.step_beta_kind,
    ``IRComparison.WordFrontend.Arithmetic.ValueForm.step_kind,
    ``IRComparison.WordFrontend.Arithmetic.ValueForm.expose_none,
    ``IRComparison.WordFrontend.Arithmetic.ValueForm.alias_none,
    ``IRComparison.WordFrontend.Certificate.localZero_typed,
    ``IRComparison.WordFrontend.Certificate.localSucc_typed,
    ``IRComparison.WordFrontend.Certificate.localFact_typed_complete,
    ``IRComparison.WordFrontend.Certificate.forIn_range_hit,
    ``IRComparison.WordFrontend.Arithmetic.AliasSetup.basic_word_refl_none,
    ``IRComparison.LeanTypeAliases.Alias.conversion_right_universe_complete,
    ``IRComparison.LeanTypeReduction.conversion_alias_left_exact,
    ``IRComparison.WordFrontend.Arithmetic.SourceCasts.closed,
    ``IRComparison.WordFrontend.Arithmetic.AliasSetup.covers_source,
    ``IRComparison.WordFrontend.Read.Signatures.header_typed,
    ``IRComparison.WordFrontend.Read.Signatures.word_index_typed,
    ``IRComparison.WordFrontend.Certificate.equality_head_check_complete,
    ``IRComparison.LeanTypeReduction.step_apply_complete,
    ``IRComparison.LeanTypeReduction.ArgumentsTyped.step_complete,
    ``IRComparison.LeanTypeReduction.named_application_complete,
    ``IRComparison.WordFrontend.loaded_constant_types_closed,
    ``IRComparison.WordFrontend.reapply_parameters,
    ``IRComparison.WordFrontend.sameTerm_complete,
    ``IRComparison.WordFrontend.sameTerm_sound,
    ``IRComparison.WordFrontend.leadingLet_let_represents,
    ``IRComparison.WordFrontend.leadingLet_beta_represents,
    ``IRComparison.FrontendDepthExamples.generated.correct,
    ``IRComparison.FrontendDepthExamples.generated.generates,
    ``IRComparison.FrontendDepthExamples.annotatedHLS.correct,
    ``IRComparison.CertifiedHLS.compile_total,
    ``IRComparison.FixedHLS.Entry.memory_and_range_checks,
    ``IRComparison.FixedHLS.Entry.compile_total,
    ``IRComparison.FixedHLS.Entry.generates_correct,
    ``IRComparison.Circuit.SystemVerilog.resetCode_eval,
    ``IRComparison.Circuit.SystemVerilog.configureCode_eval,
    ``IRComparison.Circuit.SystemVerilog.resetWrites_busy_scalar,
    ``IRComparison.Circuit.SystemVerilog.configureWrites_busy_scalar,
    ``IRComparison.Circuit.SystemVerilog.emitted_text_reset,
    ``IRComparison.Circuit.SystemVerilog.emitted_text_configure,
    ``IRComparison.Circuit.SystemVerilog.emitted_text_preparation,
    ``IRComparison.Circuit.SystemVerilog.emitted_text_reset_config_start_readout,
    ``IRComparison.PipelineWorkloads.histogramCode.wordBody_correct,
    ``IRComparison.PipelineWorkloads.compactCode.wordBody_correct,
    ``IRComparison.HLSBenchmarks.axpyCode.wordBody_correct,
    ``IRComparison.HLSBenchmarks.firCode.wordBody_correct,
    ``IRComparison.HLSBenchmarks.prefixCode.wordBody_correct,
    ``IRComparison.HLSBenchmarks.dotCode.wordBody_correct,
    ``IRComparison.HLSBenchmarks.histogramCode.wordBody_correct,
    ``IRComparison.HLSBenchmarks.gatherCode.wordBody_correct,
    ``IRComparison.HLSBenchmarks.gemmCode.wordBody_correct,
    ``IRComparison.HLSBenchmarks.stencilCode.wordBody_correct,
    ``IRComparison.HLSBenchmarks.replaceZeroCode.wordBody_correct,
    ``IRComparison.HLSBenchmarks.recurrenceCode.wordBody_correct,
    ``IRComparison.WordFrontend.NaturalLoop.source_typed_state,
    ``IRComparison.WordFrontend.OrdinarySource.Scalar.typing,
    ``IRComparison.WordFrontend.OrdinarySource.StateValue.typing,
    ``IRComparison.WordFrontend.OrdinarySource.Read.typing,
    ``IRComparison.WordFrontend.OrdinarySource.Arguments.applyTyping,
    ``IRComparison.WordFrontend.OrdinarySource.Function.typing,
    ``IRComparison.WordFrontend.OrdinarySource.Body.typing,
    ``IRComparison.WordFrontend.OrdinarySource.Body.wellScoped,
    ``IRComparison.WordFrontend.OrdinarySource.Function.wellScoped,
    ``IRComparison.WordFrontend.OrdinarySource.Function.retag,
    ``IRComparison.WordFrontend.OrdinarySource.Body.retag,
    ``IRComparison.WordFrontend.OrdinarySource.Body.typingRetagged,
    ``IRComparison.WordFrontend.OrdinarySource.Body.typingPrefixes,
    ``IRComparison.WordFrontend.OrdinarySource.Arguments.evidence,
    ``IRComparison.WordFrontend.OrdinarySource.retainedCall,
    ``IRComparison.WordFrontend.OrdinarySource.functionLetIdentity,
    ``IRComparison.WordFrontend.FunctionSyntax.lambdaSource_represents,
    ``IRComparison.WordFrontend.OrdinarySource.Function.Flow.demandsTyped,
    ``IRComparison.WordFrontend.OrdinarySource.Body.Flow.demandsTyped,
    ``IRComparison.WordFrontend.OrdinarySource.DemandsTyped.valueBound,
    ``IRComparison.WordFrontend.OrdinarySource.TypedMapping.identity,
    ``IRComparison.WordFrontend.OrdinarySource.TypedMapping.under,
    ``IRComparison.WordFrontend.OrdinarySource.TypedMapping.underClosed,
    ``IRComparison.WordFrontend.OrdinarySource.TypedMapping.consClosed,
    ``IRComparison.WordFrontend.OrdinarySource.TypedMapping.prepend,
    ``IRComparison.WordFrontend.OrdinarySource.Signature.Spelling.substitute,
    ``IRComparison.WordFrontend.OrdinarySource.mappingUnderRepresented,
    ``IRComparison.WordFrontend.OrdinarySource.typingMapped,
    ``IRComparison.WordFrontend.OrdinarySource.checkedTypingMapped,
    ``IRComparison.WordFrontend.OrdinarySource.openMapping_represented,
    ``IRComparison.WordFrontend.OrdinarySource.lambdaSourceMapped_represents,
    ``IRComparison.WordFrontend.OrdinarySource.Body.typingPrefixesMapped,
    ``IRComparison.WordFrontend.OrdinarySource.Arguments.evidenceMapped,
    ``IRComparison.WordFrontend.OrdinarySource.scalarShapeMapped,
    ``IRComparison.WordFrontend.OrdinarySource.Scalar.evidenceMapped,
    ``IRComparison.WordFrontend.OrdinarySource.Body.typingMapped,
    ``IRComparison.WordFrontend.OrdinarySource.Function.typingMapped,
    ``IRComparison.WordFrontend.OrdinarySource.StateRef.current,
    ``IRComparison.WordFrontend.OrdinarySource.CurrentMapping.underValue,
    ``IRComparison.WordFrontend.OrdinarySource.currentMapping_state,
    ``IRComparison.WordFrontend.OrdinarySource.currentMapping_range,
    ``IRComparison.WordFrontend.OrdinarySource.currentMapping_staticRange,
    ``IRComparison.WordFrontend.OrdinarySource.CurrentMapping.functionLet,
    ``IRComparison.WordFrontend.OrdinarySource.retainedCallMapped,
    ``IRComparison.WordFrontend.OrdinarySource.functionLet,
    ``IRComparison.WordFrontend.OrdinarySource.Context.lookup_origin,
    ``IRComparison.WordFrontend.OrdinarySource.initialMapping,
    ``IRComparison.WordFrontend.OrdinarySource.openParameterMapping,
    ``IRComparison.WordFrontend.OrdinarySource.Function.bindMapping,
    ``IRComparison.WordFrontend.OrdinarySource.Body.typingEntry,
    ``IRComparison.WordFrontend.OrdinarySource.freeVariables_succ,
    ``IRComparison.WordFrontend.OrdinarySource.stateVariables_underValue,
    ``IRComparison.WordFrontend.OrdinarySource.stateVariables_letScalar,
    ``IRComparison.WordFrontend.OrdinarySource.stateVariables_betaScalar,
    ``IRComparison.WordFrontend.OrdinarySource.CurrentMapping.appLeft,
    ``IRComparison.WordFrontend.OrdinarySource.CurrentMapping.appRight,
    ``IRComparison.WordFrontend.OrdinarySource.ScalarFrame.scalarShape,
    ``IRComparison.WordFrontend.OrdinarySource.StateRef.mappedReference,
    ``IRComparison.WordFrontend.OrdinarySource.ScalarFrame.evidence,
    ``IRComparison.WordFrontend.OrdinarySource.ScalarFrame.initial,
    ``IRComparison.WordFrontend.OrdinarySource.openScalarForm,
    ``IRComparison.WordFrontend.OrdinarySource.ScalarFrame.underScalar,
    ``IRComparison.WordFrontend.OrdinarySource.liftReferenceForm,
    ``IRComparison.WordFrontend.OrdinarySource.prependReferenceForm,
    ``IRComparison.WordFrontend.OrdinarySource.ScalarFrame.underNatural,
    ``IRComparison.WordFrontend.OrdinarySource.ScalarFrame.underAdministrative,
    ``IRComparison.WordFrontend.OrdinarySource.ScalarFrame.underState,
    ``IRComparison.WordFrontend.OrdinarySource.ScalarFrame.underUnit,
    ``IRComparison.WordFrontend.OrdinarySource.ScalarFrame.underStaticRange,
    ``IRComparison.WordFrontend.OrdinarySource.ScalarFrame.underNaturalRange,
    ``IRComparison.WordFrontend.OrdinarySource.ScalarFrame.bindFunction,
    ``IRComparison.WordFrontend.OrdinarySource.scalarBindingFromRetained,
    ``IRComparison.WordFrontend.OrdinarySource.Scalar.forms,
    ``IRComparison.WordFrontend.OrdinarySource.Read.forms,
    ``IRComparison.WordFrontend.OrdinarySource.mapStateSet,
    ``IRComparison.WordFrontend.OrdinarySource.StateValue.forms,
    ``IRComparison.WordFrontend.OrdinarySource.StateValue.returnSyntax,
    ``IRComparison.WordFrontend.OrdinarySource.RegisterMapping.initial,
    ``IRComparison.WordFrontend.OrdinarySource.RegisterMapping.under,
    ``IRComparison.WordFrontend.OrdinarySource.RegisterMapping.substitute,
    ``IRComparison.WordFrontend.OrdinarySource.Function.mappedHead,
    ``IRComparison.WordFrontend.OrdinarySource.RegisterMapping.functionLet,
    ``IRComparison.WordFrontend.OrdinarySource.RegisterMapping.closure,
    ``IRComparison.WordFrontend.OrdinarySource.DemandsTyped.retag,
    ``IRComparison.WordFrontend.OrdinarySource.substitute_closed,
    ``IRComparison.WordFrontend.OrdinarySource.ScalarFrame.tail,
    ``IRComparison.WordFrontend.OrdinarySource.ScalarFrame.bindHeld,
    ``IRComparison.WordFrontend.OrdinarySource.ScalarFrame.openParameter,
    ``IRComparison.WordFrontend.OrdinarySource.ScalarFrame.shiftTarget,
    ``IRComparison.WordFrontend.OrdinarySource.Parameter.extendTyped,
    ``IRComparison.WordFrontend.OrdinarySource.scalarLetSyntax,
    ``IRComparison.WordFrontend.OrdinarySource.stateLetSyntax,
    ``IRComparison.WordFrontend.OrdinarySource.readBindSyntax,
    ``IRComparison.WordFrontend.OrdinarySource.branchSyntax,
    ``IRComparison.WordFrontend.OrdinarySource.staticBoundMapped,
    ``IRComparison.WordFrontend.OrdinarySource.staticRangeSyntax,
    ``IRComparison.WordFrontend.OrdinarySource.naturalRangeSyntax,
    ``IRComparison.WordFrontend.OrdinarySource.writeSyntax,
    ``IRComparison.WordFrontend.OrdinarySource.copySyntax,
    ``IRComparison.WordFrontend.OrdinarySource.stateBindSyntax,
    ``IRComparison.WordFrontend.OrdinarySource.unitBindSyntax,
    ``IRComparison.WordFrontend.OrdinarySource.targetContext_append,
    ``IRComparison.WordFrontend.OrdinarySource.targetInputs_append,
    ``IRComparison.WordFrontend.OrdinarySource.targetContext_length,
    ``IRComparison.WordFrontend.OrdinarySource.ScalarFrame.captureExtension,
    ``IRComparison.WordFrontend.OrdinarySource.StateLinks.refl,
    ``IRComparison.WordFrontend.OrdinarySource.StateLinks.cons,
    ``IRComparison.WordFrontend.OrdinarySource.StateLinks.current,
    ``IRComparison.WordFrontend.OrdinarySource.ArgumentBindings.heldEnvironment,
    ``IRComparison.WordFrontend.OrdinarySource.Context.Related.append,
    ``IRComparison.WordFrontend.OrdinarySource.targetTyped,
    ``IRComparison.WordFrontend.OrdinarySource.ScalarFrame.atCapture,
    ``IRComparison.WordFrontend.OrdinarySource.Argument.retainedCase,
    ``IRComparison.WordFrontend.OrdinarySource.Arguments.retained,
    ``IRComparison.WordFrontend.OrdinarySource.Argument.unitSafe,
    ``IRComparison.WordFrontend.OrdinarySource.Arguments.unitSafe,
    ``IRComparison.WordFrontend.OrdinarySource.FunctionMeaning.extend,
    ``IRComparison.WordFrontend.OrdinarySource.FunctionMeaning.invoke,
    ``IRComparison.WordFrontend.OrdinarySource.FunctionMeaning.ofLambda,
    ``IRComparison.WordFrontend.OrdinarySource.FunctionEnvironment.extendTarget,
    ``IRComparison.WordFrontend.OrdinarySource.FunctionEnvironment.pushValue,
    ``IRComparison.WordFrontend.OrdinarySource.FunctionEnvironment.under,
    ``IRComparison.WordFrontend.OrdinarySource.FunctionEnvironment.bindFunction,
    ``IRComparison.WordFrontend.OrdinarySource.FunctionEnvironment.parameters,
    ``IRComparison.WordFrontend.OrdinarySource.FunctionEnvironment.captureExtension,
    ``IRComparison.WordFrontend.OrdinarySource.Function.Flow.interpret,
    ``IRComparison.WordFrontend.OrdinarySource.Body.Flow.interpret,
    ``IRComparison.WordFrontend.OrdinarySource.Body.syntaxEntry,
    ``IRComparison.WordFrontend.OrdinarySource.Body.Current.cast,
    ``IRComparison.WordFrontend.OrdinarySource.generates]
  for theoremName in audited do
    for assumption in (← collectAxioms theoremName) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains assumption do
        throwError "unexpected assumption {assumption} in {theoremName}"
  logInfo m!"Checked assumptions of {audited.length} entry-bridge theorems"

#print axioms IRComparison.Circuit.Shared.compile_ordered
#print axioms IRComparison.Circuit.Shared.compile_result_bound
#print axioms IRComparison.Circuit.Shared.compile_correct
#print axioms IRComparison.Circuit.Shared.compile_read_correct
#print axioms IRComparison.Circuit.Shared.Program.range_correct
#print axioms IRComparison.Circuit.Shared.Program.agrees

#print axioms IRComparison.Circuit.Shared.lowerValue_projection
#print axioms IRComparison.Circuit.Shared.lowerRead_projection
#print axioms IRComparison.Circuit.Shared.build_projection
#print axioms IRComparison.Circuit.Shared.Node.bitEval_correct
#print axioms IRComparison.Circuit.Shared.bitValues_correct
#print axioms IRComparison.Circuit.Shared.Program.bitEval_correct
#print axioms IRComparison.Circuit.Shared.compile_bitEval_correct
#print axioms IRComparison.Circuit.Shared.LocalRTL.lower_correct
#print axioms IRComparison.Circuit.Shared.LocalRTL.lowerGraph_correct
#print axioms IRComparison.Circuit.Shared.LocalRTL.lowerGraph_size
#print axioms IRComparison.Circuit.Shared.LocalRTL.compile_correct
#print axioms IRComparison.Circuit.Shared.LocalRTL.compile_read_correct

#print axioms IRComparison.Circuit.Shared.LocalRTL.fullValues_model
#print axioms IRComparison.Circuit.Shared.LocalRTL.compile_fullEval_correct
#print axioms IRComparison.Circuit.Shared.NetEmission.generate_ordered
#print axioms IRComparison.Circuit.Shared.NetEmission.term_correct
#print axioms IRComparison.Circuit.Shared.NetEmission.validity_correct
#print axioms IRComparison.Circuit.Shared.NetEmission.expression_correct
#print axioms IRComparison.Circuit.Shared.NetEmission.graph_correct
#print axioms IRComparison.Circuit.Shared.NetEmission.generate_correct
#print axioms IRComparison.Circuit.Shared.NetEmission.physical_from_refs
#print axioms IRComparison.Circuit.Shared.NetEmission.NetTrace.total
#print axioms IRComparison.Circuit.Shared.NetEmission.graph_trace
#print axioms IRComparison.Circuit.Shared.NetEmission.generate_total
#print axioms IRComparison.Circuit.Shared.NetEmission.read_text
#print axioms IRComparison.Circuit.Shared.NetEmission.evaluate_text
#print axioms IRComparison.Circuit.Shared.NetEmission.emitted_read_correct
#print axioms IRComparison.Circuit.Shared.NetEmission.emitted_total_correct
#print axioms IRComparison.Circuit.Shared.NetEmission.emitted_read_total_correct

#print axioms IRComparison.Circuit.SystemVerilog.Concrete.readWiresTail_eq

#print axioms IRComparison.Circuit.Emission.WellFormed.extendDeclarations
#print axioms IRComparison.Circuit.preserves_statementCodeWith
#print axioms IRComparison.Circuit.Shared.NetEmission.append_generate
#print axioms IRComparison.Circuit.Shared.NetEmission.append_builds
#print axioms IRComparison.Circuit.Shared.NetEmission.append_correct
#print axioms IRComparison.Circuit.Shared.NetEmission.intoPair_builds
#print axioms IRComparison.Circuit.Shared.NetEmission.intoPair_correct
#print axioms IRComparison.Circuit.Shared.NetEmission.intoPair_cacheMeaning
#print axioms IRComparison.Circuit.Shared.NetEmission.into_signal_correct
#print axioms IRComparison.Circuit.Shared.NetEmission.intoPair_trace
#print axioms IRComparison.Circuit.Shared.prepare_bounds
#print axioms IRComparison.Circuit.Shared.prepare_correct
#print axioms IRComparison.Circuit.Shared.prepare_range_correct
#print axioms IRComparison.Circuit.Shared.prepare_statement_correct
#print axioms IRComparison.Circuit.Shared.NetEmission.shared_statement_preserves
#print axioms IRComparison.Circuit.Shared.NetEmission.mixed_statement_preserves
#print axioms IRComparison.Circuit.Shared.NetEmission.module_declarations_ordered
#print axioms IRComparison.Circuit.Shared.NetEmission.generateModule_text

#print axioms IRComparison.Circuit.SystemVerilog.combinational_codeSound
#print axioms IRComparison.Circuit.SystemVerilog.testCode_correctWith
#print axioms IRComparison.Circuit.SystemVerilog.scalarCode_correctWith
#print axioms IRComparison.Circuit.SystemVerilog.statementCode_assign_correctWith
#print axioms IRComparison.Circuit.SystemVerilog.statementCode_store_correctWith
#print axioms IRComparison.Circuit.SystemVerilog.statementCode_send_correctWith
#print axioms IRComparison.Circuit.SystemVerilog.statementCode_refines_controlWith
#print axioms IRComparison.Circuit.SystemVerilog.keeps_statementCode
#print axioms IRComparison.Circuit.Shared.NetEmission.shared_codeSound
#print axioms IRComparison.Circuit.Shared.NetEmission.sum_codeSound
#print axioms IRComparison.Circuit.Shared.NetEmission.shared_keeps_trace
#print axioms IRComparison.Circuit.Shared.NetEmission.shared_cases_total
#print axioms IRComparison.Circuit.Shared.NetEmission.shared_statement_refines_control
#print axioms IRComparison.Circuit.Shared.NetEmission.shared_cases_refine
#print axioms IRComparison.Circuit.Shared.NetEmission.shared_module_tick
#print axioms IRComparison.Circuit.Shared.NetEmission.shared_module_text_tick

#print axioms IRComparison.Circuit.Shared.command_simulates
#print axioms IRComparison.Circuit.Shared.channel_simulates
#print axioms IRComparison.Circuit.Shared.pipeline_related
#print axioms IRComparison.Circuit.Shared.prepare_references
#print axioms IRComparison.Circuit.Shared.prepared_storage
#print axioms IRComparison.Circuit.Shared.graph_cases_references
#print axioms IRComparison.Circuit.Shared.graph_cases_ready
#print axioms IRComparison.Circuit.Shared.graph_cases_frame
#print axioms IRComparison.Circuit.Shared.generated_tick
#print axioms IRComparison.Circuit.Shared.generated_run
#print axioms IRComparison.Circuit.Shared.generated_text_run
#print axioms IRComparison.Circuit.Shared.compileStructured_correct

#print axioms IRComparison.WordLoopFacts.letValue
#print axioms IRComparison.WordLoopFacts.letStateAlias
#print axioms IRComparison.WordLoopFacts.letState
#print axioms IRComparison.WordLoopFacts.bindValue
#print axioms IRComparison.WordLoopFacts.sequence
#print axioms IRComparison.WordLoopFacts.branchCmd
#print axioms IRComparison.WordLoopFacts.unitSequence
#print axioms IRComparison.WordFrontendFacts.unitSequence
#print axioms IRComparison.WordFrontend.ScalarEnvironment.materialize_eq_substitute
#print axioms IRComparison.WordFrontend.StructuralBody.Substitution.apply_eq
#print axioms IRComparison.WordFrontend.StructuralBody.under_reference
#print axioms IRComparison.WordFrontend.ScalarSyntax.complete
#print axioms IRComparison.WordFrontend.ScalarSyntax.complete_loaded
#print axioms IRComparison.WordFrontend.Certificate.store_step_complete
#print axioms IRComparison.WordFrontend.StructuralSyntax.complete
#print axioms IRComparison.DependencyClosure.walk_contains
#print axioms IRComparison.LeanLibrary.installTypes_present
#print axioms IRComparison.LeanLibrary.Declaration.signature_unique
#print axioms IRComparison.WordFrontend.loaded_library_signature
#print axioms IRComparison.WordFrontend.ScalarSyntax.register_complete
#print axioms IRComparison.WordFrontend.ScalarSyntax.select_complete
#print axioms IRComparison.WordFrontend.StructuralLoop.body_forStatic_complete
#print axioms IRComparison.WordFrontend.StructuralLoop.yield_complete
#print axioms IRComparison.WordFrontend.StructuralStep.sequence_complete
#print axioms IRComparison.WordFrontend.StructuralStep.Conditional.complete
#print axioms IRComparison.WordFrontend.StructuralStep.Alias.alias_step_complete
#print axioms IRComparison.WordFrontend.StructuralReadBind.complete
#print axioms IRComparison.WordFrontend.StructuralReadBind.letValue_step_complete
#print axioms IRComparison.WordFrontend.StructuralStateLet.complete
#print axioms IRComparison.WordFrontend.StructuralStateLet.Loop.complete
#print axioms IRComparison.WordFrontend.StructuralUnit.complete
#print axioms IRComparison.WordFrontend.ScopedSyntax.syntax_complete
#print axioms IRComparison.WordFrontend.ScopedSyntax.complete
#print axioms IRComparison.WordFrontend.Certificate.Step.direct_beta_conversion_domain
#print axioms IRComparison.WordFrontend.Certificate.For.unit_beta_conversion

#print axioms IRComparison.DependencyClosure.walk_closed
#print axioms IRComparison.DependencyClosure.walk_reachable
#print axioms IRComparison.WordFrontend.loaded_reachable_signature
#print axioms IRComparison.WordFrontend.ScalarEnvironment.retarget_same_complete
#print axioms IRComparison.WordFrontend.ScalarEnvironment.retarget_cast_complete
#print axioms IRComparison.WordFrontend.ScalarEnvironment.reference_complete
#print axioms IRComparison.WordFrontend.ScalarSyntax.binary_visit_complete
#print axioms IRComparison.WordFrontend.Arithmetic.AliasSetup.scalar_beta_proved
#print axioms IRComparison.WordFrontend.ScalarConversion.Casts.covered
#print axioms IRComparison.WordFrontend.ScalarConversion.let_visit_complete
#print axioms IRComparison.WordFrontend.Arithmetic.neg_finish

#print axioms IRComparison.WordFrontend.ScalarSyntax.parameter_visit_complete
#print axioms IRComparison.WordFrontend.ScalarSyntax.index_visit_complete
#print axioms IRComparison.WordFrontend.ScalarSyntax.local_visit_complete
#print axioms IRComparison.WordFrontend.ScalarSyntax.literal_visit_complete
#print axioms IRComparison.WordFrontend.ScalarSyntax.neg_visit_complete
#print axioms IRComparison.WordFrontend.ScalarSyntax.select_visit_complete
#print axioms IRComparison.WordFrontend.ScalarSyntax.register_visit_complete
#print axioms IRComparison.WordFrontend.ScalarConversion.beta_visit_complete
#print axioms IRComparison.WordFrontend.LexicalScalarSyntax.complete
#print axioms IRComparison.WordFrontend.LexicalScalarSyntax.parse_complete
#print axioms IRComparison.WordFrontend.ScopedSyntax.scalar_complete

#print axioms IRComparison.WordFrontend.Certificate.continuation_beta_conversion_with_domain
#print axioms IRComparison.WordFrontend.WordBinder.Annotation.domain_proved
#print axioms IRComparison.WordFrontend.WordBinder.Annotation.function_conversion
#print axioms IRComparison.WordFrontend.WordBinder.Annotation.continuation_conversion
#print axioms IRComparison.WordFrontend.WordBinder.let_complete
#print axioms IRComparison.WordFrontend.WordBinder.step_let_complete
#print axioms IRComparison.WordFrontend.NaturalLoop.body_forRange_complete
#print axioms IRComparison.WordFrontend.loaded_source_signature
#print axioms IRComparison.WordFrontend.NativeCompleteness.SourceTable.installed
#print axioms IRComparison.WordFrontend.ScopedSyntax.Syntax.install
#print axioms IRComparison.WordFrontend.ScopedSyntax.Library.install

#print axioms IRComparison.WordFrontend.StandardLibrary.library
#print axioms IRComparison.WordFrontend.StandardLibrary.checkEntries_complete
#print axioms IRComparison.WordFrontend.StandardLibrary.check_complete
#print axioms IRComparison.WordFrontend.SignatureClosure.selected_subset
#print axioms IRComparison.WordFrontend.loaded_types_closed_in_scope
#print axioms IRComparison.WordFrontend.NativeEnvironment.scope_complete
#print axioms IRComparison.WordFrontend.NativeEnvironment.checkClosed_complete
#print axioms IRComparison.WordFrontend.NativeEnvironment.wordShape
#print axioms IRComparison.WordFrontend.NativeEnvironment.checkWordShape_complete
#print axioms IRComparison.WordFrontend.NativeEnvironment.fresh_of_not_library
#print axioms IRComparison.WordFrontend.NativeEnvironment.prepare_complete
#print axioms IRComparison.WordFrontend.compileWith_code_of_body
#print axioms IRComparison.WordFrontend.NatNotation.view_complete
#print axioms IRComparison.WordFrontend.Arithmetic.Signatures.natural_notation_typed
#print axioms IRComparison.WordFrontend.FixedCopyCompleteness.source_syntax

#print axioms IRComparison.LeanStructuralConversion.prove_application_cast_complete
#print axioms IRComparison.WordFrontend.Arithmetic.AliasSetup.scalar_beta_checked_domain_proved
#print axioms IRComparison.WordFrontend.WordBinder.Annotation.result
#print axioms IRComparison.WordFrontend.WordBinder.Annotation.substitute_native
#print axioms IRComparison.WordFrontend.WordBinder.Annotation.view_complete
#print axioms IRComparison.WordFrontend.NativeEnvironment.header_complete
#print axioms IRComparison.WordFrontend.NativeEnvironment.input_complete

#print axioms IRComparison.WordFrontend.StructuralBody.closureReference_scoped
#print axioms IRComparison.WordFrontend.StructuralBody.closureBody_scoped
#print axioms IRComparison.WordFrontend.StructuralBody.lambdaChain_scoped
#print axioms IRComparison.WordFrontend.StructuralBody.LambdaSource.parts
#print axioms IRComparison.WordFrontend.StructuralBody.LambdaSource.capture
#print axioms IRComparison.WordFrontend.StructuralBody.LambdaSource.call_scoped
#print axioms IRComparison.WordFrontend.StructuralSyntax.HeadForm.parser_congr
#print axioms IRComparison.WordFrontend.Arithmetic.AliasSetup.helper_proved
#print axioms IRComparison.WordFrontend.Certificate.For.helper_equality_conversion
#print axioms IRComparison.WordFrontend.StructuralBody.applicationHead_app
#print axioms IRComparison.WordFrontend.StructuralSyntax.helper_retarget_complete

#print axioms IRComparison.WordFrontend.Arithmetic.AliasSetup.function_state_none
#print axioms IRComparison.WordFrontend.Arithmetic.AliasSetup.function_word_none
#print axioms IRComparison.WordFrontend.StructuralSyntax.function_let_step_complete
#print axioms IRComparison.WordFrontend.FunctionSyntax.BindingValue.construct
#print axioms IRComparison.WordFrontend.FunctionSyntax.branch_complete
#print axioms IRComparison.WordFrontend.FunctionSyntax.sequence_complete
#print axioms IRComparison.WordFrontend.FunctionSyntax.complete
#print axioms IRComparison.WordFrontend.FunctionSyntax.Syntax.install

#print axioms IRComparison.WordFrontend.Certificate.finish_checked_complete
#print axioms IRComparison.WordFrontend.Read.Signatures.annotationDictionary
#print axioms IRComparison.WordFrontend.Read.Signatures.bits_header_typed
#print axioms IRComparison.WordFrontend.Read.Signatures.bits_source_typed
#print axioms IRComparison.WordFrontend.Read.element_equality_conversion
#print axioms IRComparison.WordFrontend.Read.bits_finish_complete
#print axioms IRComparison.WordFrontend.Read.bits_nat_complete
#print axioms IRComparison.WordFrontend.Read.bits_word_complete
#print axioms IRComparison.WordFrontend.WordBinder.bind_equality_conversion
#print axioms IRComparison.WordFrontend.WordBinder.bind_bits_complete
#print axioms IRComparison.WordFrontend.WordBinder.bind_bits_complete_code

#print axioms IRComparison.WordFrontend.WordBinder.checked_option_bitvec
#print axioms IRComparison.WordFrontend.WordBinder.step_bind_bits_complete

#print axioms IRComparison.WordFrontend.StructuralBody.finishBody_code
#print axioms IRComparison.WordFrontend.StructuralBody.retargetPiece_code
#print axioms IRComparison.WordFrontend.Certificate.Return.assign_step_split_complete_code
#print axioms IRComparison.WordFrontend.Read.bits_nat_complete_code
#print axioms IRComparison.WordFrontend.ScalarSyntax.local_visit_complete_code
#print axioms IRComparison.WordFrontend.FixedReadCompleteness.source_syntax
#print axioms IRComparison.WordFrontend.FixedReadCompleteness.body_complete

#print axioms IRComparison.WordFrontend.StructuralSyntax.mapped_bindValue
#print axioms IRComparison.WordFrontend.StructuralSyntax.mapped_letValue

#print axioms IRComparison.WordFrontend.FixedReadCompleteness.source_syntax_at

#print axioms IRComparison.WordFrontend.FixedReadCompleteness.body_complete_at

#print axioms IRComparison.WordFrontend.ScopedSyntax.head_form

#print axioms IRComparison.WordFrontend.Certificate.sequence_step_complete_code

#print axioms IRComparison.WordFrontend.Certificate.store_step_invariant_complete_code

#print axioms IRComparison.WordFrontend.Certificate.Return.body_skip_invariant_complete_code

#print axioms IRComparison.WordFrontend.WordBinder.let_complete_code

#print axioms IRComparison.WordFrontend.ScalarSyntax.literal_visit_complete_code

#print axioms IRComparison.WordFrontend.ScalarSyntax.index_visit_complete_code

#print axioms IRComparison.WordFrontend.ScalarSyntax.binary_visit_complete_code

#print axioms IRComparison.WordFrontend.ScalarSyntax.parameter_visit_complete_code

#print axioms IRComparison.WordFrontend.ScalarSyntax.register_visit_complete_code

#print axioms IRComparison.WordFrontend.ScalarSyntax.neg_visit_complete_code

#print axioms IRComparison.WordFrontend.FixedSequenceCompleteness.Source.declared

#print axioms IRComparison.WordFrontend.FixedSequenceCompleteness.Source.computation

#print axioms IRComparison.WordFrontend.FixedSequenceCompleteness.Source.complete

#print axioms IRComparison.WordFrontend.FixedScalarCompleteness.Source.declared

#print axioms IRComparison.WordFrontend.FixedScalarCompleteness.Source.computation

#print axioms IRComparison.WordFrontend.FixedScalarCompleteness.Source.complete


#print axioms IRComparison.WordFrontend.Read.nat_step_invariant_complete_code

#print axioms IRComparison.WordFrontend.Read.word_step_split_complete_code

#print axioms IRComparison.WordFrontend.Read.bits_word_complete_code

#print axioms IRComparison.WordFrontend.Certificate.bindValue_step_complete_code

#print axioms IRComparison.WordFrontend.ScopedSyntax.represented_head

#print axioms IRComparison.WordFrontend.FixedReadSourceCompleteness.Source.declared

#print axioms IRComparison.WordFrontend.FixedReadSourceCompleteness.Source.computation

#print axioms IRComparison.WordFrontend.FixedReadSourceCompleteness.Source.valueForm

#print axioms IRComparison.WordFrontend.FixedReadSourceCompleteness.Source.complete

#print axioms IRComparison.WordFrontend.StructuralLoop.value_skip_complete_code

#print axioms IRComparison.WordFrontend.StructuralLoop.value_assign_split_complete_code

#print axioms IRComparison.WordFrontend.StructuralLoop.yield_complete_code

#print axioms IRComparison.WordFrontend.StructuralLoop.body_forStatic_complete_code

#print axioms IRComparison.WordFrontend.StructuralStateLet.complete_code

#print axioms IRComparison.WordFrontend.StructuralStateLet.Loop.complete_code

#print axioms IRComparison.WordFrontend.StructuralStep.sequence_complete_code

#print axioms IRComparison.WordFrontend.StructuralReadBind.complete_code

#print axioms IRComparison.WordFrontend.WordBinder.step_let_complete_code

#print axioms IRComparison.WordFrontend.WordBinder.step_bind_bits_complete_code

#print axioms IRComparison.WordFrontend.StructuralUnit.complete_code

#print axioms IRComparison.WordFrontend.FixedSequenceCompleteness.StaticBound.typed

#print axioms IRComparison.WordFrontend.NaturalLoop.body_forRange_complete_code

#print axioms IRComparison.LeanTypeReduction.unfoldConstant_kind

#print axioms IRComparison.WordFrontend.Arithmetic.decEqTail_typed

#print axioms IRComparison.WordFrontend.Arithmetic.AliasSetup.base_universe

#print axioms IRComparison.WordFrontend.Arithmetic.AliasSetup.decision_step

#print axioms IRComparison.WordFrontend.Arithmetic.AliasSetup.decision_function

#print axioms IRComparison.WordFrontend.NativeEnvironment.decEqShape

#print axioms IRComparison.WordFrontend.NativeEnvironment.checkDecEqShape_complete

#print axioms IRComparison.WordFrontend.Certificate.Branch.booleanDecision_represents

#print axioms IRComparison.WordFrontend.Certificate.Branch.BooleanLibrary.header_typed

#print axioms IRComparison.WordFrontend.Certificate.Branch.BooleanLibrary.condition_typed

#print axioms IRComparison.WordFrontend.Certificate.Branch.branch_step_split_complete_code

#print axioms IRComparison.WordFrontend.StructuralStep.Conditional.split_complete_code

#print axioms IRComparison.WordFrontend.ScalarSyntax.select_visit_complete_code

#print axioms IRComparison.WordFrontend.ScalarEnvironment.lookup_selected_complete

#print axioms IRComparison.WordFrontend.ScalarEnvironment.reference_complete_code


#print axioms IRComparison.WordFrontend.ScalarEnvironment.Unbound.lookup_none

#print axioms IRComparison.WordFrontend.ScalarConversion.let_visit_complete_code

#print axioms IRComparison.WordFrontend.ScalarConversion.beta_visit_complete_code


#print axioms IRComparison.WordFrontend.LexicalScalarCode.Source.computation

#print axioms IRComparison.WordFrontend.LexicalScalarCode.Source.complete

#print axioms IRComparison.WordFrontend.LexicalScalarCode.Source.install

#print axioms IRComparison.WordFrontend.LexicalScalarCode.Source.parse_complete

#print axioms IRComparison.WordFrontend.FixedScalarCompleteness.Scoped.declared

#print axioms IRComparison.WordFrontend.FixedScalarCompleteness.Scoped.computation

#print axioms IRComparison.WordFrontend.FixedScalarCompleteness.Scoped.complete

#print axioms IRComparison.WordFrontend.FixedScalarCompleteness.Scoped.install

#print axioms IRComparison.WordFrontend.FixedReadSourceCompleteness.Source.install

#print axioms IRComparison.WordFrontend.FixedSequenceCompleteness.Source.install


#print axioms IRComparison.WordFrontend.FunctionSyntax.branch_complete_code

#print axioms IRComparison.WordFrontend.FunctionSyntax.sequence_complete_code

#print axioms IRComparison.WordFrontend.FixedFunctionCompleteness.Source.declared

#print axioms IRComparison.WordFrontend.FixedFunctionCompleteness.Source.computation

#print axioms IRComparison.WordFrontend.FixedFunctionCompleteness.Source.install

#print axioms IRComparison.WordFrontend.FixedFunctionCompleteness.Source.complete


#print axioms IRComparison.WordFrontend.AnnotatedLiteral.typed

#print axioms IRComparison.WordFrontend.AnnotatedLiteral.fact_typed

#print axioms IRComparison.WordFrontend.AnnotatedLiteral.visit_complete

#print axioms IRComparison.WordFrontend.Certificate.For.BoundSignatures.binary_header_typed

#print axioms IRComparison.WordFrontend.Certificate.For.Bound.binary

#print axioms IRComparison.LeanStructuralConversion.prove_application_or_same_complete
#print axioms IRComparison.WordFrontend.Arithmetic.AliasSetup.basic_values_none_of_types
#print axioms IRComparison.WordFrontend.Arithmetic.AliasSetup.heterogeneous_proved
#print axioms IRComparison.WordFrontend.AnnotatedBinary.dictionary_typed
#print axioms IRComparison.WordFrontend.AnnotatedBinary.header_typed
#print axioms IRComparison.WordFrontend.AnnotatedBinary.value_typed
#print axioms IRComparison.WordFrontend.AnnotatedBinary.dictionary_proved
#print axioms IRComparison.WordFrontend.AnnotatedBinary.header_proved
#print axioms IRComparison.WordFrontend.AnnotatedBinary.value_proved
#print axioms IRComparison.WordFrontend.ScalarConversion.binary_expected_proved
#print axioms IRComparison.WordFrontend.ScalarConversion.annotated_binary_finish
#print axioms IRComparison.WordFrontend.AnnotatedBinary.visit_complete_code

#print axioms IRComparison.WordFrontend.WordBinder.let_certificate
#print axioms IRComparison.WordFrontend.FunctionSyntax.letValue_complete_code
#print axioms IRComparison.WordFrontend.FunctionSyntax.branch_typed_complete_code

#print axioms IRComparison.WordFrontend.StructuralLoop.yield_certificate
#print axioms IRComparison.WordFrontend.StructuralLoop.mapped_forStatic_complete_code
#print axioms IRComparison.WordFrontend.FunctionSyntax.stepSequence_complete_code
#print axioms IRComparison.WordFrontend.FunctionSyntax.yield_complete_code
#print axioms IRComparison.WordFrontend.FunctionSyntax.stepBranch_complete_code
#print axioms IRComparison.WordFrontend.WordBinder.step_let_certificate
#print axioms IRComparison.WordFrontend.FunctionSyntax.stepLetValue_complete_code
#print axioms IRComparison.WordFrontend.FunctionSyntax.step_helper_retarget_complete
#print axioms IRComparison.WordFrontend.FunctionSyntax.step_functionLet_complete

#print axioms IRComparison.WordFrontend.WordBinder.mapped_bind_bits_complete_code
#print axioms IRComparison.WordFrontend.WordBinder.mapped_step_bind_bits_complete_code
#print axioms IRComparison.WordFrontend.FunctionSyntax.readWord_complete_code
#print axioms IRComparison.WordFrontend.FunctionSyntax.stepReadWord_complete_code

#print axioms IRComparison.WordFrontend.Certificate.StateAlias.alias_certificate
#print axioms IRComparison.WordFrontend.StructuralStep.Alias.mapped_alias_complete_code
#print axioms IRComparison.WordFrontend.FunctionSyntax.stateAlias_complete_code
#print axioms IRComparison.WordFrontend.FunctionSyntax.stepAlias_complete_code
#print axioms IRComparison.WordFrontend.NaturalLoop.mapped_forRange_complete_code
#print axioms IRComparison.WordFrontend.FunctionSyntax.valueAssign_congr
#print axioms IRComparison.WordFrontend.StructuralStateLet.mapped_complete_code
#print axioms IRComparison.WordFrontend.StructuralStateLet.Loop.mapped_complete_code
#print axioms IRComparison.WordFrontend.StructuralUnit.mapped_complete_code

#print axioms IRComparison.WordFrontend.AnnotatedNeg.header_typed
#print axioms IRComparison.WordFrontend.AnnotatedNeg.header_proved
#print axioms IRComparison.WordFrontend.AnnotatedNeg.value_proved
#print axioms IRComparison.WordFrontend.ScalarConversion.expected_value_proved
#print axioms IRComparison.WordFrontend.ScalarConversion.neg_expected_proved
#print axioms IRComparison.WordFrontend.ScalarConversion.annotated_neg_finish
#print axioms IRComparison.WordFrontend.AnnotatedNeg.visit_complete_code

#print axioms IRComparison.WordFrontend.AnnotatedLiteral.annotation_typed
#print axioms IRComparison.WordFrontend.AnnotatedCondition.dictionary_proved
#print axioms IRComparison.WordFrontend.AnnotatedCondition.header_proved
#print axioms IRComparison.WordFrontend.AnnotatedCondition.literal_proved
#print axioms IRComparison.WordFrontend.AnnotatedCondition.test_proved
#print axioms IRComparison.WordFrontend.AnnotatedCondition.condition_proved
#print axioms IRComparison.WordFrontend.AnnotatedCondition.decidable_proved
#print axioms IRComparison.WordFrontend.AnnotatedCondition.Casts.covered
#print axioms IRComparison.WordFrontend.AnnotatedCondition.choice_proved
#print axioms IRComparison.WordFrontend.AnnotatedCondition.choice_equality_proved
#print axioms IRComparison.WordFrontend.AnnotatedCondition.ChoiceConditions.conversion
#print axioms IRComparison.WordFrontend.AnnotatedBranch.finish_complete
#print axioms IRComparison.WordFrontend.AnnotatedBranch.visit_complete_code
#print axioms IRComparison.WordFrontend.AnnotatedBranch.Loop.finish_complete
#print axioms IRComparison.WordFrontend.AnnotatedBranch.Loop.visit_complete_code

#print axioms IRComparison.WordFrontend.Certificate.Branch.ite_checked_typed
#print axioms IRComparison.WordFrontend.AnnotatedCondition.choice_with_prefix_proved
#print axioms IRComparison.WordFrontend.AnnotatedCondition.scalar_choice_proved
#print axioms IRComparison.WordFrontend.AnnotatedCondition.scalar_choice_typed
#print axioms IRComparison.WordFrontend.AnnotatedCondition.scalarSource_typed
#print axioms IRComparison.WordFrontend.ScalarConversion.select_expected_proved
#print axioms IRComparison.WordFrontend.AnnotatedSelect.finish_complete
#print axioms IRComparison.WordFrontend.AnnotatedSelect.visit_complete_code

#print axioms IRComparison.WordFrontend.LexicalScalarCode.Source.evidence
#print axioms IRComparison.WordFrontend.LexicalScalarCode.Evidence.variable
#print axioms IRComparison.WordFrontend.LexicalScalarCode.Evidence.lift
#print axioms IRComparison.WordFrontend.LexicalScalarCode.ScopeTyped.lift
#print axioms IRComparison.WordFrontend.LexicalScalarCode.ScopeTyped.nextWord
#print axioms IRComparison.WordFrontend.LexicalScalarCode.ScopeTyped.initial
#print axioms IRComparison.WordFrontend.LexicalScalarCode.Source.binaryInferred
#print axioms IRComparison.WordFrontend.LexicalScalarCode.Source.negInferred
#print axioms IRComparison.WordFrontend.LexicalScalarCode.Source.selectInferred
#print axioms IRComparison.WordFrontend.FixedScalarCompleteness.Source.lexical
#print axioms IRComparison.WordFrontend.FixedScalarCompleteness.Scoped.asLexical
#print axioms IRComparison.WordFrontend.FixedScalarCompleteness.Scoped.evidence
#print axioms IRComparison.WordFrontend.FixedFunctionCompleteness.Source.branchInferred
#print axioms IRComparison.WordFrontend.FixedFunctionCompleteness.Source.stepBranchInferred
#print axioms IRComparison.WordFrontend.StandardLibrary.closed

#print axioms IRComparison.LeanStructuralConversion.prove_reduction_right_complete_types
#print axioms IRComparison.WordFrontend.Arithmetic.AliasSetup.scalar_beta_checked_domain_types
#print axioms IRComparison.WordFrontend.LexicalScalarCode.expand_cons
#print axioms IRComparison.WordFrontend.LexicalScalarCode.Source.bindingEvidence
#print axioms IRComparison.WordFrontend.LexicalScalarCode.Source.letInferred
#print axioms IRComparison.WordFrontend.LexicalScalarCode.Source.betaInferred

#print axioms IRComparison.WordFrontend.LexicalScalarCode.ScopeTyped.nextState
#print axioms IRComparison.WordFrontend.LexicalScalarCode.ScopeTyped.forStatic
#print axioms IRComparison.WordFrontend.LexicalScalarCode.Evidence.naturalIndex
#print axioms IRComparison.WordFrontend.LexicalScalarCode.ScopeTyped.withLocal
#print axioms IRComparison.WordFrontend.LexicalScalarCode.ScopeTyped.naturalLoop

#print axioms IRComparison.WordFrontend.FixedFunctionCompleteness.closure_single


#print axioms IRComparison.WordFrontend.LexicalScalarCode.expand_open
#print axioms IRComparison.WordFrontend.LexicalScalarCode.ValuesTyped.open
#print axioms IRComparison.WordFrontend.LexicalScalarCode.Source.bindingEvidenceOfEvidence
#print axioms IRComparison.WordFrontend.LexicalScalarCode.Source.bindingEvidenceOpen
#print axioms IRComparison.WordFrontend.LexicalScalarCode.Source.letOpen
#print axioms IRComparison.WordFrontend.LexicalScalarCode.Source.betaOpen
#print axioms IRComparison.WordFrontend.FixedSequenceCompleteness.Source.facts
#print axioms IRComparison.WordFrontend.FixedFunctionCompleteness.Source.facts
#print axioms IRComparison.FrontendLexicalGeneration.retainedCaptureHLS.wordBody_correct

-- Shared lexical helper construction and its ordinary-Lean integration.
#print axioms IRComparison.WordFrontend.FunctionSyntax.letSubstitution_apply
#print axioms IRComparison.WordFrontend.FunctionSyntax.let_representations
#print axioms IRComparison.WordFrontend.FunctionSyntax.lambdaSource_typed
#print axioms IRComparison.WordFrontend.FunctionSyntax.functionType_typed
#print axioms IRComparison.WordFrontend.FunctionSyntax.functionArguments_typed
#print axioms IRComparison.WordFrontend.FixedFunctionCompleteness.Source.bodyTyping
#print axioms IRComparison.WordFrontend.FixedFunctionCompleteness.Source.stepBodyTyping
#print axioms IRComparison.WordFrontend.FixedFunctionCompleteness.Source.functionLetInferred
#print axioms IRComparison.WordFrontend.FixedFunctionCompleteness.Source.stepFunctionLetInferred
#print axioms IRComparison.WordFrontend.FixedFunctionCompleteness.Source.bodyNotLambda
#print axioms IRComparison.WordFrontend.FixedFunctionCompleteness.Source.lambdaTyping
#print axioms IRComparison.WordFrontend.FixedFunctionCompleteness.Source.functionLetFromLambda
#print axioms IRComparison.WordFrontend.FixedFunctionCompleteness.Source.stepFunctionLetFromLambda
#print axioms IRComparison.WordFrontend.FixedFunctionCompleteness.Source.stateFunctionLetFromSource
#print axioms IRComparison.FrontendGenerationConditions.twoArgumentHelperHLS.wordBody_correct

-- Captured arguments: shared substitution and source-call connection.
#print axioms IRComparison.WordFrontend.FunctionSyntax.closureReference_append
#print axioms IRComparison.WordFrontend.FunctionSyntax.closureSubstitution_append
#print axioms IRComparison.WordFrontend.FunctionSyntax.closureSubstitution_append_represents
#print axioms IRComparison.WordFrontend.FunctionSyntax.lambdaSource_apply_represents
#print axioms IRComparison.WordFrontend.FunctionSyntax.closureCall_representations
#print axioms IRComparison.WordFrontend.FunctionSyntax.BindingValue.application_parts

-- Convertible helper argument spines and the common closure dispatch.
#print axioms IRComparison.LeanTypeReduction.step_apply_checked_complete
#print axioms IRComparison.LeanTypeReduction.applyReduced_typed
#print axioms IRComparison.LeanTypeReduction.checked_spine_typed
#print axioms IRComparison.LeanTypeReduction.exact_spine_prefix_typed
#print axioms IRComparison.LeanTypeReduction.step_checked_spine_complete
#print axioms IRComparison.LeanTypeReduction.ArgumentsCasts.application_typed
#print axioms IRComparison.WordFrontend.Arithmetic.ValueForm.checkedArguments
#print axioms IRComparison.WordFrontend.Arithmetic.AliasSetup.helper_checked_proved
#print axioms IRComparison.WordFrontend.Certificate.For.helper_checked_equality_conversion
#print axioms IRComparison.WordFrontend.LexicalScalarCode.expand_state_scoped
#print axioms IRComparison.WordFrontend.ScalarSyntax.Form.lexical
#print axioms IRComparison.WordFrontend.LexicalScalarCode.ExternalAt.lift
#print axioms IRComparison.WordFrontend.LexicalScalarCode.expand_scoped
#print axioms IRComparison.WordFrontend.LexicalScalarCode.Source.independent
#print axioms IRComparison.WordFrontend.FixedScalarCompleteness.Scoped.independent
#print axioms IRComparison.WordFrontend.FixedReadSourceCompleteness.Source.independent
#print axioms IRComparison.WordFrontend.FixedReadSourceCompleteness.constructSource
#print axioms IRComparison.WordFrontend.FixedSequenceCompleteness.represented_scoped
#print axioms IRComparison.WordFrontend.FixedSequenceCompleteness.reduced_scoped
#print axioms IRComparison.WordFrontend.FixedSequenceCompleteness.Source.independent
#print axioms IRComparison.WordFrontend.FixedSequenceCompleteness.constructAtomSource
#print axioms IRComparison.WordFrontend.FixedSequenceCompleteness.constructSource
#print axioms IRComparison.WordFrontend.FixedFunctionCompleteness.Source.independent
#print axioms IRComparison.WordFrontend.FixedFunctionCompleteness.constructFunctionSource
#print axioms IRComparison.WordFrontend.LexicalScalarCode.expand_scoped_compared
#print axioms IRComparison.WordFrontend.LexicalScalarCode.Source.compareLocals
#print axioms IRComparison.WordFrontend.FixedSequenceCompleteness.InputConditions.valueAssign
#print axioms IRComparison.WordFrontend.FixedSequenceCompleteness.InputConditions.yield
#print axioms IRComparison.WordFrontend.FixedSequenceCompleteness.InputConditions.forStatic
#print axioms IRComparison.WordFrontend.FixedFunctionCompleteness.argumentsFromSyntax
#print axioms IRComparison.WordFrontend.FixedFunctionCompleteness.argumentsTypedFromSyntax
#print axioms IRComparison.WordFrontend.LexicalScalarCode.Source.stateOnly
#print axioms IRComparison.WordFrontend.LexicalScalarSyntax.Form.constructSource
#print axioms IRComparison.WordFrontend.LexicalScalarSyntax.expand_cons
#print axioms IRComparison.WordFrontend.LexicalScalarSyntax.Form.evidence
#print axioms IRComparison.WordFrontend.LexicalScalarSyntax.Form.binaryInferred
#print axioms IRComparison.WordFrontend.LexicalScalarSyntax.Form.negInferred
#print axioms IRComparison.WordFrontend.LexicalScalarSyntax.Form.selectInferred
#print axioms IRComparison.WordFrontend.LexicalScalarSyntax.Form.bindingEvidence
#print axioms IRComparison.WordFrontend.LexicalScalarSyntax.Form.letFromTyping
#print axioms IRComparison.WordFrontend.LexicalScalarSyntax.Form.betaFromTyping
#print axioms IRComparison.WordFrontend.ScalarSyntax.sameTerm_application_variable
#print axioms IRComparison.WordFrontend.ScalarSyntax.Separated.initialApplication
#print axioms IRComparison.WordFrontend.FixedScalarCompleteness.Scoped.fromSyntax
#print axioms IRComparison.WordFrontend.FunctionSyntax.closureSubstitution_at_capture
#print axioms IRComparison.WordFrontend.FunctionSyntax.closureSubstitution_shift_empty
#print axioms IRComparison.WordFrontend.FunctionSyntax.Scope.coherent_empty
#print axioms IRComparison.WordFrontend.FunctionSyntax.Closure.SourceAt.shift
#print axioms IRComparison.WordFrontend.FunctionSyntax.BindingValue.sourceAt
#print axioms IRComparison.WordFrontend.FunctionSyntax.Scope.Coherent.functionLet
#print axioms IRComparison.WordFrontend.FunctionSyntax.Scope.Coherent.under
#print axioms IRComparison.WordFrontend.FunctionSyntax.Scope.lookup_parameters
#print axioms IRComparison.WordFrontend.FunctionSyntax.Scope.Coherent.applyArguments
#print axioms IRComparison.WordFrontend.FunctionSyntax.substitution_applications
#print axioms IRComparison.WordFrontend.FunctionSyntax.application_spine
#print axioms IRComparison.WordFrontend.FunctionSyntax.BindingValue.call_representations
#print axioms IRComparison.WordFrontend.FunctionSyntax.functionType_suffix_closed
#print axioms IRComparison.LeanTypeInference.CheckedTyping.install


#print axioms IRComparison.WordFrontend.FunctionSyntax.syntax_complete

#print axioms IRComparison.WordFrontend.FunctionSyntax.Syntax.bodyTyping

#print axioms IRComparison.WordFrontend.FunctionSyntax.lambdaTypingFromBody

#print axioms IRComparison.WordFrontend.FunctionSyntax.Syntax.lambdaTyping

#print axioms IRComparison.WordFrontend.FunctionSyntax.Syntax.functionLetFromLambda


#print axioms IRComparison.WordFrontend.FixedFunctionCompleteness.boundCallTypingFromSyntax

#print axioms IRComparison.WordFrontend.FixedFunctionCompleteness.Source.toEntry


#print axioms IRComparison.WordFrontend.FixedSequenceCompleteness.InputConditions.assign

#print axioms IRComparison.WordFrontend.FunctionSyntax.lambda_prefix_retag
#print axioms IRComparison.WordFrontend.FunctionSyntax.lambdaTelescope_typed
#print axioms IRComparison.WordFrontend.FunctionSyntax.lambdaPrefixesFromBody
#print axioms IRComparison.WordFrontend.FixedFunctionCompleteness.argumentsWithTypesFromSyntax

#print axioms IRComparison.WordFrontend.ScalarSyntax.Decision.mono
#print axioms IRComparison.WordFrontend.ScalarSyntax.Decision.instantiate
#print axioms IRComparison.WordFrontend.LexicalScalarCode.Evidence.instantiateExact
#print axioms IRComparison.WordFrontend.LexicalScalarSyntax.ValueShape.instantiateExact
#print axioms IRComparison.WordFrontend.LexicalScalarSyntax.ValueShape.instantiateSome
#print axioms IRComparison.WordFrontend.LexicalScalarSyntax.Form.renameCache
#print axioms IRComparison.WordFrontend.LexicalScalarSyntax.Form.closeExact
#print axioms IRComparison.WordFrontend.LexicalScalarSyntax.Form.closeOpenExact
#print axioms IRComparison.WordFrontend.LexicalScalarSyntax.StaticRegisters.rename
#print axioms IRComparison.WordFrontend.LexicalScalarSyntax.Form.bindingFromOpen
#print axioms IRComparison.WordFrontend.LexicalScalarSyntax.Form.letFromOpen
#print axioms IRComparison.WordFrontend.LexicalScalarSyntax.Form.betaFromOpen
#print axioms IRComparison.WordFrontend.ScalarSyntax.ReferenceScope.separated
#print axioms IRComparison.WordFrontend.ScalarSyntax.ReferenceScope.initial
#print axioms IRComparison.WordFrontend.ScalarSyntax.ReferenceScope.lift
#print axioms IRComparison.WordFrontend.ScalarSyntax.ReferenceScope.scalar
#print axioms IRComparison.WordFrontend.ScalarSyntax.ReferenceScope.state
#print axioms IRComparison.WordFrontend.ScalarSyntax.ReferenceScope.forStatic
#print axioms IRComparison.WordFrontend.ScalarSyntax.ReferenceScope.forIn
#print axioms IRComparison.WordFrontend.ScalarSyntax.ReferenceScope.fold
#print axioms IRComparison.WordFrontend.FunctionSyntax.Syntax.sourceTyping
#print axioms IRComparison.WordFrontend.FunctionSyntax.Syntax.helperPrefixes

#print axioms IRComparison.WordFrontend.FixedFunctionCompleteness.argumentsWithShapesFromSyntax
#print axioms IRComparison.WordFrontend.FixedFunctionCompleteness.argumentsTypedWithShapesFromSyntax

#print axioms IRComparison.WordFrontend.FunctionSyntax.Syntax.functionLetFromLambdaMode
#print axioms IRComparison.WordFrontend.FunctionSyntax.sourceBindTyping
#print axioms IRComparison.WordFrontend.FunctionSyntax.sourceBooleanTyping
#print axioms IRComparison.WordFrontend.FunctionSyntax.sourceForStaticTyping
#print axioms IRComparison.WordFrontend.FunctionSyntax.sourceForRangeTyping
#print axioms IRComparison.WordFrontend.FunctionSyntax.sourceBinderTyping
#print axioms IRComparison.WordFrontend.FixedSequenceCompleteness.InputConditions.choice
#print axioms IRComparison.WordFrontend.FixedSequenceCompleteness.InputConditions.returnVariable

#print axioms IRComparison.WordFrontend.LexicalScalarSyntax.expand_substituteCache
#print axioms IRComparison.WordFrontend.LexicalScalarSyntax.under_substituteCache
#print axioms IRComparison.WordFrontend.LexicalScalarSyntax.sourceReference_cons
#print axioms IRComparison.WordFrontend.LexicalScalarSyntax.expand_rename_cons
#print axioms IRComparison.WordFrontend.LexicalScalarSyntax.substituteCache_cons
#print axioms IRComparison.WordFrontend.LexicalScalarSyntax.Form.substituteCache
#print axioms IRComparison.WordFrontend.LexicalScalarSyntax.Form.materialize
#print axioms IRComparison.WordFrontend.LexicalScalarSyntax.Form.instantiateFromSyntax
#print axioms IRComparison.WordFrontend.LexicalScalarSyntax.ValueShape.instantiateAt
#print axioms IRComparison.WordFrontend.LexicalScalarCode.Evidence.instantiateAt
#print axioms IRComparison.WordFrontend.FunctionSyntax.parameterScope
#print axioms IRComparison.WordFrontend.FunctionSyntax.parameterInputs_retag
#print axioms IRComparison.WordFrontend.FunctionSyntax.parameterInputs_prefix
#print axioms IRComparison.WordFrontend.FunctionSyntax.parameterTypes_prefix

#print axioms IRComparison.WordFrontend.StructuralBody.bindArgument_complete
#print axioms IRComparison.WordFrontend.StructuralBody.retainArguments_bind_complete
#print axioms IRComparison.WordFrontend.StructuralBody.compileRetained_correct
#print axioms IRComparison.RetainedArgumentExamples.updateArgument_snapshot
#print axioms IRComparison.RetainedArgumentExamples.severalArguments_snapshot

#print axioms IRComparison.WordFrontend.ScopedSyntax.compile_of_parser_rule_with_code
#print axioms IRComparison.WordFrontend.NativeEnvironment.Input.compilesInstalledCodeWith
#print axioms IRComparison.WordFrontend.FunctionSyntax.BindingValue.retained_call_complete

#print axioms IRComparison.WordFrontend.FixedFunctionCompleteness.generatesRetainedSyntax
#print axioms IRComparison.WordFrontend.FixedFunctionCompleteness.Source.completeArguments
#print axioms IRComparison.WordFrontend.StructuralBody.unitArgument_of_type
#print axioms IRComparison.WordFrontend.StructuralBody.ArgumentBindings.complete
#print axioms IRComparison.WordFrontend.StructuralBody.ArgumentBindings.facts
#print axioms IRComparison.WordFrontend.StructuralBody.ArgumentBindings.install
#print axioms IRComparison.WordFrontend.StructuralBody.ArgumentBindings.scalarFromSyntax

#print axioms IRComparison.WordFrontend.RetainedConversion.conversion_complete
#print axioms IRComparison.WordFrontend.RetainedConversion.prefix_endpoint
#print axioms IRComparison.WordFrontend.RetainedConversion.reducePrefix_checkedBeta
#print axioms IRComparison.WordFrontend.RetainedConversion.reducePrefix_beta
#print axioms IRComparison.WordFrontend.RetainedConversion.reducePrefix_mono
#print axioms IRComparison.WordFrontend.StructuralBody.retargetRetainedPiece_of_retarget
#print axioms IRComparison.WordFrontend.StructuralBody.ArgumentBindings.context_growth
#print axioms IRComparison.WordFrontend.StructuralBody.ArgumentBindings.argument_count
#print axioms IRComparison.WordFrontend.FunctionSyntax.closureSubstitution_instantiate
#print axioms IRComparison.WordFrontend.FunctionSyntax.closureSubstitution_retain_actual

#print axioms IRComparison.LeanBindings.substitute_instantiate
#print axioms IRComparison.WordFrontend.RetainedConversion.contractLets_substitute
#print axioms IRComparison.WordFrontend.RetainedConversion.contractLets_represents
#print axioms IRComparison.WordFrontend.RetainedConversion.Prefix.typed
#print axioms IRComparison.WordFrontend.RetainedConversion.Prefix.instN
#print axioms IRComparison.WordFrontend.RetainedConversion.Prefix.complete
#print axioms IRComparison.WordFrontend.RetainedConversion.conversion_of_prefix
#print axioms IRComparison.WordFrontend.StructuralBody.argumentAnnotation_of_type
#print axioms IRComparison.WordFrontend.StructuralBody.ArgumentBindings.endpointInputs
#print axioms IRComparison.WordFrontend.StructuralBody.ArgumentBindings.contract
#print axioms IRComparison.WordFrontend.StructuralBody.ArgumentBindings.contract_represents
#print axioms IRComparison.WordFrontend.StructuralBody.ArgumentBindings.prefix
#print axioms IRComparison.WordFrontend.StructuralBody.ArgumentBindings.prefix_complete
#print axioms IRComparison.WordFrontend.StructuralBody.retargetRetainedPiece_of_prefix
#print axioms IRComparison.WordFrontend.FunctionSyntax.BindingValue.retained_call_representations
#print axioms IRComparison.WordFrontend.FunctionSyntax.BindingValue.retained_call_complete_with_transport
#print axioms IRComparison.WordFrontend.FixedFunctionCompleteness.Source.retainedPrefix

#print axioms IRComparison.WordFrontend.RetainedConversion.conversion_checked_call
#print axioms IRComparison.WordFrontend.StructuralBody.retargetRetainedPiece_of_conversion
#print axioms IRComparison.WordFrontend.StructuralBody.retargetRetainedPiece_checked_call
#print axioms IRComparison.WordFrontend.StructuralBody.RetainedCasts.equalityPrefix
#print axioms IRComparison.WordFrontend.FixedFunctionCompleteness.Source.completeRetainedCall

#print axioms IRComparison.LeanStructuralConversion.conversion_of_ordinary

#print axioms IRComparison.LeanStructuralConversion.conversion_of_retained

#print axioms IRComparison.LeanStructuralConversion.ordinary_of_prove

#print axioms IRComparison.WordFrontend.RetainedConversion.Prefix.length_le

#print axioms IRComparison.WordFrontend.Arithmetic.AliasSetup.covers_source_ordinary

#print axioms IRComparison.WordFrontend.StructuralSyntax.helper_retained_retarget_complete

#print axioms IRComparison.WordFrontend.FunctionSyntax.step_helper_retained_retarget_complete

#print axioms IRComparison.WordFrontend.StructuralBody.retargetRetainedPiece_typed_call

#print axioms IRComparison.WordFrontend.FunctionSyntax.BindingValue.retained_call_from_body

#print axioms IRComparison.WordFrontend.FunctionSyntax.lambdaSource_apply_scoped

#print axioms IRComparison.WordFrontend.FunctionSyntax.application_spine_scoped

#print axioms IRComparison.WordFrontend.StructuralBody.ArgumentBindings.independent

#print axioms IRComparison.WordFrontend.StructuralBody.ArgumentBindings.syntax

#print axioms IRComparison.WordFrontend.StructuralBody.ArgumentBindings.Syntax.install

#print axioms IRComparison.WordFrontend.FunctionSyntax.Syntax.retainedCallFromSourceBodies

#print axioms IRComparison.WordFrontend.FunctionSyntax.Syntax.retainedCallFromLambdaBodies

#print axioms IRComparison.WordFrontend.FixedFunctionCompleteness.retainedScalarCallFromSyntax


#print axioms IRComparison.WordFrontend.FixedFunctionCompleteness.generatesRetainedSyntaxInstalled

#print axioms IRComparison.WordFrontend.FunctionSyntax.closureSubstitution_open_scalar

#print axioms IRComparison.WordFrontend.FunctionSyntax.BindingValue.openedScalar

#print axioms IRComparison.WordFrontend.FixedFunctionCompleteness.retainedScalarCallFromOpenBody

#print axioms IRComparison.WordFrontend.FixedFunctionCompleteness.retainedCallFromSourceScope

#print axioms IRComparison.FrontendGenerationConditions.retainedOpenStateHelperHLS.wordBody_correct

#print axioms IRComparison.WordFrontend.LexicalScalarSyntax.expand_liftCache
#print axioms IRComparison.WordFrontend.LexicalScalarSyntax.Form.liftScalar
#print axioms IRComparison.WordFrontend.StructuralBody.ArgumentBindings.fromSyntax
#print axioms IRComparison.WordFrontend.StructuralBody.ArgumentBindings.endpointScope
#print axioms IRComparison.WordFrontend.FixedFunctionCompleteness.retainedCallFromSourceArguments

#print axioms IRComparison.WordFrontend.FunctionSyntax.openArguments_length
#print axioms IRComparison.WordFrontend.FunctionSyntax.closureSubstitution_open_next
#print axioms IRComparison.WordFrontend.FunctionSyntax.lambdaSource_opened
#print axioms IRComparison.WordFrontend.FunctionSyntax.BindingValue.openedArguments
#print axioms IRComparison.WordFrontend.FunctionSyntax.Syntax.retainedCallFromBodyTypes
#print axioms IRComparison.WordFrontend.StructuralBody.ArgumentBindings.scalarLayout
#print axioms IRComparison.WordFrontend.FixedFunctionCompleteness.retainedScalarArgumentsFromOpenBody
#print axioms IRComparison.WordFrontend.FixedReadSourceCompleteness.Conditions.word
#print axioms IRComparison.WordFrontend.FixedSequenceCompleteness.InputConditions.readBind
#print axioms IRComparison.FrontendGenerationConditions.retainedTwoOpenBindingsHLS.wordBody_correct

#print axioms IRComparison.WordFrontend.LexicalScalarCode.Evidence.notState

#print axioms IRComparison.WordFrontend.FixedFunctionCompleteness.sourceArgumentCases
#print axioms IRComparison.WordFrontend.FunctionSyntax.parameterLayout_state
#print axioms IRComparison.WordFrontend.FunctionSyntax.parameterLayout_scalar
#print axioms IRComparison.WordFrontend.FunctionSyntax.parameterLayout_open
#print axioms IRComparison.WordFrontend.FunctionSyntax.parameterLayout_scope
#print axioms IRComparison.WordFrontend.FunctionSyntax.argumentTypes_lift
#print axioms IRComparison.WordFrontend.StructuralBody.ArgumentBindings.parameterLayout
#print axioms IRComparison.WordFrontend.FunctionSyntax.parameterShapes_prefix
#print axioms IRComparison.WordFrontend.FunctionSyntax.parameterLayout_scalars
#print axioms IRComparison.WordFrontend.FunctionSyntax.argumentTypes_of_representations
#print axioms IRComparison.WordFrontend.FixedFunctionCompleteness.retainedArgumentsFromBodyFamily
#print axioms IRComparison.FrontendGenerationConditions.retainedMixedReadHLS.wordBody_correct

#print axioms IRComparison.WordFrontend.FunctionSyntax.sourceCheckedBindTyping
#print axioms IRComparison.WordFrontend.FunctionSyntax.sourceCheckedLetTyping
#print axioms IRComparison.WordFrontend.FunctionSyntax.sourceReadBindTyping
#print axioms IRComparison.WordFrontend.FunctionSyntax.Syntax.functionLetFromLambdaPaired
#print axioms IRComparison.WordFrontend.FunctionSyntax.Syntax.valueAssignPaired
#print axioms IRComparison.WordFrontend.FunctionSyntax.Syntax.stateLetPaired
#print axioms IRComparison.WordFrontend.FunctionSyntax.Syntax.bindValuePaired
#print axioms IRComparison.WordFrontend.FunctionSyntax.Syntax.stepBindValuePaired
#print axioms IRComparison.WordFrontend.FunctionSyntax.Syntax.booleanBranchPaired
#print axioms IRComparison.FrontendGenerationConditions.helperReadContinuationHLS.wordBody_correct

#print axioms IRComparison.WordFrontend.FunctionSyntax.Syntax.valueCurrentPaired
#print axioms IRComparison.WordFrontend.FunctionSyntax.Syntax.yieldPaired
#print axioms IRComparison.WordFrontend.FunctionSyntax.Syntax.sequencePaired
#print axioms IRComparison.WordFrontend.FunctionSyntax.Syntax.stepSequencePaired
#print axioms IRComparison.WordFrontend.FunctionSyntax.Syntax.forStaticPaired
#print axioms IRComparison.WordFrontend.FunctionSyntax.Syntax.forRangePaired
#print axioms IRComparison.WordFrontend.FixedSequenceCompleteness.InputConditions.forRange
#print axioms IRComparison.FrontendGenerationConditions.helperLoopContinuationHLS.wordBody_correct
#print axioms IRComparison.FrontendGenerationConditions.naturalForIdentityHLS.wordBody_correct
#print axioms IRComparison.FrontendGenerationConditions.naturalFoldIdentityHLS.wordBody_correct

#print axioms IRComparison.WordFrontend.NaturalLoop.source_typed_state
#print axioms IRComparison.WordFrontend.OrdinarySource.Scalar.typing
#print axioms IRComparison.WordFrontend.OrdinarySource.StateValue.typing
#print axioms IRComparison.WordFrontend.OrdinarySource.Read.typing
#print axioms IRComparison.WordFrontend.OrdinarySource.Arguments.applyTyping
#print axioms IRComparison.WordFrontend.OrdinarySource.Function.typing
#print axioms IRComparison.WordFrontend.OrdinarySource.Body.typing
#print axioms IRComparison.WordFrontend.OrdinarySource.Body.wellScoped
#print axioms IRComparison.WordFrontend.OrdinarySource.Function.wellScoped
#print axioms IRComparison.WordFrontend.OrdinarySource.Function.retag
#print axioms IRComparison.WordFrontend.OrdinarySource.Body.retag
#print axioms IRComparison.WordFrontend.OrdinarySource.Body.typingRetagged
#print axioms IRComparison.WordFrontend.OrdinarySource.Body.typingPrefixes
#print axioms IRComparison.WordFrontend.OrdinarySource.Arguments.evidence
#print axioms IRComparison.WordFrontend.OrdinarySource.retainedCall
#print axioms IRComparison.WordFrontend.OrdinarySource.functionLetIdentity

#print axioms IRComparison.WordFrontend.FunctionSyntax.lambdaSource_represents
#print axioms IRComparison.WordFrontend.OrdinarySource.Function.Flow.demandsTyped
#print axioms IRComparison.WordFrontend.OrdinarySource.Body.Flow.demandsTyped
#print axioms IRComparison.WordFrontend.OrdinarySource.DemandsTyped.valueBound
#print axioms IRComparison.WordFrontend.OrdinarySource.TypedMapping.identity
#print axioms IRComparison.WordFrontend.OrdinarySource.TypedMapping.under
#print axioms IRComparison.WordFrontend.OrdinarySource.TypedMapping.underClosed
#print axioms IRComparison.WordFrontend.OrdinarySource.TypedMapping.consClosed
#print axioms IRComparison.WordFrontend.OrdinarySource.TypedMapping.prepend
#print axioms IRComparison.WordFrontend.OrdinarySource.Signature.Spelling.substitute
#print axioms IRComparison.WordFrontend.OrdinarySource.mappingUnderRepresented
#print axioms IRComparison.WordFrontend.OrdinarySource.typingMapped
#print axioms IRComparison.WordFrontend.OrdinarySource.checkedTypingMapped
#print axioms IRComparison.WordFrontend.OrdinarySource.openMapping_represented
#print axioms IRComparison.WordFrontend.OrdinarySource.lambdaSourceMapped_represents
#print axioms IRComparison.WordFrontend.OrdinarySource.Body.typingPrefixesMapped
#print axioms IRComparison.WordFrontend.OrdinarySource.Arguments.evidenceMapped
#print axioms IRComparison.WordFrontend.OrdinarySource.scalarShapeMapped
#print axioms IRComparison.WordFrontend.OrdinarySource.Scalar.evidenceMapped
#print axioms IRComparison.WordFrontend.OrdinarySource.Body.typingMapped
#print axioms IRComparison.WordFrontend.OrdinarySource.Function.typingMapped
#print axioms IRComparison.WordFrontend.OrdinarySource.StateRef.current
#print axioms IRComparison.WordFrontend.OrdinarySource.CurrentMapping.underValue
#print axioms IRComparison.WordFrontend.OrdinarySource.currentMapping_state
#print axioms IRComparison.WordFrontend.OrdinarySource.currentMapping_range
#print axioms IRComparison.WordFrontend.OrdinarySource.currentMapping_staticRange
#print axioms IRComparison.WordFrontend.OrdinarySource.CurrentMapping.functionLet
#print axioms IRComparison.WordFrontend.OrdinarySource.retainedCallMapped
#print axioms IRComparison.WordFrontend.OrdinarySource.functionLet

#print axioms IRComparison.WordFrontend.OrdinarySource.Context.lookup_origin
#print axioms IRComparison.WordFrontend.OrdinarySource.initialMapping
#print axioms IRComparison.WordFrontend.OrdinarySource.openParameterMapping
#print axioms IRComparison.WordFrontend.OrdinarySource.Function.bindMapping
#print axioms IRComparison.WordFrontend.OrdinarySource.Body.typingEntry
#print axioms IRComparison.WordFrontend.OrdinarySource.freeVariables_succ
#print axioms IRComparison.WordFrontend.OrdinarySource.stateVariables_underValue
#print axioms IRComparison.WordFrontend.OrdinarySource.stateVariables_letScalar
#print axioms IRComparison.WordFrontend.OrdinarySource.stateVariables_betaScalar
#print axioms IRComparison.WordFrontend.OrdinarySource.CurrentMapping.appLeft
#print axioms IRComparison.WordFrontend.OrdinarySource.CurrentMapping.appRight
#print axioms IRComparison.WordFrontend.OrdinarySource.ScalarFrame.scalarShape
#print axioms IRComparison.WordFrontend.OrdinarySource.StateRef.mappedReference
#print axioms IRComparison.WordFrontend.OrdinarySource.ScalarFrame.evidence
#print axioms IRComparison.WordFrontend.OrdinarySource.ScalarFrame.initial
#print axioms IRComparison.WordFrontend.OrdinarySource.openScalarForm
#print axioms IRComparison.WordFrontend.OrdinarySource.ScalarFrame.underScalar
#print axioms IRComparison.WordFrontend.OrdinarySource.liftReferenceForm
#print axioms IRComparison.WordFrontend.OrdinarySource.prependReferenceForm
#print axioms IRComparison.WordFrontend.OrdinarySource.ScalarFrame.underNatural
#print axioms IRComparison.WordFrontend.OrdinarySource.ScalarFrame.underAdministrative
#print axioms IRComparison.WordFrontend.OrdinarySource.ScalarFrame.underState
#print axioms IRComparison.WordFrontend.OrdinarySource.ScalarFrame.underUnit
#print axioms IRComparison.WordFrontend.OrdinarySource.ScalarFrame.underStaticRange
#print axioms IRComparison.WordFrontend.OrdinarySource.ScalarFrame.underNaturalRange
#print axioms IRComparison.WordFrontend.OrdinarySource.ScalarFrame.bindFunction
#print axioms IRComparison.WordFrontend.OrdinarySource.scalarBindingFromRetained
#print axioms IRComparison.WordFrontend.OrdinarySource.Scalar.forms
#print axioms IRComparison.WordFrontend.OrdinarySource.Read.forms
#print axioms IRComparison.WordFrontend.OrdinarySource.mapStateSet
#print axioms IRComparison.WordFrontend.OrdinarySource.StateValue.forms
#print axioms IRComparison.WordFrontend.OrdinarySource.StateValue.returnSyntax
#print axioms IRComparison.WordFrontend.OrdinarySource.RegisterMapping.initial
#print axioms IRComparison.WordFrontend.OrdinarySource.RegisterMapping.under
#print axioms IRComparison.WordFrontend.OrdinarySource.RegisterMapping.substitute
#print axioms IRComparison.WordFrontend.OrdinarySource.Function.mappedHead
#print axioms IRComparison.WordFrontend.OrdinarySource.RegisterMapping.functionLet
#print axioms IRComparison.WordFrontend.OrdinarySource.RegisterMapping.closure

#print axioms IRComparison.WordFrontend.OrdinarySource.DemandsTyped.retag
#print axioms IRComparison.WordFrontend.OrdinarySource.substitute_closed
#print axioms IRComparison.WordFrontend.OrdinarySource.ScalarFrame.tail
#print axioms IRComparison.WordFrontend.OrdinarySource.ScalarFrame.bindHeld
#print axioms IRComparison.WordFrontend.OrdinarySource.ScalarFrame.openParameter
#print axioms IRComparison.WordFrontend.OrdinarySource.ScalarFrame.shiftTarget
#print axioms IRComparison.WordFrontend.OrdinarySource.Parameter.extendTyped
#print axioms IRComparison.WordFrontend.OrdinarySource.scalarLetSyntax
#print axioms IRComparison.WordFrontend.OrdinarySource.stateLetSyntax
#print axioms IRComparison.WordFrontend.OrdinarySource.readBindSyntax
#print axioms IRComparison.WordFrontend.OrdinarySource.branchSyntax
#print axioms IRComparison.WordFrontend.OrdinarySource.staticBoundMapped
#print axioms IRComparison.WordFrontend.OrdinarySource.staticRangeSyntax
#print axioms IRComparison.WordFrontend.OrdinarySource.naturalRangeSyntax
#print axioms IRComparison.WordFrontend.OrdinarySource.writeSyntax
#print axioms IRComparison.WordFrontend.OrdinarySource.copySyntax
#print axioms IRComparison.WordFrontend.OrdinarySource.stateBindSyntax
#print axioms IRComparison.WordFrontend.OrdinarySource.unitBindSyntax
#print axioms IRComparison.WordFrontend.OrdinarySource.targetContext_append
#print axioms IRComparison.WordFrontend.OrdinarySource.targetInputs_append
#print axioms IRComparison.WordFrontend.OrdinarySource.targetContext_length
#print axioms IRComparison.WordFrontend.OrdinarySource.ScalarFrame.captureExtension
#print axioms IRComparison.WordFrontend.OrdinarySource.StateLinks.refl
#print axioms IRComparison.WordFrontend.OrdinarySource.StateLinks.cons
#print axioms IRComparison.WordFrontend.OrdinarySource.StateLinks.current
#print axioms IRComparison.WordFrontend.OrdinarySource.ArgumentBindings.heldEnvironment

#print axioms IRComparison.WordFrontend.OrdinarySource.Context.Related.append

#print axioms IRComparison.WordFrontend.OrdinarySource.targetTyped

#print axioms IRComparison.WordFrontend.OrdinarySource.ScalarFrame.atCapture

#print axioms IRComparison.WordFrontend.OrdinarySource.Argument.retainedCase

#print axioms IRComparison.WordFrontend.OrdinarySource.Arguments.retained

#print axioms IRComparison.WordFrontend.OrdinarySource.Argument.unitSafe

#print axioms IRComparison.WordFrontend.OrdinarySource.Arguments.unitSafe

#print axioms IRComparison.WordFrontend.OrdinarySource.FunctionMeaning.extend

#print axioms IRComparison.WordFrontend.OrdinarySource.FunctionMeaning.invoke

#print axioms IRComparison.WordFrontend.OrdinarySource.FunctionMeaning.ofLambda

#print axioms IRComparison.WordFrontend.OrdinarySource.FunctionEnvironment.extendTarget

#print axioms IRComparison.WordFrontend.OrdinarySource.FunctionEnvironment.pushValue

#print axioms IRComparison.WordFrontend.OrdinarySource.FunctionEnvironment.under

#print axioms IRComparison.WordFrontend.OrdinarySource.FunctionEnvironment.bindFunction

#print axioms IRComparison.WordFrontend.OrdinarySource.FunctionEnvironment.parameters

#print axioms IRComparison.WordFrontend.OrdinarySource.FunctionEnvironment.captureExtension

#print axioms IRComparison.WordFrontend.OrdinarySource.Function.Flow.interpret

#print axioms IRComparison.WordFrontend.OrdinarySource.Body.Flow.interpret

#print axioms IRComparison.WordFrontend.OrdinarySource.Body.syntaxEntry

#print axioms IRComparison.WordFrontend.OrdinarySource.Body.Current.cast

#print axioms IRComparison.WordFrontend.OrdinarySource.generates

#print axioms IRComparison.WordFrontend.Certificate.body_copy_invariant_complete_code
