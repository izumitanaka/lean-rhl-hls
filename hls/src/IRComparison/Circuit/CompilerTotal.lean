import IRComparison.Circuit.ReferenceEmission
import IRComparison.Circuit.PipelineRanges

namespace IRComparison.Circuit
open SystemVerilog.Generation

/-- All sequential nodes generated from the symbolic memory plan satisfy the
actual emitter's local conditions. This is independent of width inference. -/
theorem symbolic_lower_ready (cs : List HybridSymbolicGlobal.Instruction)
    (typed : ∀ c ∈ cs, HybridIR.WordCommand (fun _ => True) c.body)
    (layout : Array (Nat × Nat)) (unique : (layout.toList.map Prod.fst).Nodup)
    (covered : layoutCovers layout (.symbolic cs) = true) :
    let a := lowerWith CountedBackend.named.build layout (.symbolic cs)
    ∀ n ∈ a.machine.nodes.toList, NodeReady a n := by
  let generated := scheduleWith CountedBackend.named.build layout (.symbolic cs)
  have allocated := Allocation.schedule_allocated CountedBackend.named layout unique (.symbolic cs)
  have inventory : ReferenceScope.Inventory generated.build
      (lowerWith CountedBackend.named.build layout (.symbolic cs)) :=
    ⟨rfl,rfl,rfl,allocated.1.memories.unique⟩
  exact (symbolic_schedule_references cs layout unique covered).assemble_ready
    (symbolic_schedule_dataWords cs typed layout) inventory rfl

theorem certify_total (a : Artifact)
    (entry : a.machine.entry < a.machine.nodes.size)
    (closed : ∀ n ∈ a.machine.nodes.toList, n.inStorage a.storageShape)
    (inputs : 2 ≤ a.wires.size)
    (inferred : inferInvariant a = .ok table) (valid : validInvariant a table = true) :
    ∃ built, certify a = .ok built ∧ built.artifact = a := by
  simp only [certify,checkStorage,dif_pos (show a.machine.entry < a.storageShape.states from entry),
    dif_pos closed,dif_pos inputs,inferred,bind,Except.bind,dif_pos valid,pure,Except.pure]
  exact ⟨_,rfl,rfl⟩

/-- The actual memory optimizer, rolled lowering, width checker and complete
SystemVerilog emitter succeed for every declared BV32 source body. No target
checker or successful transformation is a premise. The selected memory plan
is retained, including its buffers and FIFOs. -/
theorem compile_generation (outputs : List Nat) (sizes : Nat → Nat)
    (ks : List HybridWord.Kernel) (layout : Array (Nat × Nat))
    (unique : (layout.toList.map Prod.fst).Nodup)
    (sourceClosed : ∀ k ∈ ks, (∃ n, (k.array,n) ∈ layout.toList) ∧
      k.body.lower.target.ArraysWithin (fun a => ∃ n, (a,n) ∈ layout.toList))
    (ports : ∀ n ∈ outputs, ∃ size, (n,size) ∈ layout.toList) :
    ∃ p built text, HybridWord.compileProgram outputs sizes ks = some p ∧
      compile layout (HybridUnifiedPipeline.lower p) CountedBackend.named.build = .ok built ∧
      built.emit outputs = .ok text := by
  obtain ⟨p,table,hp,layoutChecked,budget,communication,inferred,valid⟩ :=
    compile_rolled_checks outputs sizes ks layout unique sourceClosed
  obtain ⟨program,selected⟩ := symbolic_compile_total outputs sizes
    (HybridUnifiedPipeline.compactStages (ks.map HybridWord.Kernel.lower))
  have form : p = .symbolic program := by
    have eqn : HybridWord.compileProgram outputs sizes ks = some (.symbolic program) := by
      simp [HybridWord.compileProgram,HybridUnifiedPipeline.compile,selected]
    exact Option.some.inj (hp.symm.trans eqn)
  subst p
  have covered : layoutCovers layout (.symbolic program.plan.code) = true := by
    unfold checkLayout at layoutChecked
    simp only [bind,Except.bind,pure,Except.pure] at layoutChecked
    split at layoutChecked <;> simp_all [HybridUnifiedPipeline.lower]
  let a := lowerWith CountedBackend.named.build layout (.symbolic program.plan.code)
  have ready := symbolic_lower_ready program.plan.code
    (program.plan.word (word_compactStages ks)) layout unique covered
  have metadata := Allocation.scheduled_metadata CountedBackend.named layout unique
    (.symbolic program.plan.code) a.machine rfl
  have entry : a.machine.entry < a.machine.nodes.size := by
    have positive := (scheduleWith CountedBackend.named.build layout (.symbolic program.plan.code)).schedule.size_pos
    simp only [a,lowerWith,Schedule.assemble,List.size_toArray,List.length_cons,Schedule.layout_length]
    omega
  have initial := Pipelining.InitialWidths.scheduled_check layout (.symbolic program.plan.code)
  have inputs : 2 ≤ a.wires.size := by
    simp only [Pipelining.initialWidthsSafe,Bool.and_eq_true,decide_eq_true_eq] at initial
    exact initial.1
  obtain ⟨built,certified,same⟩ := certify_total a entry (fun n hn => (ready n hn).1) inputs inferred valid
  obtain ⟨text,emitted⟩ := emit_of_nodes (metadata.moduleReady entry (fun n hn => (ready n hn).1)) ready
    (metadata.ports ports)
  refine ⟨.symbolic program,built,text,hp,?_,?_⟩
  · simp only [compile,layoutChecked,budget,communication,bind,Except.bind]
    exact certified
  · simpa only [Checked.emit,same] using emitted

end IRComparison.Circuit
