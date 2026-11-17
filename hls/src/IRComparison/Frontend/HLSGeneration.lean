import IRComparison.Frontend.CertifiedHLS
import IRComparison.Circuit.CompilerTotal

namespace IRComparison.Circuit

private theorem memorySize_declared (h : memorySize a n = .ok size) : a.storageShape.hasMemory n := by
  unfold memorySize at h
  cases found : a.memories.toList.find? (fun p => p.1 == n) with
  | none => simp [found,throw] at h
  | some p =>
    have member := List.mem_of_find?_eq_some found
    have name := List.find?_some found
    have same : p.1 = n := by simpa only [beq_iff_eq] using name
    apply Allocation.declared_live (size:=p.2)
    simpa only [← same] using member

private theorem checkReadOutputs_declared (h : checkReadOutputs a outputs = .ok ()) :
    ∀ n ∈ outputs, a.storageShape.hasMemory n := by
  induction outputs with
  | nil => simp
  | cons x xs ih =>
    unfold checkReadOutputs at h
    simp only [List.forIn_cons] at h
    cases hx : memorySize a x <;> simp [hx,bind,Except.bind,pure,Except.pure] at h
    rename_i size
    intro n hn
    rcases List.mem_cons.mp hn with rfl | hn
    · exact memorySize_declared hx
    · exact ih h n hn

theorem emit_declared (h : emit a outputs = .ok text) :
    ∀ n ∈ outputs, a.storageShape.hasMemory n := by
  obtain ⟨code,generated,_⟩ := SystemVerilog.emit_module h
  cases hc : checkModuleArtifact a <;> simp [generateModule,hc,bind,Except.bind] at generated
  cases hg : generateCode a <;> simp [hg] at generated
  cases hr : checkReadOutputs a outputs <;> simp [hr,pure,Except.pure] at generated
  exact checkReadOutputs_declared hr

namespace Shared

theorem generateGraphModule_declared (h : generateGraphModule a g outputs = .ok code) :
    ∀ n ∈ outputs, a.storageShape.hasMemory n := by
  obtain ⟨_,_,generated⟩ := generateGraphModule_components h
  cases hc : checkModuleArtifact a <;>
    simp [NetEmission.generateModule,hc,bind,Except.bind] at generated
  cases hg : ((graphCases a g).mapM (statementCode a)).run {} <;> simp [hg] at generated
  cases hr : checkReadOutputs a outputs <;> simp [hr,pure,Except.pure] at generated
  exact checkReadOutputs_declared hr

end Shared

namespace Pipelining

theorem generateGraphModule_declared (h : generateGraphModule a g outputs = .ok code) :
    ∀ n ∈ outputs, a.storageShape.hasMemory n := by
  cases hc : checkGraph a g <;> simp [generateGraphModule,hc,bind,Except.bind] at h
  cases hg : generateGraph a g <;> simp [hg] at h
  cases hr : checkReadOutputs a outputs <;> simp [hr,pure,Except.pure] at h
  exact checkReadOutputs_declared hr

theorem generateBatchModule_declared (h : generateBatchModule a bs outputs = .ok code) :
    ∀ n ∈ outputs, a.storageShape.hasMemory n := by
  cases hc : checkBatchArtifact a bs <;> simp [generateBatchModule,hc,bind,Except.bind] at h
  cases hg : generateBatches a bs <;> simp [hg] at h
  cases hr : checkReadOutputs a outputs <;> simp [hr,pure,Except.pure] at h
  exact checkReadOutputs_declared hr

theorem Integrated.outputs_declared (built : Integrated (outputs:=outputs) p layout fuel) :
    ∀ n ∈ outputs, built.artifact.storageShape.hasMemory n := by
  cases built with
  | sequential b text compiled emitted reason => exact emit_declared emitted
  | structured b compiled => exact Shared.generateGraphModule_declared (Shared.compileStructured_facts compiled).generated
  | pipelined b compiled =>
    obtain ⟨actions,after,linearized,realized,artifact,generated⟩ := (compileOptimizedScheduled_facts compiled).compiled
    exact generateBatchModule_declared generated

end Pipelining
end IRComparison.Circuit

namespace IRComparison.CertifiedHLS
open Circuit Circuit.Pipelining

/-- Declared, typed source bodies always yield actual RTL. Scheduling may pick
any successful optimized route; its fallback preserves the same memory plan. -/
theorem compile_total (entry : Entry source) (outputs : List Nat) (sizes : Nat → Nat)
    (layout : Array (Nat × Nat)) (fuel : Nat) (strategy : LoopStrategy)
    (unique : (layout.toList.map Prod.fst).Nodup)
    (sourceClosed : ∀ k ∈ entry.kernels, (∃ n, (k.array,n) ∈ layout.toList) ∧
      k.body.lower.target.ArraysWithin (fun a => ∃ n, (a,n) ∈ layout.toList))
    (ports : ∀ n ∈ outputs, ∃ size, (n,size) ∈ layout.toList) :
    ∃ result, compile entry outputs sizes layout fuel strategy = .ok result := by
  obtain ⟨plan,built,text,planned,compiled,emitted⟩ :=
    compile_generation outputs sizes entry.kernels layout unique sourceClosed ports
  obtain ⟨backend,integrated⟩ := integrate_total plan layout fuel strategy ⟨built,text,compiled,emitted⟩
  have safe : ∀ a ∈ outputs, a < layoutLimit layout := by
    intro a ha
    obtain ⟨size,member⟩ := ports a ha
    exact layout_member_bound member
  have declared := backend.outputs_declared
  refine ⟨⟨plan,backend,safe,declared⟩,?_⟩
  simp only [compile,planned,finish,integrated,bind,Except.bind,dif_pos safe,dif_pos declared,pure,Except.pure]

end IRComparison.CertifiedHLS
