import IRComparison.Circuit.Observation
import IRComparison.Circuit.Pipelining.BankBounds

namespace IRComparison.Circuit.Pipelining
open SystemVerilog

structure BatchChecks (a : Artifact) (bs : Batches) : Prop where
  entry : a.machine.entry = 0
  size : bs.length+1 ≤ a.storageShape.states
  widths : batchWidthsSafe a.wires.toList bs = true
  initial : initialWidthsSafe a.wires.toList = true
  distinct : ∀ as ∈ bs, BanksDistinct as
  closed : BatchesClosed a.storageShape bs

theorem checkBatch_sound (h : checkBatchArtifact a bs = .ok unit) : BatchChecks a bs := by
  cases hc : checkModuleArtifact a <;> cases hs : checkStorage a <;>
    simp [checkBatchArtifact,hc,hs,bind,Except.bind,pure,Except.pure] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  rename_i entry size widths initial distinct closed
  refine ⟨entry,size,widths,initial,?_,?_⟩
  · simpa only [List.all_eq_true,decide_eq_true_eq] using distinct
  · simpa only [List.all_eq_true,decide_eq_true_eq] using closed

theorem generateBatchModule_components (h : generateBatchModule a bs outputs = .ok code) :
    BatchChecks a bs ∧ ∃ cases emission, generateBatches a bs = .ok (cases,emission) ∧
      code = moduleCode a outputs cases emission.text := by
  cases hc : checkBatchArtifact a bs <;> simp [generateBatchModule,hc,bind,Except.bind] at h
  cases hg : generateBatches a bs <;> simp [hg] at h
  cases hr : checkReadOutputs a outputs <;> simp [hr,pure,Except.pure] at h
  exact ⟨checkBatch_sound hc,_,_,rfl,h.symm⟩

/-- No per-clock proof is requested from the caller: the generator's static
checks imply every numeric and bank-size invariant along the execution. -/
theorem generated_batch_run (generated : generateBatchModule a bs outputs = .ok code)
    (logical : Circuit.Runtime) (initial : BatchBound a bs logical)
    (r : RTL.InterfaceState a.storageShape) (running : r.Running)
    (same : StorageAgreement a.storageShape r.core.decode logical) (cycles : Nat) :
    ∃ result, (Concrete.parseModule code.text).bind (fun parsed => parsed.run a.storageShape cycles r) = some result ∧
      StorageAgreement a.storageShape result.core.decode
        ((batchProgram bs a.machine.capacities).run a.storageShape.wireRange cycles logical) ∧ result.Running := by
  obtain ⟨checks,cases,emission,compiled,rfl⟩ := generateBatchModule_components generated
  have invariant := fun n => batchRun_bound a bs checks.closed checks.widths initial n
  obtain ⟨result,executed,agrees,running'⟩ := physical_batches_run a bs checks.closed checks.distinct compiled logical
    (fun n => (invariant n).storage checks.size)
    (fun n _ => by rw [batchStatements_length]; have := (invariant n).pc; omega)
    r running same cycles
  refine ⟨result,?_,agrees,running'⟩
  rw [batchModule_text a bs outputs generated,SystemVerilog.moduleCode_run]
  exact executed

theorem word_initial_bound (h : initialWidthsSafe f = true) (s : HybridWord.State) (x y : HybridWord.Word) :
    WidthBound f (wordPayload s x y) := by
  have hh : 2 ≤ f.length ∧ (initialWidthFrame f.length).within f = true := by
    simpa [initialWidthsSafe] using h
  refine ⟨DataWords.encoded s,Frame.within_sound hh.2 ?_,by intros; simp_all [wordPayload,Payload.at]⟩
  intro n
  simp only [initialWidthFrame,Frame.get,List.getElem?_map,wordPayload,Payload.at]
  by_cases hn : n < f.length
  · rw [List.getElem?_range hn]
    simp only [Option.map_some,Option.getD_some]
    by_cases h0 : n = 0
    · subst n; simpa using word_encoded x
    · by_cases h1 : n = 1
      · subst n; simpa using word_encoded y
      · simp [h0,h1,show ¬ n < 2 by omega,zeroRange,Interval.Contains]
  · simp [hn,show n ≠ 0 by omega,show n ≠ 1 by omega,zeroRange,Interval.Contains]

theorem realized_rtl_correct (k : HybridWord.Kernel) (b : Build) (hb : 2 ≤ b.wires.size) (ii : Nat)
    (selected : pipelineWord k b ii = (.scheduled code plan,b'))
    (hw : batchWidthsSafe (realize code plan.cycles b'.wires).widths.toList
      (realize code plan.cycles b'.wires).batches = true)
    (hi : initialWidthsSafe (realize code plan.cycles b'.wires).widths.toList = true)
    (s : HybridWord.State) (x y : HybridWord.Word) :
    let r := realize code plan.cycles b'.wires
    ((batchProgram r.batches capacities).run (Frame.get r.widths.toList) (r.batches.length+1)
      ((wordPayload s x y).at 0)).result = some ((k.source x y s).map HybridWord.State.encode) := by
  dsimp only
  rw [batchProgram_correct _ hw _ (word_initial_bound hi s x y),realize_correct]
  obtain ⟨result,he,ho⟩ := pipelineWord_correct k b hb ii s x y (cap := capacityOf capacities)
  rw [selected] at he
  change runCycles _ _ _ _ = result at he
  rw [he,ho]

/-- Observe declared storage and failure, without asserting anything about
padding or source arrays absent from the hardware interface. -/
def SourceObservation (shape : StorageShape) (r : Circuit.Runtime) (expected : Option State) : Prop :=
  ResultObservation shape.registers
    (fun actual final => ∀ n, shape.hasMemory n → actual.arrays n = final.arrays n) r expected

theorem source_observation (same : StorageAgreement shape r logical)
    (h : logical.result = some expected) : SourceObservation shape r expected :=
  ResultObservation.of_agreement same h (fun _ _ arrays => arrays)

/-- Ordinary Lean source → scheduled/reused holding registers → finite RTL
→ the printed SystemVerilog program. All transform/emission arguments are
general; execution starts at an initialized invocation, as in the baseline
backend. Target propagation delays are deliberately outside this theorem. -/
theorem pipelineWord_text_correct (k : HybridWord.Kernel) (b : Build) (hb : 2 ≤ b.wires.size) (ii : Nat)
    (selected : pipelineWord k b ii = (.scheduled source plan,b'))
    (a : Artifact) (layout : a.wires = (realize source plan.cycles b'.wires).widths)
    (generated : generateBatchModule a (realize source plan.cycles b'.wires).batches outputs = .ok code)
    (s : HybridWord.State) (x y : HybridWord.Word) (fits : a.InputFits s.encode)
    (r : RTL.InterfaceState a.storageShape) (running : r.Running)
    (same : StorageAgreement a.storageShape r.core.decode ((wordPayload s x y).at 0)) :
    ∃ result, (Concrete.parseModule code.text).bind (fun parsed =>
      parsed.run a.storageShape ((realize source plan.cycles b'.wires).batches.length+1) r) = some result ∧
      SourceObservation a.storageShape result.core.decode ((k.source x y s).map HybridWord.State.encode) := by
  have checks := (generateBatchModule_components generated).1
  have initial : BatchBound a (realize source plan.cycles b'.wires).batches ((wordPayload s x y).at 0) :=
    ⟨word_initial_bound checks.initial s x y,⟨fits,by intro q; simp [wordPayload,Payload.at,Circuit.Runtime.payload]⟩,by simp [Payload.at]⟩
  obtain ⟨result,executed,agrees,_⟩ := generated_batch_run generated _ initial r running same
    ((realize source plan.cycles b'.wires).batches.length+1)
  refine ⟨result,executed,source_observation agrees ?_⟩
  rw [shape_frame,layout]
  exact realized_rtl_correct k b hb ii selected (by simpa [layout] using checks.widths)
    (by simpa [layout] using checks.initial) s x y

end IRComparison.Circuit.Pipelining
