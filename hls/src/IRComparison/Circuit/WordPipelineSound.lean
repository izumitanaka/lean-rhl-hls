import IRComparison.Circuit.Backend
import IRComparison.Hybrid.HybridWordGlobal

namespace IRComparison.Circuit

theorem certify_artifact (h : certify a = .ok checked) : checked.artifact = a := by
  unfold certify at h
  cases hs : checkStorage a with
  | error => simp [hs,bind,Except.bind] at h
  | ok certificate =>
    simp only [hs,bind,Except.bind] at h
    split at h
    · cases hi : inferInvariant a with
      | error e => simp [hi,bind,Except.bind] at h
      | ok table =>
        simp only [hi,bind,Except.bind] at h
        split at h
        · cases h; rfl
        · cases h
    · cases h

theorem checkLayout_covered (h : checkLayout layout code = .ok ()) : layoutCovers layout code = true := by
  by_cases hc : layoutCovers layout code = true
  · exact hc
  · by_cases hd : (layout.toList.map Prod.fst).eraseDups.length = layout.size
    · simp [checkLayout,hd,hc,bind,Except.bind,pure,Except.pure] at h
    · simp [checkLayout,hd,hc,bind,Except.bind,pure,Except.pure] at h

theorem compile_facts (h : compile layout code = .ok checked) :
    checked.artifact = lower layout code ∧ layoutCovers layout code = true ∧
      hasSendBounds code = true ∧ checkCommunication code = .ok () := by
  unfold compile at h
  cases hl : checkLayout layout code with
  | error => simp [hl,bind,Except.bind] at h
  | ok u =>
    cases u
    cases hb : checkSendBudgets code with
    | error => simp [hl,hb,bind,Except.bind] at h
    | ok u =>
      cases u
      cases hc : checkCommunication code with
      | error => simp [hl,hb,hc,bind,Except.bind] at h
      | ok u =>
        cases u
        simp only [hl,hb,hc,bind,Except.bind] at h
        exact ⟨certify_artifact h,checkLayout_covered hl,checkSendBudgets_sound hb,rfl⟩

/-- Native BV32 source kernels through memory optimization, either control
route, allocation, assembly, and checked finite-width arithmetic. -/
theorem word_pipeline_finishes (p : HybridWord.Plan outputs sizes ks)
    (compiled : compile layout (HybridUnifiedPipeline.lower p) = .ok checked)
    (outputsSafe : ∀ a ∈ outputs, a < layoutLimit layout)
    (s : HybridWord.State) (x y : HybridWord.Word)
    (sized : PipelineShapes.Layout sizes s.encode)
    (ready : p.Ready (HybridWord.encode x) (HybridWord.encode y) s.encode) :
    let machine := checked.artifact.machine
    let wr := fun n => checked.artifact.wires[n]?.getD zeroRange
    ∃ cycles result, (machine.bitRun wr cycles (machine.start s.encode (HybridWord.encode x) (HybridWord.encode y))).result = some result ∧
      result.map (PipelineUse.observe outputs) =
        (HybridWord.source x y ks s).map (fun t => PipelineUse.observe outputs t.encode) := by
  obtain ⟨same,covered,known,communication⟩ := compile_facts compiled
  obtain ⟨cycles,result,hr,ho⟩ := unified_pipeline_finishes p layout covered known communication outputsSafe s.encode
    (HybridWord.encode x) (HybridWord.encode y) sized ready
  refine ⟨cycles,result,?_,?_⟩
  · rw [checked.execution,same]
    exact hr
  · simpa only [HybridWord.source_correct,Option.map_map,Function.comp_def] using ho

end IRComparison.Circuit
