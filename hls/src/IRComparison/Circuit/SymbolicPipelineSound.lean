import IRComparison.Circuit.SymbolicInstructions
import IRComparison.Circuit.ChannelsAllocation
import IRComparison.Circuit.LayoutScope
import IRComparison.Circuit.BudgetCheck

namespace IRComparison.Circuit
open HybridSymbolicGlobal (Instruction)

/-- The finite list below occurs only in a proposition/proof. Neither the
compiler nor its layout/channel/budget checks construct it. -/
theorem symbolic_execute_trim (cs : List Instruction)
    (safe : ∀ c ∈ cs, InstructionScoped limit (symbolicReference c)) :
    (HybridSymbolicGlobal.execute x y cs s qs).map (trimState limit) =
      HybridSymbolicGlobal.execute x y cs (trimState limit s) qs := by
  rw [← symbolicReference_execute,← symbolicReference_execute]
  apply execute_trim
  intro c hc
  obtain ⟨raw,member,rfl⟩ := List.mem_map.mp hc
  exact safe raw member

theorem symbolic_output_member (hc : c ∈ cs) (ha : a ∈ (symbolicOutput c).toList) :
    a ∈ symbolicChannels cs := by
  simp only [symbolicChannels,List.mem_eraseDups,List.mem_flatMap]
  exact ⟨c,hc,List.mem_append_left _ ha⟩

theorem symbolicBudget_fold (cs : List Instruction) (a base : Nat) :
    let total := cs.foldl (fun n c => if symbolicOutput c = some a then max n (symbolicBudget c) else n) base
    base ≤ total ∧ ∀ c ∈ cs, symbolicOutput c = some a → symbolicBudget c ≤ total := by
  induction cs generalizing base with
  | nil => exact ⟨Nat.le_refl _,by simp⟩
  | cons c cs ih =>
    dsimp only [List.foldl_cons]
    split
    next hc =>
      have hh := ih (max base (symbolicBudget c))
      refine ⟨Nat.le_trans (Nat.le_max_left _ _) hh.1,?_⟩
      intro d hd he
      rcases List.mem_cons.mp hd with rfl | ht
      · exact Nat.le_trans (Nat.le_max_right _ _) hh.1
      · exact hh.2 d ht he
    next hc =>
      have hh := ih base
      refine ⟨hh.1,?_⟩
      intro d hd he
      rcases List.mem_cons.mp hd with rfl | ht
      · exact False.elim (hc he)
      · exact hh.2 d ht he

theorem symbolicBudget_member (hc : c ∈ cs) (ha : a ∈ (symbolicOutput c).toList) :
    symbolicBudget c ≤ symbolicCapacity cs a := by
  apply (symbolicBudget_fold cs a 0).2 c hc
  cases ho : symbolicOutput c <;> simp_all

theorem symbolic_layout_scoped (covered : layoutCovers layout (.symbolic cs) = true)
    (communication : checkCommunication (.symbolic cs) = .ok ()) :
    SymbolicScoped (symbolicChannels cs) (layoutLimit layout) cs := by
  have consistent : ∀ c ∈ cs, instructionChannels (symbolicChannels cs) (symbolicReference c) := by
    dsimp only [checkCommunication] at communication
    split at communication
    next hh =>
      intro c hc
      exact of_decide_eq_true (List.all_eq_true.mp hh c hc)
    next => cases communication
  have member : ∀ c ∈ cs, ∀ a ∈ (symbolicInput c :: (symbolicOutput c).toList ++ allCommandArrays (symbolicBody c).body),
      a < layoutLimit layout := by
    intro c hc a ha
    exact source_layout_bound covered (List.mem_flatMap.mpr ⟨c,hc,ha⟩)
  exact ⟨consistent,fun c hc a ha => symbolic_output_member hc ha,
    fun c hc => member c hc _ (by simp),
    fun c hc a ha => member c hc a (by simp [ha]),
    fun c hc a ha => member c hc a (by simp [ha])⟩

/-- Rule-generated counted loops refine the allocated clock machine, including
multiple independent channels in source order. -/
theorem symbolic_pipeline_schedule_with (backend : CountedBackend) (layout : Array (Nat × Nat)) (cs : List Instruction)
    (covered : layoutCovers layout (.symbolic cs) = true)
    (known : hasSendBounds (.symbolic cs) = true)
    (communication : checkCommunication (.symbolic cs) = .ok ())
    (outputsSafe : ∀ a ∈ outputs, a < layoutLimit layout) (s : State) (x y : Int) :
    let generated := scheduleWith backend.build layout (.symbolic cs)
    let machine := generated.schedule.assemble generated.build.queues
    ∃ result, (scheduleWith backend.build layout (.symbolic cs)).schedule.Eval machine.capacity
      ⟨s,(fun n => if n = 0 then x else if n = 1 then y else 0),fun _ => []⟩ result ∧
      result.map (fun p => PipelineUse.observe outputs p.data) =
        (HybridSymbolicGlobal.execute x y cs s (fun _ => [])).map (PipelineUse.observe outputs) := by
  let sizes := fun a => ((layout.toList.find? (fun p => p.1 == a)).map Prod.snd).getD 0
  let b : Build := { memories := layout, nextArray := layoutLimit layout }
  let allocated := allocateChannels (symbolicCapacity cs) (symbolicChannels cs) b
  let mapping := channelLookup allocated.1
  let generated := symbolicInstructionsWith backend.build sizes mapping cs allocated.2
  let machine := generated.1.assemble generated.2.queues
  let p : Payload := ⟨s,(fun n => if n = 0 then x else if n = 1 then y else 0),fun _ => []⟩
  have initialQueues : QueueWellFormed b := ⟨by simp [b],by simp [b]⟩
  have afterAllocation := allocateChannels_queues (symbolicCapacity cs) (symbolicChannels cs) b initialQueues
  have finalQueues := symbolicInstructions_queues_with backend sizes mapping cs allocated.2 afterAllocation
  have table := finalQueues.covers generated.1
  have allocation := allocateChannels_correct (symbolicCapacity cs) (symbolicChannels cs) b
  have allocatedTable := table.before (symbolicInstructions_extension_with backend sizes mapping cs allocated.2)
  have sourceScope := symbolic_layout_scoped covered communication
  have capacity : SymbolicCapacity mapping machine.capacity cs := by
    intro c hc
    have hh := List.all_eq_true.mp known c hc
    cases hb : sendBound (symbolicBody c).body with
    | none => simp [hb] at hh
    | some n =>
      refine ⟨n,rfl,?_⟩
      intro a ha
      exact Nat.le_trans (symbolicBudget_member hc ha) (allocation.capacity allocatedTable (symbolic_output_member hc ha))
  obtain ⟨r,hr,ho⟩ := symbolicInstructions_correct_with backend (x:=x) (y:=y) sizes mapping cs allocated.2
    (by rw [allocation.wires]; change 2 ≤ 2; omega)
    (by rw [allocation.arrays]; exact Nat.le_refl _) allocation.channels sourceScope capacity table p rfl (by simp [p])
  refine ⟨r,hr,?_⟩
  have projected := congrArg (Option.map (PipelineUse.observe outputs)) ho
  have empty : channelView (symbolicChannels cs) mapping p.queues = fun _ => [] := by
    funext a; simp [channelView,p]
  rw [empty,← symbolic_execute_trim cs (fun c hc => symbolic_reference_scope c (sourceScope.input c hc) (sourceScope.body c hc))] at projected
  simpa only [Option.map_map,Function.comp_def,p,observe_trim outputsSafe] using projected

abbrev symbolic_pipeline_schedule {outputs : List Nat} :=
  symbolic_pipeline_schedule_with (outputs:=outputs) CountedBackend.legacy

end IRComparison.Circuit
