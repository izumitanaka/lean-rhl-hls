import IRComparison.Circuit.ChannelsAllocation
import IRComparison.Circuit.LayoutScope
import IRComparison.Circuit.BudgetCheck

namespace IRComparison.Circuit

theorem outputBudget_fold (cs : List HybridIR.Instruction) (a base : Nat) :
    let total := cs.foldl (fun n c => if c.output = some a then max n ((blocksBudget c.blocks).getD 0) else n) base
    base ≤ total ∧ ∀ c ∈ cs, c.output = some a → (blocksBudget c.blocks).getD 0 ≤ total := by
  induction cs generalizing base with
  | nil => exact ⟨Nat.le_refl _,by simp⟩
  | cons c cs ih =>
    dsimp only [List.foldl_cons]
    split
    next hc =>
      have hh := ih (max base ((blocksBudget c.blocks).getD 0))
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

theorem outputBudget_member (hc : c ∈ cs) (ha : a ∈ c.output.toList) :
    (blocksBudget c.blocks).getD 0 ≤ outputBudget cs a := by
  apply (outputBudget_fold cs a 0).2 c hc
  cases ho : c.output <;> simp_all

theorem output_channel_member (hc : c ∈ cs) (ha : a ∈ c.output.toList) : a ∈ channelIds cs := by
  simp only [channelIds,List.mem_eraseDups,List.mem_filterMap]
  refine ⟨c,hc,?_⟩
  cases ho : c.output <;> simp_all

theorem expanded_layout_scoped (covered : layoutCovers layout (.expanded cs) = true)
    (communication : checkCommunication (.expanded cs) = .ok ()) :
    InstructionsScoped (channelIds cs) (layoutLimit layout) cs := by
  have member : ∀ c ∈ cs, ∀ a ∈ (c.input :: c.output.toList ++
        (match c.mode with | .channel a => [a] | .memory a _ _ => [a]) ++
        c.blocks.flatMap (fun b => allCommandArrays b.body)), a < layoutLimit layout := by
    intro c hc a ha
    apply source_layout_bound covered
    exact List.mem_flatMap.mpr ⟨c,hc,ha⟩
  refine ⟨communication_checked communication,fun c hc a ha => output_channel_member hc ha,?_,?_⟩
  · intro c hc
    refine ⟨member c hc c.input (by simp),?_,?_⟩
    · cases hm : c.mode with
      | channel a => exact member c hc a (by simp [hm])
      | memory a order fifo => exact member c hc a (by simp [hm])
    · intro block hb a ha
      exact member c hc a (by simp only [List.mem_cons,List.mem_append]; exact Or.inr (List.mem_flatMap.mpr ⟨block,hb,ha⟩))
  · intro c hc a ha
    exact member c hc a (by simp [ha])

end IRComparison.Circuit
