import IRComparison.Circuit.Layout
import IRComparison.Circuit.MemoryProjection

namespace IRComparison.Circuit

def layoutLimit (layout : Array (Nat × Nat)) := layout.foldl (fun n p => max n (p.1+1)) 0

theorem layout_fold_bound (entries : List (Nat × Nat)) (base : Nat) :
    base ≤ entries.foldl (fun n p => max n (p.1+1)) base ∧
      ∀ p ∈ entries, p.1 < entries.foldl (fun n p => max n (p.1+1)) base := by
  induction entries generalizing base with
  | nil => exact ⟨Nat.le_refl _,by simp⟩
  | cons p ps ih =>
    have hh := ih (max base (p.1+1))
    refine ⟨?_,?_⟩
    · exact Nat.le_trans (Nat.le_max_left _ _) hh.1
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _)) hh.1
      · exact hh.2 q hq

theorem layout_member_bound (h : (a,n) ∈ layout.toList) : a < layoutLimit layout := by
  have hh := (layout_fold_bound layout.toList 0).2 (a,n) h
  simpa only [Array.foldl_toList,layoutLimit] using hh

theorem source_layout_bound (covered : layoutCovers layout code = true) (member : a ∈ sourceArrays code) :
    a < layoutLimit layout := by
  obtain ⟨n,hn⟩ := layoutCovers_sound covered a member
  exact layout_member_bound hn

theorem observe_trim (safe : ∀ a ∈ outputs, a < limit) (s : State) :
    PipelineUse.observe outputs (trimState limit s) = PipelineUse.observe outputs s := by
  unfold PipelineUse.observe trimState
  congr 1
  apply List.map_congr_left
  intro a ha
  simp [safe a ha]

end IRComparison.Circuit
