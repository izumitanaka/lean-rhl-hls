import PaperCore.BufferNames

namespace PaperCore.WindowNames
open BufferNames

def names (variables : List Var) (count : Nat) : List Var := (List.range count).map (name variables)

theorem names_distinct (variables : List Var) (count : Nat) : (names variables count).Nodup := by
  have mapDistinct : ∀ xs : List Nat, xs.Nodup → (xs.map (name variables)).Nodup := by
    intro xs distinct
    induction xs with
    | nil => simp
    | cons x rest ih =>
      apply List.nodup_cons.mpr
      constructor
      · intro member
        obtain ⟨j,hj,equal⟩ := List.mem_map.mp member
        have same := BufferNames.injective equal
        subst j
        exact (List.nodup_cons.mp distinct).1 hj
      · exact ih (List.nodup_cons.mp distinct).2
  exact mapDistinct _ List.nodup_range

def refillNames (variables : List Var) (overlap delta : Nat) : List Var :=
  (List.range delta).map (fun n => name variables (overlap+n))

theorem split_names : names variables (overlap+delta) = names variables overlap ++ refillNames variables overlap delta := by
  simp [names,refillNames,List.range_add,List.map_append,List.map_map,Function.comp_def]

theorem all_distinct : (names variables overlap ++ refillNames variables overlap delta).Nodup := by
  rw [← split_names]
  exact names_distinct _ _

theorem all_fresh : ∀ b ∈ names variables overlap ++ refillNames variables overlap delta, b ∉ variables := by
  rw [← split_names]
  intro b member
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
  exact BufferNames.fresh


end PaperCore.WindowNames
