import IRComparison.Frontend.WordStandardLibrary

/-! Proof-producing construction of the ordinary native signature scope.
The finite graph and declaration representations are the specification;
compiler or parser success is not used to define it. -/
namespace IRComparison.WordFrontend.NativeEnvironment
open Lean4Lean LeanTypeInference

private def Available (native : Lean.Environment) (names : List Lean.Name) : Prop :=
  ∀ n ∈ names, Nonempty (LeanLibrary.Declaration native n)

private def available (native : Lean.Environment) : (names : List Lean.Name) →
    Option (PLift (Available native names))
  | [] => some ⟨by intro n h; cases h⟩
  | n::rest => do
    let declaration ← LeanLibrary.load native n
    let tail ← available native rest
    return ⟨by
      intro m member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨declaration⟩
      · exact tail.down m member⟩

private theorem available_complete (valid : Available native names) :
    ∃ result, available native names = some result := by
  induction names with
  | nil => exact ⟨_,rfl⟩
  | cons n rest ih =>
    obtain ⟨declaration⟩ := valid n (by simp)
    obtain ⟨d,loaded⟩ := declaration.load_complete
    obtain ⟨tail,done⟩ := ih (fun n hn => valid n (List.mem_cons_of_mem _ hn))
    simp only [available,loaded,done,bind,Option.bind]
    exact ⟨_,rfl⟩

structure ScopeResult (native : Lean.Environment) (roots : List Lean.Name) where
  val : List Lean.Name
  property : SignatureClosure native roots val
  walked : dependencies native roots [] = some val

/-- Build the finite dependency scope from ordinary native declarations.
Uniqueness, closure and presence of roots come from the traversal theorem;
they are not obligations exported to the user. -/
def scope (native : Lean.Environment) (roots : List Lean.Name) :
    Option (ScopeResult native roots) :=
  match walked : dependencies native roots [] with
  | none => none
  | some names => do
    if listed : names ⊆ declarationNames native then
      let present ← available native names
      return ⟨names,{
        unique := (DependencyClosure.walk_inventory _ _ roots [] (fun _ => True)
          (by simp) (by simp) (by simp) (by simp) walked).1
        listed := listed
        roots := fun n hn => DependencyClosure.walk_contains _ _ roots [] walked n (Or.inl hn)
        available := present.down
        closed := by
          intro n hn info found d hd
          obtain ⟨ds,eqn,closed⟩ := DependencyClosure.walk_closed _ _ roots [] (by simp) walked n hn
          have same : ds = LeanEntryEnvironment.constants info.type := by
            simpa [typeDependencies,found] using eqn.symm
          exact closed d (same.symm ▸ hd) },walked⟩
    else none

/-- The environment builder is complete for the independent finite signature
conditions. It uses the environment's actual finite size, not a fixed budget. -/
theorem scope_complete (valid : SignatureClosure native roots names) :
    ∃ result, scope native roots = some result := by
  obtain ⟨selected,base,walked,_⟩ := valid.install_complete
  have inventory := valid.selected_subset walked
  have listed : selected ⊆ declarationNames native := fun n hn => valid.listed (inventory hn)
  obtain ⟨present,checked⟩ := available_complete
    (fun n hn => valid.available n (inventory hn))
  unfold scope
  split
  · rename_i missing
    rw [walked] at missing
    contradiction
  · rename_i selected' found
    have same := Option.some.inj (found.symm.trans walked)
    subst selected'
    simp only [dif_pos listed,checked,bind,Option.bind]
    exact ⟨_,rfl⟩

end IRComparison.WordFrontend.NativeEnvironment
