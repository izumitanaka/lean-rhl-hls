import Lean

namespace IRComparison.DependencyClosure
open Lean

/-- The counter bounds DISTINCT unvisited definitions, not worklist edges.
At entry it is the size of the actual finite environment. Repeated edges and
cycles do not consume it. The proof uses a remaining-name set, erased at runtime. -/
def walk (next : Name → Option (List Name)) (capacity : Nat) (todo seen : List Name) : Option (List Name) :=
  match todo with
  | [] => some seen
  | n::rest =>
    if n ∈ seen then walk next capacity rest seen
    else match capacity with
    | 0 => none
    | budget+1 => do
      let deps ← next n
      walk next budget (deps ++ rest) (n::seen)
termination_by (capacity,todo.length)
decreasing_by
  · simp_wf
    apply Prod.Lex.right
    simp_all
  · simp_wf
    apply Prod.Lex.left
    omega

private theorem move_member {a n : Name} {seen remaining : List Name}
    (h : a ∈ seen ∨ a ∈ remaining) :
    a ∈ n::seen ∨ a ∈ remaining.erase n := by
  by_cases eq : a = n
  · subst a; simp
  · rcases h with h | h
    · exact Or.inl (List.mem_cons_of_mem _ h)
    · exact Or.inr ((List.mem_erase_of_ne eq).mpr h)

/-- A finite, closed graph with available definitions is always traversed
successfully, including cycles and repeated references. The conditions concern
the input graph, not the success of the traversal or a fuel estimate. -/
theorem complete (next : Name → Option (List Name)) (remaining todo seen : List Name)
    (capacity : Nat) (bound : remaining.length ≤ capacity)
    (pending : ∀ n ∈ todo, n ∈ seen ∨ n ∈ remaining)
    (available : ∀ n ∈ remaining, ∃ deps, next n = some deps ∧
      ∀ d ∈ deps, d ∈ seen ∨ d ∈ remaining) :
    ∃ result, walk next capacity todo seen = some result := by
  cases todo with
  | nil => exact ⟨seen,by simp [walk]⟩
  | cons n rest =>
    by_cases hs : n ∈ seen
    · obtain ⟨result,done⟩ := complete next remaining rest seen capacity bound
        (fun m hm => pending m (List.mem_cons_of_mem _ hm)) available
      refine ⟨result,?_⟩
      cases capacity <;> simpa only [walk,if_pos hs] using done
    · have hn : n ∈ remaining := (pending n (by simp)).resolve_left hs
      have positive : 0 < remaining.length := List.length_pos_of_mem hn
      cases capacity with
      | zero => omega
      | succ budget =>
        obtain ⟨deps,found,closed⟩ := available n hn
        have newPending : ∀ m ∈ deps ++ rest, m ∈ n::seen ∨ m ∈ remaining.erase n := by
          intro m hm
          rcases List.mem_append.mp hm with hm | hm
          · exact move_member (closed m hm)
          · exact move_member (pending m (List.mem_cons_of_mem _ hm))
        have newAvailable : ∀ m ∈ remaining.erase n, ∃ ds, next m = some ds ∧
            ∀ d ∈ ds, d ∈ n::seen ∨ d ∈ remaining.erase n := by
          intro m hm
          obtain ⟨ds,hds,closed⟩ := available m (List.mem_of_mem_erase hm)
          exact ⟨ds,hds,fun d hd => move_member (closed d hd)⟩
        have newBound : (remaining.erase n).length ≤ budget := by
          simp only [List.length_erase_of_mem hn]
          omega
        obtain ⟨result,done⟩ := complete next (remaining.erase n) (deps ++ rest) (n::seen)
          budget newBound newPending newAvailable
        exact ⟨result,by simpa only [walk,if_neg hs,found,bind,Option.bind] using done⟩
termination_by (capacity,todo.length)
decreasing_by
  · simp_wf
    apply Prod.Lex.right
    simp_all
  · simp_wf
    apply Prod.Lex.left
    omega

/-- Traversal only accumulates distinct declarations from the supplied graph.
This supplies the fresh-name condition of formal library installation. -/
theorem walk_inventory (next : Name → Option (List Name)) (capacity : Nat)
    (todo seen : List Name) (allowed : Name → Prop)
    (unique : seen.Nodup)
    (old : ∀ n ∈ seen, allowed n) (pending : ∀ n ∈ todo, allowed n)
    (closed : ∀ n, allowed n → ∀ deps, next n = some deps → ∀ d ∈ deps, allowed d)
    (success : walk next capacity todo seen = some result) :
    result.Nodup ∧ ∀ n ∈ result, allowed n := by
  cases todo with
  | nil =>
    simp only [walk,Option.some.injEq] at success
    subst result
    exact ⟨unique,old⟩
  | cons n rest =>
    by_cases known : n ∈ seen
    · have tail : walk next capacity rest seen = some result := by
        cases capacity <;> simpa only [walk,if_pos known] using success
      exact walk_inventory next capacity rest seen allowed unique old
        (fun x hx => pending x (List.mem_cons_of_mem _ hx)) closed tail
    · cases capacity with
      | zero => simp [walk,known] at success
      | succ budget =>
        simp only [walk,if_neg known] at success
        cases found : next n with
        | none => simp [found] at success
        | some deps =>
          simp only [found,bind,Option.bind] at success
          apply walk_inventory next budget (deps ++ rest) (n::seen) allowed
            (List.nodup_cons.mpr ⟨known,unique⟩) ?_ ?_ closed success
          · intro x member
            rcases List.mem_cons.mp member with rfl | member
            · exact pending x (by simp)
            · exact old x member
          · intro x member
            rcases List.mem_append.mp member with member | member
            · exact closed n (pending n (by simp)) deps found x member
            · exact pending x (List.mem_cons_of_mem _ member)
termination_by (capacity,todo.length)
decreasing_by
  · simp_wf
    apply Prod.Lex.right
    simp_all
  · simp_wf
    apply Prod.Lex.left
    omega

/-- Every pending or already seen declaration occurs in a successful result.
This is the presence direction needed to derive installed library signatures;
`walk_inventory` separately excludes unrelated declarations. -/
theorem walk_contains (next : Name → Option (List Name)) (capacity : Nat)
    (todo seen : List Name) (success : walk next capacity todo seen = some result) :
    ∀ n, n ∈ todo ∨ n ∈ seen → n ∈ result := by
  cases todo with
  | nil =>
    simp only [walk,Option.some.injEq] at success
    subst result
    intro n h
    simpa using h
  | cons first rest =>
    by_cases known : first ∈ seen
    · have tail : walk next capacity rest seen = some result := by
        cases capacity <;> simpa only [walk,if_pos known] using success
      have ih := walk_contains next capacity rest seen tail
      intro n h
      apply ih
      rcases h with h | h
      · rcases List.mem_cons.mp h with rfl | h
        · exact Or.inr known
        · exact Or.inl h
      · exact Or.inr h
    · cases capacity with
      | zero => simp [walk,known] at success
      | succ budget =>
        simp only [walk,if_neg known] at success
        cases found : next first with
        | none => simp [found] at success
        | some deps =>
          simp only [found,bind,Option.bind] at success
          have ih := walk_contains next budget (deps ++ rest) (first::seen) success
          intro n h
          apply ih
          rcases h with h | h
          · rcases List.mem_cons.mp h with rfl | h
            · exact Or.inr (by simp)
            · exact Or.inl (List.mem_append_right _ h)
          · exact Or.inr (List.mem_cons_of_mem _ h)
termination_by (capacity,todo.length)
decreasing_by
  · simp_wf
    apply Prod.Lex.right
    simp_all
  · simp_wf
    apply Prod.Lex.left
    omega

/-- Successful traversal closes the discovered declarations under type
references. The initial invariant allows edges into the pending worklist. -/
theorem walk_closed (next : Name → Option (List Name)) (capacity : Nat)
    (todo seen : List Name)
    (closed : ∀ n ∈ seen, ∃ ds, next n = some ds ∧ ∀ d ∈ ds, d ∈ todo ∨ d ∈ seen)
    (success : walk next capacity todo seen = some result) :
    ∀ n ∈ result, ∃ ds, next n = some ds ∧ ∀ d ∈ ds, d ∈ result := by
  cases todo with
  | nil =>
    simp only [walk,Option.some.injEq] at success
    subst result
    intro n hn
    obtain ⟨ds,found,deps⟩ := closed n hn
    exact ⟨ds,found,fun d hd => by simpa using deps d hd⟩
  | cons first rest =>
    by_cases known : first ∈ seen
    · have tail : walk next capacity rest seen = some result := by
        cases capacity <;> simpa only [walk,if_pos known] using success
      apply walk_closed next capacity rest seen _ tail
      intro n hn
      obtain ⟨ds,found,deps⟩ := closed n hn
      refine ⟨ds,found,?_⟩
      intro d hd
      rcases deps d hd with h | h
      · rcases List.mem_cons.mp h with rfl | h
        · exact Or.inr known
        · exact Or.inl h
      · exact Or.inr h
    · cases capacity with
      | zero => simp [walk,known] at success
      | succ budget =>
        simp only [walk,if_neg known] at success
        cases found : next first with
        | none => simp [found] at success
        | some deps =>
          simp only [found,bind,Option.bind] at success
          apply walk_closed next budget (deps ++ rest) (first::seen) _ success
          intro n hn
          rcases List.mem_cons.mp hn with rfl | hn
          · exact ⟨deps,found,fun d hd => Or.inl (List.mem_append_left _ hd)⟩
          · obtain ⟨ds,eqn,edges⟩ := closed n hn
            refine ⟨ds,eqn,?_⟩
            intro d hd
            rcases edges d hd with h | h
            · rcases List.mem_cons.mp h with rfl | h
              · exact Or.inr (by simp)
              · exact Or.inl (List.mem_append_right _ h)
            · exact Or.inr (List.mem_cons_of_mem _ h)
termination_by (capacity,todo.length)
decreasing_by
  · simp_wf
    apply Prod.Lex.right
    simp_all
  · simp_wf
    apply Prod.Lex.left
    omega

/-- Reachability describes the declaration graph independently of the loader. -/
inductive Reachable (next : Name → Option (List Name)) (roots : List Name) : Name → Prop where
  | root : n ∈ roots → Reachable next roots n
  | dependency : Reachable next roots n → next n = some ds → d ∈ ds → Reachable next roots d

theorem Reachable.mono (reachable : Reachable next roots n) (subset : roots ⊆ more) :
    Reachable next more n := by
  induction reachable with
  | root h => exact .root (subset h)
  | dependency _ found hd ih => exact .dependency ih found hd

theorem walk_reachable (success : walk next capacity roots [] = some result)
    (reachable : Reachable next roots n) : n ∈ result := by
  have closed := walk_closed next capacity roots [] (by simp) success
  induction reachable with
  | root h => exact walk_contains next capacity roots [] success _ (Or.inl h)
  | dependency _ found hd ih =>
    obtain ⟨ds,eqn,deps⟩ := closed _ ih
    cases Option.some.inj (found.symm.trans eqn)
    exact deps _ hd

end IRComparison.DependencyClosure
